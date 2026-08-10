import NativeCarrySpectralWeyl.Finite.StepDensity
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Normalized finite-camera POVMs from the continuous step density

This file turns the positive density from the step-moment layer into the
operator-valued measure described in the research notes.  For a finite camera
family, write

`D(x)ᵢᵢ = 1_{(0, ellᵢ]}(x)`

and let `M₀` be the periodic profile product mean.  The unnormalized density is

`dΣ(x) = D(x) M₀ D(x) dx`.

It is positive semidefinite pointwise, its integral over every measurable set
is positive semidefinite, and its total mass is exactly the camera Gram matrix
`G`.  When `G` is positive definite, congruence by its canonical positive
inverse square root produces

`dE(x) = G⁻¹/² dΣ(x) G⁻¹/²`,

a normalized finite-dimensional POVM.  Finally, pushing this measure forward
by `x ↦ 1 + log x` gives the centered-log spectral POVM used in the Weyl
construction.  The complete construction is instantiated for the canonical
six-camera family.

Mathlib offers several equivalent norms on finite matrices and therefore does
not install a canonical normed-space instance on `Matrix`.  The vector-measure
codomain is represented by pair-indexed coordinates `ι × ι → ℝ`; the inverse
maps `matrixToPair` and `pairToMatrix` preserve the exact matrix semantics.
-/

open scoped BigOperators Matrix MatrixOrder MeasureTheory ENNReal
open Set MeasureTheory

noncomputable section

namespace NativeCarrySpectralWeyl.Finite

def stepCutoff (slope : ℕ) (x : ℝ) : ℝ :=
  (Ioc 0 (slope : ℝ)).indicator (fun _ => 1) x

private theorem stepCutoff_mul (a b : ℕ) (x : ℝ) :
    stepCutoff a x * stepCutoff b x = stepCutoff (min a b) x := by
  simp only [stepCutoff, ← Set.inter_indicator_mul, Ioc_inter_Ioc,
    max_self, Nat.cast_min, one_mul]

private theorem integrable_stepCutoff (slope : ℕ) :
    Integrable (stepCutoff slope) := by
  unfold stepCutoff
  exact (integrableOn_const (by simp [Real.volume_Ioc])).integrable_indicator
    measurableSet_Ioc

private theorem integral_stepCutoff (slope : ℕ) :
    ∫ x : ℝ, stepCutoff slope x = slope := by
  unfold stepCutoff
  rw [integral_indicator_const _ measurableSet_Ioc]
  simp

private theorem integrable_stepCutoff_mul (a b : ℕ) :
    Integrable (fun x => stepCutoff a x * stepCutoff b x) := by
  simpa only [stepCutoff_mul] using integrable_stepCutoff (min a b)

def integralGramMatrix {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ x, f x i * f x j ∂μ

theorem integralGramMatrix_posSemidef {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] (μ : Measure α) (f : α → ι → ℝ)
    (hint : ∀ i j, Integrable (fun x => f x i * f x j) μ) :
    (integralGramMatrix μ f).PosSemidef := by
  classical
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    simp only [integralGramMatrix, star_trivial]
    congr 1
    funext x
    ring
  · intro v
    have hterm (i j : ι) : Integrable
        (fun x => v i * (f x i * f x j) * v j) μ :=
      ((hint i j).const_mul (v i)).mul_const (v j)
    calc
      star v ⬝ᵥ (integralGramMatrix μ f *ᵥ v) =
          ∑ i, ∑ j, ∫ x,
            v i * (f x i * f x j) * v j ∂μ := by
        simp only [dotProduct, Matrix.mulVec, integralGramMatrix,
          star_trivial]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← integral_mul_const, ← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = ∫ x, ∑ i, ∑ j,
          v i * (f x i * f x j) * v j ∂μ := by
        rw [integral_finsetSum]
        · congr 1
          funext i
          rw [integral_finsetSum]
          intro j hj
          exact hterm i j
        · intro i hi
          exact integrable_finsetSum _ fun j _ => hterm i j
      _ = ∫ x, (∑ i, v i * f x i) ^ 2 ∂μ := by
        congr 1
        funext x
        rw [sq, Fintype.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≥ 0 := integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)

def cameraStepDensity {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) (x : ℝ) : Matrix ι ι ℝ :=
  periodicMeanMatrix period camera ⊙
    Matrix.vecMulVec
      (fun i => stepCutoff (Camera.cameraSlope (camera i)) x)
      (star fun i => stepCutoff (Camera.cameraSlope (camera i)) x)

theorem cameraStepDensity_posSemidef {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) (x : ℝ) :
    (cameraStepDensity period camera x).PosSemidef := by
  exact (periodicMeanMatrix_posSemidef period camera).hadamard
    (Matrix.posSemidef_vecMulVec_self_star _)

/-- Pair-indexed coordinates give finite matrices a canonical product Banach
space, avoiding any arbitrary choice among Mathlib's equivalent matrix norms. -/
def matrixToPair {ι : Type*} (A : Matrix ι ι ℝ) : ι × ι → ℝ :=
  fun p => A p.1 p.2

/-- Recover a matrix from its pair-indexed coordinate vector. -/
def pairToMatrix {ι : Type*} (v : ι × ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => v (i, j)

@[simp] theorem pairToMatrix_matrixToPair {ι : Type*}
    (A : Matrix ι ι ℝ) : pairToMatrix (matrixToPair A) = A := by
  rfl

@[simp] theorem matrixToPair_pairToMatrix {ι : Type*}
    (v : ι × ι → ℝ) : matrixToPair (pairToMatrix v) = v := by
  ext ⟨i, j⟩
  rfl

@[simp] theorem pairToMatrix_zero {ι : Type*} :
    pairToMatrix (0 : ι × ι → ℝ) = 0 := by
  rfl

@[simp] theorem pairToMatrix_add {ι : Type*} (v w : ι × ι → ℝ) :
    pairToMatrix (v + w) = pairToMatrix v + pairToMatrix w := by
  rfl

theorem matrixToPair_injective {ι : Type*} :
    Function.Injective (matrixToPair : Matrix ι ι ℝ → ι × ι → ℝ) := by
  intro A B h
  simpa only [pairToMatrix_matrixToPair] using congrArg pairToMatrix h

theorem pairToMatrix_injective {ι : Type*} :
    Function.Injective (pairToMatrix : (ι × ι → ℝ) → Matrix ι ι ℝ) := by
  intro v w h
  simpa only [matrixToPair_pairToMatrix] using congrArg matrixToPair h

def cameraStepDensityVector {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) (x : ℝ) : ι × ι → ℝ :=
  matrixToPair (cameraStepDensity period camera x)

theorem cameraStepDensityVector_integrable {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    Integrable (cameraStepDensityVector period camera) := by
  apply Integrable.of_eval
  intro p
  rcases p with ⟨i, j⟩
  simp only [cameraStepDensityVector, matrixToPair, cameraStepDensity,
    Matrix.hadamard_apply, Matrix.vecMulVec_apply, star_trivial]
  exact (integrable_stepCutoff_mul (Camera.cameraSlope (camera i))
    (Camera.cameraSlope (camera j))).const_mul _

theorem cameraStepDensityVector_integral {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    ∫ x, cameraStepDensityVector period camera x =
      matrixToPair (periodicGramMatrix period camera) := by
  classical
  ext ⟨i, j⟩
  rw [MeasureTheory.eval_integral
    (fun p => (cameraStepDensityVector_integrable period camera).eval p)]
  simp only [cameraStepDensityVector, matrixToPair, cameraStepDensity,
    Matrix.hadamard_apply, Matrix.vecMulVec_apply, star_trivial]
  rw [integral_const_mul]
  simp_rw [stepCutoff_mul]
  rw [integral_stepCutoff]
  simp [periodicGramMatrix, slopeMinMatrix, Camera.cameraSlope, Nat.cast_min]
  ring

def stepSetGramMatrix {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) (s : Set ℝ) : Matrix ι ι ℝ :=
  integralGramMatrix (volume.restrict s)
    (fun x i => stepCutoff (slope i) x)

theorem stepSetGramMatrix_posSemidef {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) (s : Set ℝ) :
    (stepSetGramMatrix slope s).PosSemidef := by
  apply integralGramMatrix_posSemidef
  intro i j
  exact (integrable_stepCutoff_mul (slope i) (slope j)).integrableOn

def cameraStepMeasure {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    VectorMeasure ℝ (ι × ι → ℝ) :=
  volume.withDensityᵥ (cameraStepDensityVector period camera)

theorem cameraStepMeasure_apply {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    cameraStepMeasure period camera s =
      matrixToPair (periodicMeanMatrix period camera ⊙
        stepSetGramMatrix (fun i => Camera.cameraSlope (camera i)) s) := by
  rw [cameraStepMeasure, MeasureTheory.withDensityᵥ_apply
    (cameraStepDensityVector_integrable period camera) hs]
  have hrest : Integrable (cameraStepDensityVector period camera)
      (volume.restrict s) :=
    (cameraStepDensityVector_integrable period camera).integrableOn
  ext ⟨i, j⟩
  rw [MeasureTheory.eval_integral (fun p => hrest.eval p)]
  simp only [cameraStepDensityVector, matrixToPair, cameraStepDensity,
    Matrix.hadamard_apply, Matrix.vecMulVec_apply, star_trivial,
    stepSetGramMatrix, integralGramMatrix]
  rw [integral_const_mul]

theorem cameraStepMeasure_toMatrix_apply {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    pairToMatrix (cameraStepMeasure period camera s) =
      periodicMeanMatrix period camera ⊙
        stepSetGramMatrix (fun i => Camera.cameraSlope (camera i)) s := by
  rw [cameraStepMeasure_apply period camera hs,
    pairToMatrix_matrixToPair]

theorem cameraStepMeasure_posSemidef {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (pairToMatrix (cameraStepMeasure period camera s)).PosSemidef := by
  rw [cameraStepMeasure_toMatrix_apply period camera hs]
  exact (periodicMeanMatrix_posSemidef period camera).hadamard
    (stepSetGramMatrix_posSemidef _ s)

theorem cameraStepMeasure_univ {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    cameraStepMeasure period camera Set.univ =
      matrixToPair (periodicGramMatrix period camera) := by
  rw [cameraStepMeasure, MeasureTheory.withDensityᵥ_apply
    (cameraStepDensityVector_integrable period camera) MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using
    cameraStepDensityVector_integral period camera

def matrixCongruenceAddHom {ι : Type*} [Fintype ι]
    (R : Matrix ι ι ℝ) : (ι × ι → ℝ) →+ (ι × ι → ℝ) where
  toFun v := matrixToPair (R * pairToMatrix v * R)
  map_zero' := by
    ext ⟨i, j⟩
    simp [matrixToPair]
  map_add' v w := by
    ext ⟨i, j⟩
    simp [matrixToPair, mul_add, add_mul]

theorem matrixCongruenceAddHom_continuous {ι : Type*} [Fintype ι]
    (R : Matrix ι ι ℝ) : Continuous (matrixCongruenceAddHom R) := by
  apply continuous_pi
  intro p
  rcases p with ⟨i, j⟩
  simp only [matrixCongruenceAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    matrixToPair, pairToMatrix, Matrix.mul_apply]
  fun_prop

def normalizedCameraStepMeasure {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (period : ℕ)
    (camera : ι → ℕ) : VectorMeasure ℝ (ι × ι → ℝ) :=
  (cameraStepMeasure period camera).mapRange
    (matrixCongruenceAddHom (positiveInverseSqrt G))
    (matrixCongruenceAddHom_continuous (positiveInverseSqrt G))

theorem normalizedCameraStepMeasure_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι ℝ) (period : ℕ)
    (camera : ι → ℕ) (s : Set ℝ) :
    pairToMatrix (normalizedCameraStepMeasure G period camera s) =
      whitenedMatrix G (pairToMatrix (cameraStepMeasure period camera s)) := by
  simp [normalizedCameraStepMeasure, matrixCongruenceAddHom,
    whitenedMatrix]

theorem normalizedCameraStepMeasure_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosDef)
    (period : ℕ) (camera : ι → ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (pairToMatrix
      (normalizedCameraStepMeasure G period camera s)).PosSemidef := by
  rw [normalizedCameraStepMeasure_apply]
  exact whitenedMatrix_posSemidef hG
    (cameraStepMeasure_posSemidef period camera hs)

theorem normalizedCameraStepMeasure_univ {ι : Type*} [Fintype ι]
    [DecidableEq ι] (period : ℕ) (camera : ι → ℕ)
    (hG : (periodicGramMatrix period camera).PosDef) :
    normalizedCameraStepMeasure (periodicGramMatrix period camera)
        period camera Set.univ = matrixToPair (1 : Matrix ι ι ℝ) := by
  apply pairToMatrix_injective
  rw [normalizedCameraStepMeasure_apply, cameraStepMeasure_univ,
    pairToMatrix_matrixToPair, pairToMatrix_matrixToPair]
  exact whitenedGram_eq_one hG

structure MatrixPOVM (α ι : Type*) [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] where
  measure : VectorMeasure α (ι × ι → ℝ)
  positive : ∀ {s : Set α}, MeasurableSet s →
    (pairToMatrix (measure s)).PosSemidef
  normalized : measure Set.univ = matrixToPair (1 : Matrix ι ι ℝ)

def cameraStepPOVM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (period : ℕ) (camera : ι → ℕ)
    (hG : (periodicGramMatrix period camera).PosDef) : MatrixPOVM ℝ ι where
  measure := normalizedCameraStepMeasure
    (periodicGramMatrix period camera) period camera
  positive := normalizedCameraStepMeasure_posSemidef hG period camera
  normalized := normalizedCameraStepMeasure_univ period camera hG

def sixCameraStepPOVM : MatrixPOVM ℝ (Fin 6) :=
  cameraStepPOVM 420 sixCamera (by
    rw [sixCameraGram_eq]
    exact sixCameraGram_posDef)

def centeredLogCoordinate (x : ℝ) : ℝ := 1 + Real.log x

theorem measurable_centeredLogCoordinate : Measurable centeredLogCoordinate := by
  exact measurable_const.add Real.measurable_log

namespace MatrixPOVM

def map {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [DecidableEq ι] (E : MatrixPOVM α ι)
    (f : α → β) (hf : Measurable f) : MatrixPOVM β ι where
  measure := E.measure.map f
  positive := by
    intro s hs
    rw [VectorMeasure.map_apply E.measure hf hs]
    exact E.positive (hs.preimage hf)
  normalized := by
    rw [VectorMeasure.map_apply E.measure hf MeasurableSet.univ]
    simpa only [preimage_univ] using E.normalized

end MatrixPOVM

def cameraCenteredLogPOVM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (period : ℕ) (camera : ι → ℕ)
    (hG : (periodicGramMatrix period camera).PosDef) : MatrixPOVM ℝ ι :=
  (cameraStepPOVM period camera hG).map centeredLogCoordinate
    measurable_centeredLogCoordinate

def sixCameraCenteredLogPOVM : MatrixPOVM ℝ (Fin 6) :=
  cameraCenteredLogPOVM 420 sixCamera (by
    rw [sixCameraGram_eq]
    exact sixCameraGram_posDef)

/-- Every measurable effect of the canonical centered-log six-camera POVM is
positive semidefinite. -/
theorem sixCameraCenteredLogPOVM_posSemidef {s : Set ℝ}
    (hs : MeasurableSet s) :
    (pairToMatrix (sixCameraCenteredLogPOVM.measure s)).PosSemidef :=
  sixCameraCenteredLogPOVM.positive hs

/-- The total effect of the canonical centered-log six-camera POVM is the
identity matrix. -/
theorem sixCameraCenteredLogPOVM_univ :
    sixCameraCenteredLogPOVM.measure Set.univ =
      matrixToPair (1 : Matrix (Fin 6) (Fin 6) ℝ) :=
  sixCameraCenteredLogPOVM.normalized

end NativeCarrySpectralWeyl.Finite
