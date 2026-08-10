import NativeCarrySpectralWeyl.Finite.Whitening
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous step density and concrete variance positivity

This file closes the positivity condition left by the algebraic whitening
layer.  For a finite family of positive natural slopes it realizes the full
two-level moment block as the integral Gram matrix of the truncated features

`1_{{x ≤ ell_i}}` and `(1 + log x) 1_{{x ≤ ell_i}}`.

The singular endpoint is handled exactly: the primitive
`x * (1 + log(x)^2)` tends to zero as `x → 0+`, giving

`integral 0..ell (1 + log x)^2 = ell * (1 + log(ell)^2)`.

The step Gram block is positive semidefinite by integration of a square.  Its
Hadamard product with the repeated periodic product-mean block recovers the
documented matrices `G`, `H`, and `J`.  The Schur-complement theorem from the
whitening layer then yields unconditional positive semidefiniteness of the
canonical six-camera variance.
-/

open scoped BigOperators Matrix MatrixOrder Interval
open Filter Set MeasureTheory intervalIntegral Topology

noncomputable section

namespace NativeCarrySpectralWeyl.Finite

open NativeCarrySpectralWeyl.Camera

private theorem tendsto_self_mul_log_sq_nhdsGT_zero :
    Tendsto (fun x : ℝ => x * Real.log x ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hsqrt : Tendsto (fun x : ℝ => Real.log x * Real.sqrt x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using h
  have hsq := hsqrt.mul hsqrt
  have heq : (fun x : ℝ => Real.log x * Real.sqrt x *
      (Real.log x * Real.sqrt x)) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x * Real.log x ^ 2) := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have hx0 : 0 ≤ x := hx.le
    calc
      Real.log x * Real.sqrt x * (Real.log x * Real.sqrt x) =
          Real.sqrt x ^ 2 * Real.log x ^ 2 := by ring
      _ = x * Real.log x ^ 2 := by rw [Real.sq_sqrt hx0]
  simpa only [zero_mul] using hsq.congr' heq

private def secondMomentPrimitive (x : ℝ) : ℝ :=
  x * (1 + Real.log x ^ 2)

private theorem secondMomentPrimitive_tendsto_zero :
    Tendsto secondMomentPrimitive (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hlog := tendsto_self_mul_log_sq_nhdsGT_zero
  have hid : Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  change Tendsto (fun x : ℝ => x * (1 + Real.log x ^ 2))
    (nhdsWithin 0 (Ioi 0)) (nhds 0)
  convert hid.add hlog using 1
  · funext x
    ring
  · ring

private theorem secondMomentPrimitive_continuousOn {b : ℝ} (_hb : 0 < b) :
    ContinuousOn secondMomentPrimitive (Icc 0 b) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hright : ContinuousWithinAt secondMomentPrimitive (Ioi 0) 0 := by
      simpa [ContinuousWithinAt, secondMomentPrimitive] using
        secondMomentPrimitive_tendsto_zero
    exact (continuousWithinAt_Ioi_iff_Ici.mp hright).mono
      Icc_subset_Ici_self
  · exact ((continuousAt_id.mul
      (continuousAt_const.add ((Real.continuousAt_log hx0).pow 2))).continuousWithinAt)

private theorem secondMomentPrimitive_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt secondMomentPrimitive ((1 + Real.log x) ^ 2) x := by
  have h := (hasDerivAt_id x).mul
    ((hasDerivAt_const x 1).add ((Real.hasDerivAt_log hx).pow 2))
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.pow_apply, id_eq, one_mul, zero_add]
  field_simp [hx]
  ring

theorem intervalIntegrable_centeredLogSq_zero {b : ℝ} (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => (1 + Real.log x) ^ 2)
      volume 0 b := by
  apply intervalIntegrable_deriv_of_nonneg
    (g := secondMomentPrimitive)
  · simpa [uIcc_of_le hb.le] using secondMomentPrimitive_continuousOn hb
  · intro x hx
    rw [min_eq_left hb.le, max_eq_right hb.le] at hx
    exact secondMomentPrimitive_hasDerivAt hx.1.ne'
  · intro x hx
    positivity

theorem integral_centeredLogSq_zero {b : ℝ} (hb : 0 < b) :
    ∫ x in 0..b, (1 + Real.log x) ^ 2 =
      b * (1 + Real.log b ^ 2) := by
  rw [integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := secondMomentPrimitive) (fa := 0)
    (fb := b * (1 + Real.log b ^ 2))
    (hint := intervalIntegrable_centeredLogSq_zero hb)]
  · ring
  · exact hb
  · intro x hx
    exact secondMomentPrimitive_hasDerivAt hx.1.ne'
  · exact secondMomentPrimitive_tendsto_zero
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (ContinuousAt.tendsto (by
        unfold secondMomentPrimitive
        exact continuousAt_id.mul
          (continuousAt_const.add ((Real.continuousAt_log hb.ne').pow 2))))

theorem intervalIntegrable_centeredLog_zero {b : ℝ} :
    IntervalIntegrable (fun x : ℝ => 1 + Real.log x) volume 0 b := by
  exact intervalIntegrable_const.add intervalIntegrable_log'

theorem integral_centeredLog_zero {b : ℝ} (hb : 0 < b) :
    ∫ x in 0..b, (1 + Real.log x) = b * Real.log b := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    intervalIntegrable_log', intervalIntegral.integral_const,
    integral_log_from_zero_of_pos hb]
  ring

def intervalGramMatrix {ι : Type*} (f : ℝ → ι → ℝ) (a b : ℝ) :
    Matrix ι ι ℝ :=
  fun i j => ∫ x in a..b, f x i * f x j

theorem intervalGramMatrix_posSemidef {ι : Type*} [Fintype ι]
    (f : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hint : ∀ i j, IntervalIntegrable (fun x => f x i * f x j)
      volume a b) : (intervalGramMatrix f a b).PosSemidef := by
  classical
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    simp only [intervalGramMatrix, star_trivial]
    congr 1
    funext x
    ring
  · intro v
    have hterm (i j : ι) : IntervalIntegrable
        (fun x => v i * (f x i * f x j) * v j) volume a b :=
      ((hint i j).const_mul (v i)).mul_const (v j)
    calc
      star v ⬝ᵥ (intervalGramMatrix f a b *ᵥ v) =
          ∑ i, ∑ j, ∫ x in a..b,
            v i * (f x i * f x j) * v j := by
        simp only [dotProduct, Matrix.mulVec, intervalGramMatrix,
          star_trivial]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_mul_const]
        ring
      _ = ∫ x in a..b, ∑ i, ∑ j,
          v i * (f x i * f x j) * v j := by
        rw [intervalIntegral.integral_finsetSum]
        · congr 1
          funext i
          rw [intervalIntegral.integral_finsetSum]
          intro j hj
          exact hterm i j
        · intro i hi
          have hs := IntervalIntegrable.sum Finset.univ
            (fun j hj => hterm i j)
          rw [Finset.sum_fn] at hs
          exact hs
      _ = ∫ x in a..b, (∑ i, v i * f x i) ^ 2 := by
        congr 1
        funext x
        rw [sq, Fintype.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≥ 0 := intervalIntegral.integral_nonneg_of_forall hab
        (fun x => sq_nonneg _)

private theorem indicator_Iic_mul_indicator_Iic
    (f g : ℝ → ℝ) (a b x : ℝ) :
    (Iic a).indicator f x * (Iic b).indicator g x =
      {y | y ≤ min a b}.indicator (fun y => f y * g y) x := by
  change _ = (Iic (a ⊓ b)).indicator (fun y => f y * g y) x
  rw [← Set.inter_indicator_mul]
  rw [Iic_inter_Iic]

private theorem intervalIntegrable_indicator_Iic {f : ℝ → ℝ}
    {a b : ℝ} (hf : IntervalIntegrable f volume 0 b) :
    IntervalIntegrable (fun x => {y | y ≤ a}.indicator f x) volume 0 b := by
  change IntervalIntegrable ((Iic a).indicator f) volume 0 b
  rw [intervalIntegrable_iff]
  exact hf.def'.indicator measurableSet_Iic

/-- A harmless common upper bound for a finite family of natural slopes. -/
def slopeMomentBound {ι : Type*} [Fintype ι] (slope : ι → ℕ) : ℝ :=
  1 + ∑ i, (slope i : ℝ)

private theorem slope_cast_lt_slopeMomentBound {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) (i : ι) : (slope i : ℝ) < slopeMomentBound slope := by
  have hi : (slope i : ℝ) ≤ ∑ j, (slope j : ℝ) :=
    Finset.single_le_sum (fun j _ => Nat.cast_nonneg (slope j))
      (Finset.mem_univ i)
  unfold slopeMomentBound
  linarith

/-- The two step features `1` and `1 + log x`, truncated at each slope. -/
def slopeMomentFeature {ι : Type*} (slope : ι → ℕ) (x : ℝ) : ι ⊕ ι → ℝ
  | Sum.inl i => (Iic (slope i : ℝ)).indicator (fun _ => 1) x
  | Sum.inr i =>
      (Iic (slope i : ℝ)).indicator (fun y => 1 + Real.log y) x

private theorem slopeMomentFeature_mul_intervalIntegrable {ι : Type*}
    [Fintype ι] (slope : ι → ℕ) (p q : ι ⊕ ι) :
    IntervalIntegrable
      (fun x => slopeMomentFeature slope x p * slopeMomentFeature slope x q)
      volume 0 (slopeMomentBound slope) := by
  have hB : 0 < slopeMomentBound slope := by
    unfold slopeMomentBound
    positivity
  rcases p with i | i <;> rcases q with j | j
  · simp only [slopeMomentFeature]
    simpa only [indicator_Iic_mul_indicator_Iic, one_mul] using
      (intervalIntegrable_indicator_Iic
        (a := min (slope i : ℝ) (slope j : ℝ)) intervalIntegrable_const)
  · simp only [slopeMomentFeature]
    simpa only [indicator_Iic_mul_indicator_Iic, one_mul] using
      (intervalIntegrable_indicator_Iic
        (a := min (slope i : ℝ) (slope j : ℝ))
        intervalIntegrable_centeredLog_zero)
  · simp only [slopeMomentFeature]
    simpa only [indicator_Iic_mul_indicator_Iic, mul_one] using
      (intervalIntegrable_indicator_Iic
        (a := min (slope i : ℝ) (slope j : ℝ))
        intervalIntegrable_centeredLog_zero)
  · simp only [slopeMomentFeature]
    simpa only [indicator_Iic_mul_indicator_Iic, pow_two] using
      (intervalIntegrable_indicator_Iic
        (a := min (slope i : ℝ) (slope j : ℝ))
        (intervalIntegrable_centeredLogSq_zero hB))

/-- Continuous two-level step moment block before the periodic profile mean
is inserted. -/
def slopeMomentBlock {ι : Type*} [Fintype ι] (slope : ι → ℕ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  intervalGramMatrix (slopeMomentFeature slope) 0 (slopeMomentBound slope)

/-- Positivity of the continuous step moment block follows from its integral
Gram representation. -/
theorem slopeMomentBlock_posSemidef {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) : (slopeMomentBlock slope).PosSemidef := by
  apply intervalGramMatrix_posSemidef
  · unfold slopeMomentBound
    positivity
  · exact slopeMomentFeature_mul_intervalIntegrable slope

theorem slopeMomentBlock_apply_inl_inl {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) (hslope : ∀ i, 0 < slope i) (i j : ι) :
    slopeMomentBlock slope (Sum.inl i) (Sum.inl j) =
      ((min (slope i) (slope j) : ℕ) : ℝ) := by
  let ell : ℝ := min (slope i : ℝ) (slope j : ℝ)
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by exact_mod_cast hslope i) (by exact_mod_cast hslope j)
  have hellB : ell ≤ slopeMomentBound slope :=
    (min_le_left _ _).trans (slope_cast_lt_slopeMomentBound slope i).le
  dsimp [ell] at hell hellB
  simp only [slopeMomentBlock, intervalGramMatrix, slopeMomentFeature]
  simp_rw [indicator_Iic_mul_indicator_Iic]
  rw [intervalIntegral.integral_indicator ⟨hell.le, hellB⟩]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
    sub_zero]
  exact (Nat.cast_min (slope i) (slope j)).symm

theorem slopeMomentBlock_apply_inl_inr {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) (hslope : ∀ i, 0 < slope i) (i j : ι) :
    slopeMomentBlock slope (Sum.inl i) (Sum.inr j) =
      ((min (slope i) (slope j) : ℕ) : ℝ) *
        Real.log (min (slope i) (slope j) : ℕ) := by
  let ell : ℝ := min (slope i : ℝ) (slope j : ℝ)
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by exact_mod_cast hslope i) (by exact_mod_cast hslope j)
  have hellB : ell ≤ slopeMomentBound slope :=
    (min_le_left _ _).trans (slope_cast_lt_slopeMomentBound slope i).le
  dsimp [ell] at hell hellB
  simp only [slopeMomentBlock, intervalGramMatrix, slopeMomentFeature]
  simp_rw [indicator_Iic_mul_indicator_Iic]
  rw [intervalIntegral.integral_indicator ⟨hell.le, hellB⟩]
  simp only [one_mul]
  rw [integral_centeredLog_zero hell]
  rw [Nat.cast_min]

theorem slopeMomentBlock_apply_inr_inl {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) (hslope : ∀ i, 0 < slope i) (i j : ι) :
    slopeMomentBlock slope (Sum.inr i) (Sum.inl j) =
      ((min (slope i) (slope j) : ℕ) : ℝ) *
        Real.log (min (slope i) (slope j) : ℕ) := by
  let ell : ℝ := min (slope i : ℝ) (slope j : ℝ)
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by exact_mod_cast hslope i) (by exact_mod_cast hslope j)
  have hellB : ell ≤ slopeMomentBound slope :=
    (min_le_left _ _).trans (slope_cast_lt_slopeMomentBound slope i).le
  dsimp [ell] at hell hellB
  simp only [slopeMomentBlock, intervalGramMatrix, slopeMomentFeature]
  simp_rw [indicator_Iic_mul_indicator_Iic]
  rw [intervalIntegral.integral_indicator ⟨hell.le, hellB⟩]
  simp only [mul_one]
  rw [integral_centeredLog_zero hell]
  rw [Nat.cast_min]

theorem slopeMomentBlock_apply_inr_inr {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) (hslope : ∀ i, 0 < slope i) (i j : ι) :
    slopeMomentBlock slope (Sum.inr i) (Sum.inr j) =
      ((min (slope i) (slope j) : ℕ) : ℝ) *
        (1 + Real.log (min (slope i) (slope j) : ℕ) ^ 2) := by
  let ell : ℝ := min (slope i : ℝ) (slope j : ℝ)
  have hell : 0 < ell := by
    dsimp [ell]
    exact lt_min (by exact_mod_cast hslope i) (by exact_mod_cast hslope j)
  have hellB : ell ≤ slopeMomentBound slope :=
    (min_le_left _ _).trans (slope_cast_lt_slopeMomentBound slope i).le
  dsimp [ell] at hell hellB
  simp only [slopeMomentBlock, intervalGramMatrix, slopeMomentFeature]
  simp_rw [indicator_Iic_mul_indicator_Iic]
  rw [intervalIntegral.integral_indicator ⟨hell.le, hellB⟩]
  simp_rw [← pow_two]
  rw [integral_centeredLogSq_zero hell]
  rw [Nat.cast_min]

/-- A profile vector repeated in the two moment coordinates. -/
def repeatedProfileVector {ι : Type*} (camera : ι → ℕ) (residue : ℕ) :
    ι ⊕ ι → ℝ
  | Sum.inl i => profileVector camera residue i
  | Sum.inr i => profileVector camera residue i

/-- The periodic product mean repeated in all four blocks. -/
def repeatedPeriodicMeanMatrix {ι : Type*} (period : ℕ)
    (camera : ι → ℕ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  (period : ℝ)⁻¹ • ∑ residue ∈ Finset.range period,
    Matrix.vecMulVec (repeatedProfileVector camera residue)
      (star (repeatedProfileVector camera residue))

@[simp] theorem repeatedPeriodicMeanMatrix_apply_inl_inl {ι : Type*}
    [Fintype ι] (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    repeatedPeriodicMeanMatrix period camera (Sum.inl i) (Sum.inl j) =
      periodicMeanMatrix period camera i j := by
  classical
  simp [repeatedPeriodicMeanMatrix, periodicMeanMatrix, Matrix.sum_apply,
    Matrix.vecMulVec_apply, repeatedProfileVector, star_trivial]

@[simp] theorem repeatedPeriodicMeanMatrix_apply_inl_inr {ι : Type*}
    [Fintype ι] (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    repeatedPeriodicMeanMatrix period camera (Sum.inl i) (Sum.inr j) =
      periodicMeanMatrix period camera i j := by
  classical
  simp [repeatedPeriodicMeanMatrix, periodicMeanMatrix, Matrix.sum_apply,
    Matrix.vecMulVec_apply, repeatedProfileVector, star_trivial]

@[simp] theorem repeatedPeriodicMeanMatrix_apply_inr_inl {ι : Type*}
    [Fintype ι] (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    repeatedPeriodicMeanMatrix period camera (Sum.inr i) (Sum.inl j) =
      periodicMeanMatrix period camera i j := by
  classical
  simp [repeatedPeriodicMeanMatrix, periodicMeanMatrix, Matrix.sum_apply,
    Matrix.vecMulVec_apply, repeatedProfileVector, star_trivial]

@[simp] theorem repeatedPeriodicMeanMatrix_apply_inr_inr {ι : Type*}
    [Fintype ι] (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    repeatedPeriodicMeanMatrix period camera (Sum.inr i) (Sum.inr j) =
      periodicMeanMatrix period camera i j := by
  classical
  simp [repeatedPeriodicMeanMatrix, periodicMeanMatrix, Matrix.sum_apply,
    Matrix.vecMulVec_apply, repeatedProfileVector, star_trivial]

/-- Repeating the periodic mean in both moment coordinates preserves
positive semidefiniteness: it is the same normalized rank-one sum with
repeated profile vectors. -/
theorem repeatedPeriodicMeanMatrix_posSemidef {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (repeatedPeriodicMeanMatrix period camera).PosSemidef := by
  classical
  unfold repeatedPeriodicMeanMatrix
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_sum (Finset.range period) fun residue _ =>
      Matrix.posSemidef_vecMulVec_self_star
        (repeatedProfileVector camera residue)
  · positivity

/-- The documented camera moment block is exactly the Schur product of the
continuous step Gram block with the repeated periodic profile mean. -/
theorem cameraMomentBlock_eq_hadamard_step {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (period : ℕ) (camera : ι → ℕ)
    (hslope : ∀ i, 0 < cameraSlope (camera i)) :
    momentBlockMatrix (periodicGramMatrix period camera)
        (firstMomentMatrix period camera)
        (secondCenteredMomentMatrix period camera) =
      repeatedPeriodicMeanMatrix period camera ⊙
        slopeMomentBlock (fun i => cameraSlope (camera i)) := by
  ext p q
  rcases p with i | i <;> rcases q with j | j
  · simp only [momentBlockMatrix, Matrix.fromBlocks_apply₁₁,
      repeatedPeriodicMeanMatrix_apply_inl_inl, Matrix.hadamard_apply]
    rw [slopeMomentBlock_apply_inl_inl _ hslope]
    simp only [periodicGramMatrix, slopeMinMatrix, Matrix.hadamard_apply]
    rw [Nat.cast_min]
    ring
  · simp only [momentBlockMatrix, Matrix.fromBlocks_apply₁₂,
      repeatedPeriodicMeanMatrix_apply_inl_inr, Matrix.hadamard_apply]
    rw [slopeMomentBlock_apply_inl_inr _ hslope]
    simp only [firstMomentMatrix, weightedMomentMatrix, periodicGramMatrix,
      slopeMinMatrix, slopeWeightMatrix, slopeOverlap, firstMomentWeight,
      Matrix.hadamard_apply]
    rw [Nat.cast_min]
    ring
  · simp only [momentBlockMatrix, Matrix.fromBlocks_apply₂₁,
      repeatedPeriodicMeanMatrix_apply_inr_inl, Matrix.hadamard_apply]
    rw [slopeMomentBlock_apply_inr_inl _ hslope]
    simp only [firstMomentMatrix, weightedMomentMatrix, periodicGramMatrix,
      slopeMinMatrix, slopeWeightMatrix, slopeOverlap, firstMomentWeight,
      Matrix.hadamard_apply]
    rw [Nat.cast_min]
    ring
  · simp only [momentBlockMatrix, Matrix.fromBlocks_apply₂₂,
      repeatedPeriodicMeanMatrix_apply_inr_inr, Matrix.hadamard_apply]
    rw [slopeMomentBlock_apply_inr_inr _ hslope]
    simp only [secondCenteredMomentMatrix, weightedMomentMatrix,
      periodicGramMatrix, slopeMinMatrix, slopeWeightMatrix, slopeOverlap,
      secondCenteredMomentWeight, Matrix.hadamard_apply]
    rw [Nat.cast_min]
    ring

/-- Positivity of the concrete finite-camera moment block, obtained from the
continuous step density and the periodic profile Gram factor. -/
theorem cameraMomentBlock_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (period : ℕ) (camera : ι → ℕ)
    (hslope : ∀ i, 0 < cameraSlope (camera i)) :
    (momentBlockMatrix (periodicGramMatrix period camera)
      (firstMomentMatrix period camera)
      (secondCenteredMomentMatrix period camera)).PosSemidef := by
  rw [cameraMomentBlock_eq_hadamard_step period camera hslope]
  exact (repeatedPeriodicMeanMatrix_posSemidef period camera).hadamard
    (slopeMomentBlock_posSemidef fun i => cameraSlope (camera i))

/-- Every slope in the canonical camera package `2, ..., 7` is positive. -/
theorem sixCamera_slope_pos (i : Fin 6) :
    0 < cameraSlope (sixCamera i) := by
  fin_cases i <;> norm_num [sixCamera, cameraSlope]

/-- The exact six-camera moment block is positive semidefinite, now without
the conditional hypothesis left by the purely algebraic whitening layer. -/
theorem sixCameraMomentBlock_posSemidef :
    (momentBlockMatrix sixCameraGram sixCameraFirstMoment
      sixCameraSecondCenteredMoment).PosSemidef := by
  rw [← sixCameraGram_eq, ← sixCameraFirstMoment_eq,
    ← sixCameraSecondCenteredMoment_eq]
  exact cameraMomentBlock_posSemidef 420 sixCamera sixCamera_slope_pos

/-- Concrete positivity of the canonical six-camera variance operator. -/
theorem sixCameraVariance_posSemidef : sixCameraVariance.PosSemidef := by
  exact varianceOperator_posSemidef_of_block sixCameraGram_posDef
    sixCameraFirstMoment_isSelfAdjoint.isHermitian
    sixCameraMomentBlock_posSemidef

end NativeCarrySpectralWeyl.Finite
