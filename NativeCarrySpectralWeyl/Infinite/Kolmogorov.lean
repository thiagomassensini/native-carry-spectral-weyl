import NativeCarrySpectralWeyl.Infinite.GramKernel
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Kolmogorov realization of the all-bases periodic kernel

The periodic profile-mean kernel `m_bc` is positive semidefinite on every
finite camera family.  This file forms its canonical algebraic
pre-inner-product space, lets Mathlib's completion quotient the possible null
space automatically, and obtains a complete real Hilbert space `K₀` generated
densely by canonical vectors `r_b` satisfying

`inner ℝ (r_b) (r_c) = periodicMeanKernel b c`.

This is deliberately the Kolmogorov layer only.  The slope factor
`min (ell_b) (ell_c)` in the camera Gram kernel is not part of `K₀`; it is
realized later by indicator functions in the Naimark space
`L² ((0, ∞), K₀)`.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits

/-- On a finite camera set, the canonical periodic-mean kernel can be
evaluated using the single common period attached to that set. -/
theorem periodicMeanKernel_eq_commonPeriod {support : Finset CameraIndex}
    {camera₁ camera₂ : CameraIndex} (hcamera₁ : camera₁ ∈ support)
    (hcamera₂ : camera₂ ∈ support) :
    periodicMeanKernel camera₁ camera₂ =
      periodicProductMean (finiteSupportPeriod support)
        (cameraLabel camera₁) (cameraLabel camera₂) := by
  rw [periodicMeanKernel,
    periodicProductMean_eq_pairPeriod camera₁ camera₂
      (pairPeriod_dvd_finiteSupportPeriod hcamera₁ hcamera₂)
      (finiteSupportPeriod_pos support)]

/-- Principal finite restriction of the all-bases periodic-mean kernel. -/
def finitePeriodicMeanMatrix (support : Finset CameraIndex) :
    Matrix support support ℝ :=
  fun camera₁ camera₂ => periodicMeanKernel camera₁.1 camera₂.1

/-- A finite periodic-mean restriction is exactly the previously constructed
periodic profile-mean matrix over its canonical common period. -/
theorem finitePeriodicMeanMatrix_eq_periodicMeanMatrix
    (support : Finset CameraIndex) :
    finitePeriodicMeanMatrix support =
      periodicMeanMatrix (finiteSupportPeriod support)
        (fun camera : support => cameraLabel camera.1) := by
  ext camera₁ camera₂
  rw [finitePeriodicMeanMatrix, periodicMeanMatrix_apply,
    periodicMeanKernel_eq_commonPeriod camera₁.property camera₂.property]

/-- Every finite principal restriction of the all-bases periodic-mean kernel
is positive semidefinite. -/
theorem finitePeriodicMeanMatrix_posSemidef (support : Finset CameraIndex) :
    (finitePeriodicMeanMatrix support).PosSemidef := by
  rw [finitePeriodicMeanMatrix_eq_periodicMeanMatrix]
  exact periodicMeanMatrix_posSemidef _ _

/-- A type-distinct algebraic copy of finitely supported camera
coefficients.  It is kept distinct from `CameraFinsupp`, because the two
spaces carry different intrinsic forms and hence different norms. -/
def KolmogorovPre := CameraIndex →₀ ℝ

instance instAddCommGroupKolmogorovPre : AddCommGroup KolmogorovPre :=
  inferInstanceAs (AddCommGroup (CameraIndex →₀ ℝ))

instance instModuleKolmogorovPre : Module ℝ KolmogorovPre :=
  inferInstanceAs (Module ℝ (CameraIndex →₀ ℝ))

/-- The coefficient-level linear equivalence between the type-distinct
Kolmogorov algebraic space and ordinary `Finsupp`. -/
def kolmogorovPreEquiv : KolmogorovPre ≃ₗ[ℝ] (CameraIndex →₀ ℝ) where
  toFun u := u
  invFun u := u
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Algebraic coordinate vector in the type-distinct Kolmogorov core. -/
def kolmogorovSingle (camera : CameraIndex) (coefficient : ℝ) :
    KolmogorovPre :=
  kolmogorovPreEquiv.symm (Finsupp.single camera coefficient)

/-- Bilinear periodic-mean form on finitely supported camera coefficients. -/
def periodicMeanForm (u v : KolmogorovPre) : ℝ :=
  (kolmogorovPreEquiv u).sum fun camera₁ coefficient₁ =>
    (kolmogorovPreEquiv v).sum fun camera₂ coefficient₂ =>
      coefficient₁ * periodicMeanKernel camera₁ camera₂ * coefficient₂

/-- Restriction of a Kolmogorov coefficient vector to the subtype of its own
support. -/
def periodicSupportCoefficients (u : KolmogorovPre) :
    (kolmogorovPreEquiv u).support →₀ ℝ :=
  Finsupp.subtypeDomain
    (fun camera => camera ∈ (kolmogorovPreEquiv u).support)
    (kolmogorovPreEquiv u)

/-- The periodic-mean form is symmetric. -/
theorem periodicMeanForm_comm (u v : KolmogorovPre) :
    periodicMeanForm u v = periodicMeanForm v u := by
  classical
  simp only [periodicMeanForm, Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro camera₂ hcamera₂
  apply Finset.sum_congr rfl
  intro camera₁ hcamera₁
  rw [periodicMeanKernel_comm]
  ring

/-- The self-pairing of a finitely supported vector is the quadratic form of
the finite periodic-mean matrix on its support. -/
theorem periodicMeanForm_self_eq_finitePeriodicMeanMatrix
    (u : KolmogorovPre) :
    periodicMeanForm u u =
      (periodicSupportCoefficients u).sum fun camera₁ coefficient₁ =>
        (periodicSupportCoefficients u).sum fun camera₂ coefficient₂ =>
          star coefficient₁ *
            finitePeriodicMeanMatrix (kolmogorovPreEquiv u).support
              camera₁ camera₂ *
              coefficient₂ := by
  classical
  simp [periodicMeanForm, periodicSupportCoefficients,
    finitePeriodicMeanMatrix, Finsupp.sum,
    ← Finset.sum_attach (kolmogorovPreEquiv u).support,
    ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain]

/-- The periodic-mean form is nonnegative on every finitely supported
coefficient vector. -/
theorem periodicMeanForm_nonneg (u : KolmogorovPre) :
    0 ≤ periodicMeanForm u u := by
  rw [periodicMeanForm_self_eq_finitePeriodicMeanMatrix]
  exact (finitePeriodicMeanMatrix_posSemidef
    (kolmogorovPreEquiv u).support).2
    (periodicSupportCoefficients u)

/-- The periodic-mean form is additive in its first variable. -/
theorem periodicMeanForm_add_left (u₁ u₂ v : KolmogorovPre) :
  periodicMeanForm (u₁ + u₂) v =
      periodicMeanForm u₁ v + periodicMeanForm u₂ v := by
  classical
  rw [periodicMeanForm, map_add, Finsupp.sum_add_index'] <;>
    simp [periodicMeanForm, add_mul, Finsupp.sum_add]

/-- The periodic-mean form is additive in its second variable. -/
theorem periodicMeanForm_add_right (u v₁ v₂ : KolmogorovPre) :
    periodicMeanForm u (v₁ + v₂) =
      periodicMeanForm u v₁ + periodicMeanForm u v₂ := by
  rw [periodicMeanForm_comm, periodicMeanForm_add_left]
  simp only [periodicMeanForm_comm]

/-- The periodic-mean form is homogeneous in its first variable. -/
theorem periodicMeanForm_smul_left (scalar : ℝ) (u v : KolmogorovPre) :
    periodicMeanForm (scalar • u) v = scalar * periodicMeanForm u v := by
  classical
  rw [periodicMeanForm, map_smul, Finsupp.sum_smul_index] <;>
    simp [periodicMeanForm, Finsupp.mul_sum, mul_assoc]

/-- The periodic-mean form is homogeneous in its second variable. -/
theorem periodicMeanForm_smul_right (scalar : ℝ) (u v : KolmogorovPre) :
    periodicMeanForm u (scalar • v) = scalar * periodicMeanForm u v := by
  rw [periodicMeanForm_comm, periodicMeanForm_smul_left]
  simp only [periodicMeanForm_comm]

/-- The periodic-mean form vanishes when its first variable vanishes. -/
@[simp] theorem periodicMeanForm_zero_left (v : KolmogorovPre) :
    periodicMeanForm 0 v = 0 := by
  simp [periodicMeanForm]

/-- The periodic-mean form vanishes when its second variable vanishes. -/
@[simp] theorem periodicMeanForm_zero_right (u : KolmogorovPre) :
    periodicMeanForm u 0 = 0 := by
  rw [periodicMeanForm_comm]
  exact periodicMeanForm_zero_left u

/-- Canonical coordinate vectors recover the periodic-mean kernel. -/
@[simp] theorem periodicMeanForm_single_single
    (camera₁ camera₂ : CameraIndex) (coefficient₁ coefficient₂ : ℝ) :
    periodicMeanForm (kolmogorovSingle camera₁ coefficient₁)
        (kolmogorovSingle camera₂ coefficient₂) =
      coefficient₁ * periodicMeanKernel camera₁ camera₂ * coefficient₂ := by
  classical
  simp [periodicMeanForm, kolmogorovSingle]

/-- Positive-semidefinite pre-inner-product core induced by the all-bases
periodic-mean kernel. -/
@[implicit_reducible]
def periodicMeanInnerProductCore :
    PreInnerProductSpace.Core ℝ KolmogorovPre where
  inner := periodicMeanForm
  conj_inner_symm u v := by
    simpa only [starRingEnd_apply, star_trivial] using periodicMeanForm_comm v u
  re_inner_nonneg := periodicMeanForm_nonneg
  add_left := periodicMeanForm_add_left
  smul_left u v scalar := by
    simpa only [starRingEnd_apply, star_trivial] using
      periodicMeanForm_smul_left scalar u v

/-- Intrinsic seminormed additive-group structure generated by the
periodic-mean form.  Null vectors are identified by the completion below. -/
noncomputable instance instSeminormedAddCommGroupKolmogorovPre :
    SeminormedAddCommGroup KolmogorovPre :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ KolmogorovPre _ _ _
    periodicMeanInnerProductCore

/-- Intrinsic real pre-inner-product structure generated by the periodic-mean
form. -/
noncomputable instance instInnerProductSpaceKolmogorovPre :
    InnerProductSpace ℝ KolmogorovPre :=
  InnerProductSpace.ofCore periodicMeanInnerProductCore

/-- The intrinsic pre-inner product is exactly the periodic-mean form. -/
@[simp] theorem kolmogorovPre_inner_eq_periodicMeanForm
    (u v : KolmogorovPre) :
    inner ℝ u v = periodicMeanForm u v := rfl

/-- The square of the intrinsic seminorm is the periodic-mean quadratic
form. -/
theorem kolmogorovPre_norm_sq (u : KolmogorovPre) :
    ‖u‖ ^ 2 = periodicMeanForm u u := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ)]
  rfl

/-- Canonical Kolmogorov Hilbert space of the periodic-mean kernel.  Mathlib's
completion first separates seminorm-zero vectors and then completes. -/
abbrev KolmogorovSpace := UniformSpace.Completion KolmogorovPre

/-- The canonical periodic-kernel Kolmogorov space is complete. -/
theorem kolmogorovSpace_isComplete_univ :
    IsComplete (Set.univ : Set KolmogorovSpace) :=
  complete_univ

/-- Canonical linear norm-preserving map from finitely supported coefficients
into the Kolmogorov completion. -/
def kolmogorovEmbedding : KolmogorovPre →ₗᵢ[ℝ] KolmogorovSpace :=
  UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := KolmogorovPre)

/-- The Kolmogorov embedding is the ordinary completion coercion. -/
@[simp] theorem kolmogorovEmbedding_apply (u : KolmogorovPre) :
    kolmogorovEmbedding u = (u : KolmogorovSpace) := rfl

/-- Finitely supported periodic-kernel coefficients have dense image in the
Kolmogorov space. -/
theorem kolmogorovEmbedding_denseRange : DenseRange kolmogorovEmbedding := by
  change DenseRange ((↑) : KolmogorovPre → KolmogorovSpace)
  exact UniformSpace.Completion.denseRange_coe

/-- Completion preserves the periodic-mean inner product exactly. -/
theorem kolmogorovEmbedding_inner (u v : KolmogorovPre) :
    inner ℝ (kolmogorovEmbedding u) (kolmogorovEmbedding v) =
      periodicMeanForm u v := by
  simp

/-- Canonical Kolmogorov vector `r_b` associated with one native camera. -/
def kolmogorovVector (camera : CameraIndex) : KolmogorovSpace :=
  kolmogorovEmbedding (kolmogorovSingle camera 1)

/-- The canonical Kolmogorov vectors realize the periodic-mean kernel
exactly. -/
@[simp] theorem inner_kolmogorovVector (camera₁ camera₂ : CameraIndex) :
    inner ℝ (kolmogorovVector camera₁) (kolmogorovVector camera₂) =
      periodicMeanKernel camera₁ camera₂ := by
  simp [kolmogorovVector]

/-- The squared norm of a canonical Kolmogorov vector is the corresponding
diagonal periodic mean. -/
theorem norm_kolmogorovVector_sq (camera : CameraIndex) :
    ‖kolmogorovVector camera‖ ^ 2 = periodicMeanKernel camera camera := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ)]
  exact inner_kolmogorovVector camera camera

/-- Finite linear combinations of the canonical vectors are exactly the
images of algebraic Kolmogorov coefficient vectors. -/
theorem kolmogorovEmbedding_eq_linearCombination (u : KolmogorovPre) :
    kolmogorovEmbedding u =
      Finsupp.linearCombination ℝ kolmogorovVector
        (kolmogorovPreEquiv u) := by
  have hmaps :
      (kolmogorovEmbedding : KolmogorovPre →ₗ[ℝ] KolmogorovSpace).comp
          kolmogorovPreEquiv.symm.toLinearMap =
        Finsupp.linearCombination ℝ kolmogorovVector := by
    apply Finsupp.lhom_ext
    intro camera coefficient
    rw [LinearMap.comp_apply, Finsupp.linearCombination_single]
    change kolmogorovEmbedding
        (kolmogorovPreEquiv.symm (Finsupp.single camera coefficient)) =
      coefficient • kolmogorovVector camera
    have hsingle :
        kolmogorovPreEquiv.symm (Finsupp.single camera coefficient) =
          coefficient •
            kolmogorovPreEquiv.symm (Finsupp.single camera 1) := by
      apply kolmogorovPreEquiv.injective
      simp
    rw [hsingle, map_smul]
    rfl
  calc
    kolmogorovEmbedding u =
        ((kolmogorovEmbedding : KolmogorovPre →ₗ[ℝ] KolmogorovSpace).comp
          kolmogorovPreEquiv.symm.toLinearMap) (kolmogorovPreEquiv u) := by
            simp
    _ = Finsupp.linearCombination ℝ kolmogorovVector
        (kolmogorovPreEquiv u) := LinearMap.congr_fun hmaps _

/-- The algebraic span of the canonical Kolmogorov vectors contains the
dense completion image. -/
theorem range_kolmogorovEmbedding_subset_span :
    Set.range kolmogorovEmbedding ⊆
      (Submodule.span ℝ (Set.range kolmogorovVector) :
        Set KolmogorovSpace) := by
  rintro _ ⟨u, rfl⟩
  rw [kolmogorovEmbedding_eq_linearCombination]
  rw [← Finsupp.range_linearCombination]
  exact ⟨kolmogorovPreEquiv u, rfl⟩

/-- The canonical vectors `r_b` generate the Kolmogorov space densely. -/
theorem dense_span_kolmogorovVector :
    Dense (Submodule.span ℝ (Set.range kolmogorovVector) :
      Set KolmogorovSpace) :=
  kolmogorovEmbedding_denseRange.mono
    range_kolmogorovEmbedding_subset_span

end NativeCarrySpectralWeyl.Infinite
