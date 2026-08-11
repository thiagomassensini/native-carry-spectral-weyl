import NativeCarrySpectralWeyl.Infinite.CameraCompletion
import NativeCarrySpectralWeyl.Infinite.Kolmogorov
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Explicit all-bases Naimark isometry

The Kolmogorov vectors `r_b` realize the periodic profile-mean kernel
`m_bc`.  This file realizes the remaining slope factor by putting the
constant vector `r_b` on the interval `(0, ell_b]` inside
`L² ((0, ∞), K₀)`.  Lebesgue measure restricted to `(0, ∞)` gives

`inner (1_(0,ell_b] r_b) (1_(0,ell_c] r_c)
  = min(ell_b, ell_c) * m_bc = gramKernel b c`.

Finite linear combinations therefore define an isometry from the intrinsic
camera `Finsupp` space.  Its continuous extension along the dense
completion embedding is the explicit all-bases Naimark isometry

`CameraHilbert →ₗᵢ[ℝ] L² ((0, ∞), K₀)`.

This is only the isometric realization.  The logarithmic multiplication
operator, its projection-valued measure, compressed Cauchy transforms and
the unbounded Weyl inverse are separate subsequent obligations.
-/

open scoped ENNReal MeasureTheory RealInnerProductSpace
open Set MeasureTheory

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

open NativeCarrySpectralWeyl.Camera

/-- Lebesgue measure on the positive half-line, represented as a restricted
measure on `ℝ`. -/
def positiveLebesgueMeasure : Measure ℝ :=
  volume.restrict (Ioi 0)

/-- The interval carrying the Kolmogorov vector of one camera. -/
def cameraInterval (camera : CameraIndex) : Set ℝ :=
  Ioc 0 (cameraSlope (cameraLabel camera) : ℝ)

/-- Every camera interval is Lebesgue measurable. -/
theorem cameraInterval_measurable (camera : CameraIndex) :
    MeasurableSet (cameraInterval camera) :=
  measurableSet_Ioc

/-- Every camera interval lies in the positive half-line. -/
theorem cameraInterval_subset_positive (camera : CameraIndex) :
    cameraInterval camera ⊆ Ioi 0 := by
  intro x hx
  exact hx.1

/-- Every camera interval has finite positive-half-line measure. -/
theorem positiveLebesgueMeasure_cameraInterval_ne_top
    (camera : CameraIndex) :
    positiveLebesgueMeasure (cameraInterval camera) ≠ ∞ := by
  rw [positiveLebesgueMeasure,
    Measure.restrict_apply (cameraInterval_measurable camera)]
  exact ne_of_lt
    ((measure_mono Set.inter_subset_left).trans_lt measure_Ioc_lt_top)

/-- The overlap of two camera intervals has length equal to the smaller
camera slope.  This is the measure-theoretic source of the slope-minimum
factor in the all-bases Gram kernel. -/
theorem positiveLebesgueMeasure_inter_cameraInterval
    (camera₁ camera₂ : CameraIndex) :
    positiveLebesgueMeasure.real
        (cameraInterval camera₁ ∩ cameraInterval camera₂) =
      (min (cameraSlope (cameraLabel camera₁))
        (cameraSlope (cameraLabel camera₂)) : ℕ) := by
  rw [positiveLebesgueMeasure, measureReal_restrict_apply]
  · rw [cameraInterval, cameraInterval, Ioc_inter_Ioc]
    simp only [max_self]
    rw [inter_eq_left.mpr]
    · rw [Real.volume_real_Ioc_of_le]
      · simp only [sub_zero, Nat.cast_min]
      · exact le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro x hx
      exact hx.1
  · exact (cameraInterval_measurable camera₁).inter
      (cameraInterval_measurable camera₂)

/-- The explicit Naimark dilation space `L² ((0, ∞), K₀)`. -/
abbrev NaimarkSpace :=
  Lp KolmogorovSpace 2 positiveLebesgueMeasure

/-- The step vector `1_(0,ell_b] r_b` associated with one camera. -/
def naimarkCameraVector (camera : CameraIndex) : NaimarkSpace :=
  indicatorConstLp 2 (cameraInterval_measurable camera)
    (positiveLebesgueMeasure_cameraInterval_ne_top camera)
    (kolmogorovVector camera)

/-- The `L²` representative of a Naimark camera vector is almost everywhere
the documented constant indicator function. -/
theorem naimarkCameraVector_coeFn (camera : CameraIndex) :
    ⇑(naimarkCameraVector camera) =ᵐ[positiveLebesgueMeasure]
      (cameraInterval camera).indicator
        (fun _ => kolmogorovVector camera) := by
  exact indicatorConstLp_coeFn

/-- Naimark camera vectors recover the complete all-bases Gram kernel. -/
@[simp] theorem inner_naimarkCameraVector
    (camera₁ camera₂ : CameraIndex) :
    inner ℝ (naimarkCameraVector camera₁) (naimarkCameraVector camera₂) =
      gramKernel camera₁ camera₂ := by
  rw [naimarkCameraVector, naimarkCameraVector,
    L2.inner_indicatorConstLp_indicatorConstLp
      (cameraInterval_measurable camera₁)
      (cameraInterval_measurable camera₂)
      (positiveLebesgueMeasure_cameraInterval_ne_top camera₁)
      (positiveLebesgueMeasure_cameraInterval_ne_top camera₂),
    positiveLebesgueMeasure_inter_cameraInterval,
    inner_kolmogorovVector]
  simp [gramKernel]

/-- The squared norm of one Naimark camera vector is its Gram diagonal. -/
theorem norm_naimarkCameraVector_sq (camera : CameraIndex) :
    ‖naimarkCameraVector camera‖ ^ 2 = gramKernel camera camera := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ)]
  exact inner_naimarkCameraVector camera camera

/-- Finite coefficient vectors are sent to the corresponding finite linear
combination of explicit indicator vectors. -/
def naimarkCoreMap : CameraFinsupp →ₗ[ℝ] NaimarkSpace :=
  Finsupp.linearCombination ℝ naimarkCameraVector

/-- Coefficient-level formula for the explicit step-function map. -/
theorem naimarkCoreMap_apply (u : CameraFinsupp) :
    naimarkCoreMap u =
      u.sum fun camera coefficient =>
        coefficient • naimarkCameraVector camera :=
  rfl

/-- The core map sends a single camera coefficient to the expected scalar
multiple of its indicator vector. -/
@[simp] theorem naimarkCoreMap_single (camera : CameraIndex)
    (coefficient : ℝ) :
    naimarkCoreMap (Finsupp.single camera coefficient) =
      coefficient • naimarkCameraVector camera := by
  simp [naimarkCoreMap]

/-- The explicit step-function map realizes the intrinsic Gram form exactly
on finitely supported camera coefficients. -/
theorem naimarkCoreMap_inner (u v : CameraFinsupp) :
    inner ℝ (naimarkCoreMap u) (naimarkCoreMap v) = gramForm u v := by
  classical
  rw [gramForm_comm]
  simp only [naimarkCoreMap, Finsupp.linearCombination_apply,
    Finsupp.sum_inner, Finsupp.inner_sum, real_inner_smul_left,
    real_inner_smul_right, inner_naimarkCameraVector, gramForm]
  apply Finsupp.sum_congr
  intro camera₂ hcamera₂
  apply Finsupp.sum_congr
  intro camera₁ hcamera₁
  rw [gramKernel_comm camera₁ camera₂]
  ring

/-- The explicit step-function map preserves the intrinsic camera norm. -/
theorem naimarkCoreMap_norm (u : CameraFinsupp) :
    ‖naimarkCoreMap u‖ = ‖u‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    naimarkCoreMap_inner, cameraFinsupp_inner_eq_gramForm]

/-- The coefficient-level Naimark map bundled as a linear isometry. -/
def naimarkCoreIsometry : CameraFinsupp →ₗᵢ[ℝ] NaimarkSpace where
  toLinearMap := naimarkCoreMap
  norm_map' := naimarkCoreMap_norm

/-- The bundled core isometry has the expected value on a single camera. -/
@[simp] theorem naimarkCoreIsometry_single (camera : CameraIndex)
    (coefficient : ℝ) :
    naimarkCoreIsometry (Finsupp.single camera coefficient) =
      coefficient • naimarkCameraVector camera :=
  naimarkCoreMap_single camera coefficient

/-- Continuous extension of the core Naimark map along the canonical dense
embedding into the camera Hilbert completion. -/
def naimarkExtension : CameraHilbert →L[ℝ] NaimarkSpace :=
  naimarkCoreIsometry.toContinuousLinearMap.extend
    cameraEmbedding.toContinuousLinearMap

/-- The extension agrees exactly with the explicit step-function map on the
dense finitely supported core. -/
@[simp] theorem naimarkExtension_cameraEmbedding (u : CameraFinsupp) :
    naimarkExtension (cameraEmbedding u) = naimarkCoreIsometry u := by
  exact ContinuousLinearMap.extend_eq
    naimarkCoreIsometry.toContinuousLinearMap cameraEmbedding_denseRange
      cameraEmbedding.isometry.isUniformInducing u

/-- The continuous extension remains norm preserving on the whole camera
Hilbert completion. -/
theorem naimarkExtension_norm (x : CameraHilbert) :
    ‖naimarkExtension x‖ = ‖x‖ := by
  refine cameraEmbedding_denseRange.induction_on
    (p := fun y => ‖naimarkExtension y‖ = ‖y‖) x ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp naimarkExtension.continuous) continuous_norm
  · intro u
    rw [naimarkExtension_cameraEmbedding, naimarkCoreIsometry.norm_map,
      cameraEmbedding.norm_map]

/-- Explicit all-bases Naimark isometry into `L² ((0, ∞), K₀)`. -/
def naimarkIsometry : CameraHilbert →ₗᵢ[ℝ] NaimarkSpace where
  toLinearMap := naimarkExtension.toLinearMap
  norm_map' := naimarkExtension_norm

/-- The all-bases isometry agrees with the finite step-function formula on
the dense camera core. -/
@[simp] theorem naimarkIsometry_cameraEmbedding (u : CameraFinsupp) :
    naimarkIsometry (cameraEmbedding u) = naimarkCoreIsometry u :=
  naimarkExtension_cameraEmbedding u

/-- Every canonical camera vector is sent to its documented constant
indicator function. -/
@[simp] theorem naimarkIsometry_cameraVector (camera : CameraIndex) :
    naimarkIsometry (cameraVector camera) = naimarkCameraVector camera := by
  rw [cameraVector, naimarkIsometry_cameraEmbedding,
    naimarkCoreIsometry_single, one_smul]

/-- The completed Naimark isometry preserves every camera inner product. -/
@[simp] theorem naimarkIsometry_inner (x y : CameraHilbert) :
    inner ℝ (naimarkIsometry x) (naimarkIsometry y) = inner ℝ x y :=
  naimarkIsometry.inner_map_map x y

end NativeCarrySpectralWeyl.Infinite
