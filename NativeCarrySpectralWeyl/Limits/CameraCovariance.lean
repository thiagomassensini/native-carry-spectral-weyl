import NativeCarrySpectralWeyl.Finite.Gram
import NativeCarrySpectralWeyl.Limits.PeriodicMean

/-!
# Weighted cutoff covariance of a finite camera family

This file connects the abstract periodic weighted-mean theorem to the native
camera profiles.  Under the Dirichlet--Abel hypotheses on a scalar weight, the
normalized weighted profile matrix converges to the periodic profile-mean
matrix.  Multiplication by the fixed slope-overlap kernel then gives the
slope-weighted camera Gram matrix from the finite spectral package.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

noncomputable section

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

/-- Real product of two integer camera profiles at one spectral index. -/
def realProfileProduct (camera₁ camera₂ n : ℕ) : ℝ :=
  (profile camera₁ n : ℤ) * (profile camera₂ n : ℤ)

/-- The product of two supported profiles is periodic with every common
profile period. -/
theorem realProfileProduct_periodic {period camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂)
    (hperiod₁ : cameraSlope camera₁ ∣ period)
    (hperiod₂ : cameraSlope camera₂ ∣ period) :
    Function.Periodic (realProfileProduct camera₁ camera₂) period := by
  intro n
  simp only [realProfileProduct]
  rw [profile_add_commonPeriod hcamera₁ hperiod₁,
    profile_add_commonPeriod hcamera₂ hperiod₂]

/-- The abstract period mean of a real profile product is the product mean
used in the finite Gram construction. -/
theorem periodMean_realProfileProduct (period camera₁ camera₂ : ℕ) :
    periodMean (realProfileProduct camera₁ camera₂) period =
      periodicProductMean period camera₁ camera₂ := by
  simp [periodMean, realProfileProduct, periodicProductMean, periodicProductSum,
    Int.cast_sum, Int.cast_mul, smul_eq_mul]

/-- Normalized weighted profile-product matrix at a finite cutoff. -/
def weightedProfileMeanMatrix {ι : Type*} (weight : ℕ → ℝ) (cutoff : ℕ)
    (camera : ι → ℕ) : Matrix ι ι ℝ :=
  fun i j =>
    (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
      ∑ n ∈ Finset.range cutoff,
        weight n * realProfileProduct (camera i) (camera j) n

/-- Entrywise weighted periodic averaging for a finite camera family. -/
theorem tendsto_weightedProfileMeanMatrix_apply {ι : Type*} [Fintype ι]
    {period : ℕ} {camera : ι → ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop) (i j : ι) :
    Tendsto (fun cutoff => weightedProfileMeanMatrix weight cutoff camera i j)
      atTop (nhds (periodicMeanMatrix period camera i j)) := by
  have hproduct : Function.Periodic
      (realProfileProduct (camera i) (camera j)) period :=
    realProfileProduct_periodic (hcamera i) (hcamera j) (hcommon i) (hcommon j)
  have hlimit := tendsto_periodic_weightedMean hperiod hproduct
    hweightAnti hweightZero hmass
  simpa only [weightedProfileMeanMatrix, periodicMeanMatrix_apply,
    periodMean_realProfileProduct, smul_eq_mul] using hlimit

/-- The whole normalized weighted profile matrix converges to the periodic
mean matrix.  Since the camera index is finite, this is simultaneous uniform
entry convergence. -/
theorem tendsto_weightedProfileMeanMatrix {ι : Type*} [Fintype ι]
    {period : ℕ} {camera : ι → ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop) :
    Tendsto (fun cutoff => weightedProfileMeanMatrix weight cutoff camera)
      atTop (nhds (periodicMeanMatrix period camera)) := by
  change Tendsto (fun cutoff i j => weightedProfileMeanMatrix weight cutoff camera i j)
    atTop (nhds fun i j => periodicMeanMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_weightedProfileMeanMatrix_apply hperiod hcamera hcommon
    hweightAnti hweightZero hmass i j

/-- Slope-rescaled normalized profile matrix.  The actual camera cutoff, whose
pair `(i,j)` extends to `min slope_i slope_j * M`, is defined below. -/
def weightedCameraCovariance {ι : Type*} (weight : ℕ → ℝ) (cutoff : ℕ)
    (camera : ι → ℕ) : Matrix ι ι ℝ :=
  slopeMinMatrix (fun i => cameraSlope (camera i)) ⊙
    weightedProfileMeanMatrix weight cutoff camera

/-- The slope-rescaled weighted profile matrix converges to the periodic Gram
matrix. -/
theorem tendsto_weightedCameraCovariance {ι : Type*} [Fintype ι]
    {period : ℕ} {camera : ι → ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop) :
    Tendsto (fun cutoff => weightedCameraCovariance weight cutoff camera)
      atTop (nhds (periodicGramMatrix period camera)) := by
  change Tendsto (fun cutoff i j => weightedCameraCovariance weight cutoff camera i j)
    atTop (nhds fun i j => periodicGramMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  simpa only [weightedCameraCovariance, periodicGramMatrix, Matrix.hadamard_apply]
    using (tendsto_weightedProfileMeanMatrix_apply hperiod hcamera hcommon
      hweightAnti hweightZero hmass i j).const_mul
        (slopeMinMatrix (fun i => cameraSlope (camera i)) i j)

/-- Norm convergence of the slope-rescaled profile matrix to its Gram matrix.
The matrix norm here is the finite entry-sup norm; in particular this is
stronger than entrywise convergence and is equivalent to every standard
finite-dimensional matrix norm. -/
theorem tendsto_norm_weightedCameraCovariance_sub {ι : Type*} [Fintype ι]
    {period : ℕ} {camera : ι → ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop) :
    Tendsto (fun cutoff =>
      ‖weightedCameraCovariance weight cutoff camera -
        periodicGramMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_weightedCameraCovariance hperiod hcamera hcommon
    hweightAnti hweightZero hmass
  have hconstant : Tendsto (fun _ : ℕ => periodicGramMatrix period camera)
      atTop (nhds (periodicGramMatrix period camera)) := tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- A weight has asymptotically linear mass when increasing the cutoff by a
fixed positive natural factor multiplies its total mass by that factor.  This
isolates the regular-variation input `A_{L M} / A_M → L` from the periodic
arithmetic. -/
def HasAsymptoticallyLinearMass (weight : ℕ → ℝ) : Prop :=
  ∀ scale : ℕ, 0 < scale →
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff), weight n)
      atTop (nhds (scale : ℝ))

/-- Multiplication of a natural cutoff by a positive fixed scale tends to
infinity. -/
theorem tendsto_nat_const_mul_atTop {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ => scale * cutoff) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro bound
  exact eventually_atTop.2 ⟨bound, fun cutoff hcutoff => by
    have hone : 1 ≤ scale := hscale
    nlinarith⟩

/-- The genuine pairwise camera cutoff covariance: the `(i,j)` entry contains
the common profile up to `min(slope_i,slope_j) * M` and is normalized by the
base mass `A_M`. -/
def scaledCutoffCameraCovariance {ι : Type*} (weight : ℕ → ℝ) (cutoff : ℕ)
    (camera : ι → ℕ) : Matrix ι ι ℝ :=
  fun i j =>
    (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
      ∑ n ∈ Finset.range
          (min (cameraSlope (camera i)) (cameraSlope (camera j)) * cutoff),
        weight n * realProfileProduct (camera i) (camera j) n

/-- Entrywise convergence of the genuine scaled cutoff covariance to the
camera Gram kernel. -/
theorem tendsto_scaledCutoffCameraCovariance_apply {ι : Type*} [Fintype ι]
    {period : ℕ} {camera : ι → ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop)
    (hmassLinear : HasAsymptoticallyLinearMass weight) (i j : ι) :
    Tendsto (fun cutoff => scaledCutoffCameraCovariance weight cutoff camera i j)
      atTop (nhds (periodicGramMatrix period camera i j)) := by
  let scale := min (cameraSlope (camera i)) (cameraSlope (camera j))
  have hslope (k : ι) : 0 < cameraSlope (camera k) := by
    rw [cameraSlope]
    split_ifs
    · norm_num
    · exact lt_of_lt_of_le (by norm_num) (hcamera k)
  have hscale : 0 < scale := lt_min (hslope i) (hslope j)
  have hproduct : Function.Periodic
      (realProfileProduct (camera i) (camera j)) period :=
    realProfileProduct_periodic (hcamera i) (hcamera j) (hcommon i) (hcommon j)
  have havg := tendsto_periodic_weightedMean hperiod hproduct
    hweightAnti hweightZero hmass
  have hscaledAvg : Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff), weight n)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          weight n * realProfileProduct (camera i) (camera j) n)
      atTop (nhds (periodicProductMean period (camera i) (camera j))) := by
    have hcomp := havg.comp (tendsto_nat_const_mul_atTop hscale)
    change Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff), weight n)⁻¹ •
        ∑ n ∈ Finset.range (scale * cutoff),
          weight n • realProfileProduct (camera i) (camera j) n)
      atTop (nhds (periodMean
        (realProfileProduct (camera i) (camera j)) period)) at hcomp
    simpa only [periodMean_realProfileProduct, smul_eq_mul] using hcomp
  have hratio := hmassLinear scale hscale
  have hproductLimit := hratio.mul hscaledAvg
  have hscaledMass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range (scale * cutoff), weight n) atTop atTop :=
    hmass.comp (tendsto_nat_const_mul_atTop hscale)
  have heventual : (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          weight n * realProfileProduct (camera i) (camera j) n) =ᶠ[atTop]
      (fun cutoff : ℕ =>
        ((∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff), weight n) *
        ((∑ n ∈ Finset.range (scale * cutoff), weight n)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            weight n * realProfileProduct (camera i) (camera j) n)) := by
    filter_upwards [hscaledMass.eventually_gt_atTop 0] with cutoff hpositive
    field_simp [ne_of_gt hpositive]
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          weight n * realProfileProduct (camera i) (camera j) n)
      atTop (nhds ((scale : ℝ) *
        periodicProductMean period (camera i) (camera j))) :=
    hproductLimit.congr' heventual.symm
  simpa only [scaledCutoffCameraCovariance, scale, periodicGramMatrix_apply]
    using hlimit

/-- The genuine finite scaled cutoff covariance converges as a matrix to the
periodic camera Gram matrix. -/
theorem tendsto_scaledCutoffCameraCovariance {ι : Type*} [Fintype ι]
    {period : ℕ} {camera : ι → ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop)
    (hmassLinear : HasAsymptoticallyLinearMass weight) :
    Tendsto (fun cutoff => scaledCutoffCameraCovariance weight cutoff camera)
      atTop (nhds (periodicGramMatrix period camera)) := by
  change Tendsto
    (fun cutoff i j => scaledCutoffCameraCovariance weight cutoff camera i j)
    atTop (nhds fun i j => periodicGramMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_scaledCutoffCameraCovariance_apply hperiod hcamera hcommon
    hweightAnti hweightZero hmass hmassLinear i j

/-- Uniform finite-matrix norm convergence of the genuine scaled cutoff
covariance. -/
theorem tendsto_norm_scaledCutoffCameraCovariance_sub {ι : Type*} [Fintype ι]
    {period : ℕ} {camera : ι → ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop)
    (hmassLinear : HasAsymptoticallyLinearMass weight) :
    Tendsto (fun cutoff =>
      ‖scaledCutoffCameraCovariance weight cutoff camera -
        periodicGramMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_scaledCutoffCameraCovariance hperiod hcamera hcommon
    hweightAnti hweightZero hmass hmassLinear
  have hconstant : Tendsto (fun _ : ℕ => periodicGramMatrix period camera)
      atTop (nhds (periodicGramMatrix period camera)) := tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- The genuine scaled cutoff covariance of cameras `2, ..., 7` converges to
the exact documented six-camera Gram matrix. -/
theorem tendsto_sixCamera_scaledCutoffCovariance {weight : ℕ → ℝ}
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop)
    (hmassLinear : HasAsymptoticallyLinearMass weight) :
    Tendsto (fun cutoff => scaledCutoffCameraCovariance weight cutoff sixCamera)
      atTop (nhds sixCameraGram) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [sixCameraGram_eq] using
    (tendsto_scaledCutoffCameraCovariance (period := 420) (camera := sixCamera)
      (by norm_num) hcamera sixCamera_commonPeriod hweightAnti hweightZero hmass
      hmassLinear)

/-- Uniform finite-matrix norm convergence for the exact six-camera package. -/
theorem tendsto_norm_sixCamera_scaledCutoffCovariance_sub {weight : ℕ → ℝ}
    (hweightAnti : Antitone weight)
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop)
    (hmassLinear : HasAsymptoticallyLinearMass weight) :
    Tendsto (fun cutoff =>
      ‖scaledCutoffCameraCovariance weight cutoff sixCamera - sixCameraGram‖)
      atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [sixCameraGram_eq] using
    (tendsto_norm_scaledCutoffCameraCovariance_sub
      (period := 420) (camera := sixCamera) (by norm_num) hcamera
      sixCamera_commonPeriod hweightAnti hweightZero hmass hmassLinear)

end NativeCarrySpectralWeyl.Limits
