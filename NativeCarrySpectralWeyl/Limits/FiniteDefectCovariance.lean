import NativeCarrySpectralWeyl.Camera.NaturalInteriorProfile
import NativeCarrySpectralWeyl.Finite.ReturnMetric
import NativeCarrySpectralWeyl.Limits.ResolventWeight
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic

/-!
# Literal finite defect-probe covariance

This file connects the exact finite native-camera coefficients to the
resolvent-weighted periodic covariance.  It keeps the paper indexing: the
spectral position is `n + 1`, so the coefficient at that position is paired
with `resolventWeight z n = |z - log(n+1)|⁻²`.

The already formalized coefficient bridge shows that the complete finite
stencil agrees with the periodic profile on its core.  The only remaining
terms form a uniformly bounded tail, including the one-unit antipodal
correction of even cameras.  That tail vanishes after resolvent-mass
normalization.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- Fixed seed/tail width of a native camera beyond its periodic core. -/
def cameraBoundaryWidth (camera : ℕ) : ℕ :=
  if camera = 2 then 1 else camera / 2

/-- Last positive spectral position emitted by a finite native camera. -/
def finiteCameraWindow (camera cutoff : ℕ) : ℕ :=
  cameraSlope camera * cutoff + cameraBoundaryWidth camera

@[simp] theorem cameraBoundaryWidth_two : cameraBoundaryWidth 2 = 1 := by
  simp [cameraBoundaryWidth]

theorem cameraBoundaryWidth_of_ne_two {camera : ℕ} (hcamera : camera ≠ 2) :
    cameraBoundaryWidth camera = camera / 2 := by
  simp [cameraBoundaryWidth, hcamera]

@[simp] theorem finiteCameraWindow_two (cutoff : ℕ) :
    finiteCameraWindow 2 cutoff = 4 * cutoff + 1 := by
  simp [finiteCameraWindow]

theorem finiteCameraWindow_of_ne_two {camera : ℕ} (hcamera : camera ≠ 2)
    (cutoff : ℕ) :
    finiteCameraWindow camera cutoff = camera * cutoff + camera / 2 := by
  simp [finiteCameraWindow, cameraBoundaryWidth_of_ne_two hcamera,
    cameraSlope_of_ne_two hcamera]

/-- On the full slope-scaled core, the literal finite coefficient is exactly
the periodic coefficient, including all seed positions. -/
theorem finiteCoefficient_eq_profile_of_le_core {camera cutoff position : ℕ}
    (hcamera : 2 ≤ camera) (hposition : 1 ≤ position)
    (hcore : position ≤ cameraSlope camera * cutoff) :
    finiteCoefficient camera cutoff position = profile camera position := by
  by_cases htwo : camera = 2
  · subst camera
    rw [profile_two]
    apply c2_finiteCoefficient_eq_profile hposition
    simpa using hcore.trans (by omega : 4 * cutoff ≤ 4 * cutoff + 1)
  · have hthree : 3 ≤ camera := by omega
    rw [cameraSlope_of_ne_two htwo] at hcore
    apply natural_finiteCoefficient_eq_profile hthree hposition
    have hhalf : 1 ≤ camera / 2 := Nat.one_le_iff_ne_zero.mpr (by omega)
    omega

/-- Zero-indexed real coefficient used by the finite spectral matrices. -/
def finiteCoefficientAt (camera cutoff n : ℕ) : ℝ :=
  (finiteCoefficient camera cutoff (n + 1) : ℤ)

theorem finiteCoefficientAt_eq_profile_of_lt_core {camera cutoff n : ℕ}
    (hcamera : 2 ≤ camera) (hcore : n < cameraSlope camera * cutoff) :
    finiteCoefficientAt camera cutoff n = (profile camera (n + 1) : ℤ) := by
  simp only [finiteCoefficientAt]
  rw [finiteCoefficient_eq_profile_of_le_core hcamera (by omega) (by omega)]

/-- Every literal finite coefficient vanishes strictly beyond its emitted
window.  This support statement also covers the corrected final coefficient
of an even camera. -/
theorem finiteCoefficient_eq_zero_of_window_lt {camera cutoff position : ℕ}
    (hcamera : 2 ≤ camera)
    (hout : finiteCameraWindow camera cutoff < position) :
    finiteCoefficient camera cutoff position = 0 := by
  by_cases htwo : camera = 2
  · subst camera
    apply c2_finiteCoefficient_eq_zero_of_outside
    right
    simpa only [finiteCameraWindow_two] using hout
  · have hthree : 3 ≤ camera := by omega
    have hout' : camera * cutoff + camera / 2 < position := by
      simpa only [finiteCameraWindow_of_ne_two htwo] using hout
    rcases Nat.even_or_odd camera with heven | hodd
    · have hfour : 4 ≤ camera := by
        obtain ⟨half, rfl⟩ := heven
        omega
      rw [even_finiteCoefficient_eq_profile_window hfour heven]
      split_ifs <;> omega
    · rw [odd_finiteCoefficient_eq_profile_window hthree hodd]
      split_ifs <;> omega

/-- Zero-indexed support form used when expanding finite matrix products. -/
theorem finiteCoefficientAt_eq_zero_of_window_le {camera cutoff n : ℕ}
    (hcamera : 2 ≤ camera) (hout : finiteCameraWindow camera cutoff ≤ n) :
    finiteCoefficientAt camera cutoff n = 0 := by
  simp only [finiteCoefficientAt]
  rw [finiteCoefficient_eq_zero_of_window_lt hcamera (by omega)]
  norm_num

/-- Uniform integer bound for every periodic profile coefficient. -/
theorem profile_natAbs_le (camera n : ℕ) :
    Int.natAbs (profile camera n) ≤ camera + 4 := by
  rw [profile]
  split_ifs with htwo hodd
  · subst camera
    simp only [c2Profile, dvdIndicator]
    split_ifs <;> norm_num
  · simp only [oddProfile, dvdIndicator]
    split_ifs
    · rw [mul_one]
      omega
    · norm_num
  · simp only [evenProfile, dvdIndicator]
    split_ifs
    all_goals norm_num at *
    all_goals omega

/-- Uniform cutoff-independent bound for every literal finite coefficient. -/
theorem finiteCoefficient_natAbs_le {camera cutoff n : ℕ}
    (hcamera : 2 ≤ camera) :
    Int.natAbs (finiteCoefficient camera cutoff n) ≤ camera + 4 := by
  by_cases htwo : camera = 2
  · subst camera
    rw [c2_finiteCoefficient_eq_profile_window]
    split_ifs
    · exact profile_natAbs_le 2 n
    · simp
  · have hthree : 3 ≤ camera := by omega
    rcases Nat.even_or_odd camera with heven | hodd
    · have hfour : 4 ≤ camera := by
        obtain ⟨half, rfl⟩ := heven
        omega
      rw [even_finiteCoefficient_eq_profile_window hfour heven]
      split_ifs
      · simp only [evenProfile, dvdIndicator]
        split_ifs
        all_goals norm_num at *
        all_goals omega
      · norm_num
      · simp
    · rw [odd_finiteCoefficient_eq_profile_window hthree hodd]
      split_ifs
      · simp only [oddProfile, dvdIndicator]
        split_ifs
        · rw [mul_one]
          omega
        · norm_num
      · simp

/-- Real absolute-value form of the uniform finite-coefficient bound. -/
theorem abs_finiteCoefficientAt_le {camera cutoff n : ℕ}
    (hcamera : 2 ≤ camera) :
    |finiteCoefficientAt camera cutoff n| ≤ (camera + 4 : ℕ) := by
  simp only [finiteCoefficientAt]
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast finiteCoefficient_natAbs_le (cutoff := cutoff) (n := n + 1) hcamera

/-- Common slope-scaled core length for a pair of cameras. -/
def pairCoreLength (camera₁ camera₂ cutoff : ℕ) : ℕ :=
  min (cameraSlope camera₁) (cameraSlope camera₂) * cutoff

/-- Common emitted window for a pair of literal finite cameras. -/
def pairFiniteWindow (camera₁ camera₂ cutoff : ℕ) : ℕ :=
  min (finiteCameraWindow camera₁ cutoff) (finiteCameraWindow camera₂ cutoff)

/-- Fixed bound on the pairwise boundary width. -/
def pairBoundaryWidth (camera₁ camera₂ : ℕ) : ℕ :=
  max (cameraBoundaryWidth camera₁) (cameraBoundaryWidth camera₂)

/-- A common finite spectral window large enough to contain every camera in a
finite family. -/
def finiteFamilyWindow {index : Type*} [Fintype index]
    (cutoff : ℕ) (camera : index → ℕ) : ℕ :=
  Finset.univ.sup fun i => finiteCameraWindow (camera i) cutoff

theorem finiteCameraWindow_le_finiteFamilyWindow
    {index : Type*} [Fintype index] (cutoff : ℕ) (camera : index → ℕ)
    (i : index) :
    finiteCameraWindow (camera i) cutoff ≤ finiteFamilyWindow cutoff camera := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun j : index => finiteCameraWindow (camera j) cutoff)
    (Finset.mem_univ i)

/-- Literal finite camera matrix on the common family window. -/
def finiteCameraMatrix {index : Type*} [Fintype index]
    (cutoff : ℕ) (camera : index → ℕ) :
    Matrix index (Fin (finiteFamilyWindow cutoff camera)) ℂ :=
  fun i n => (finiteCoefficientAt (camera i) cutoff n : ℂ)

/-- Diagonal finite resolvent at the paper spectral sites `log(n+1)`. -/
def finiteResolventMatrix (z : ℂ) (window : ℕ) :
    Matrix (Fin window) (Fin window) ℂ :=
  Matrix.diagonal fun n =>
    (z - (Real.log (n.val + 1) : ℂ))⁻¹

/-- Squaring the diagonal finite resolvent gives the concrete resolvent
weights used in the literal covariance. -/
theorem finiteResolventMatrix_mul_conjTranspose (z : ℂ) (window : ℕ) :
    finiteResolventMatrix z window * (finiteResolventMatrix z window)ᴴ =
      Matrix.diagonal fun n : Fin window => (resolventWeight z n.val : ℂ) := by
  rw [finiteResolventMatrix, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext n
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_conj,
    Complex.normSq_inv, resolventWeight]

theorem pairCoreLength_le_pairFiniteWindow (camera₁ camera₂ cutoff : ℕ) :
    pairCoreLength camera₁ camera₂ cutoff ≤
      pairFiniteWindow camera₁ camera₂ cutoff := by
  apply le_min
  · exact le_trans (Nat.mul_le_mul_right cutoff (min_le_left _ _))
      (Nat.le_add_right _ _)
  · exact le_trans (Nat.mul_le_mul_right cutoff (min_le_right _ _))
      (Nat.le_add_right _ _)

theorem pairFiniteWindow_le_core_add_boundary (camera₁ camera₂ cutoff : ℕ) :
    pairFiniteWindow camera₁ camera₂ cutoff ≤
      pairCoreLength camera₁ camera₂ cutoff +
        pairBoundaryWidth camera₁ camera₂ := by
  unfold pairFiniteWindow pairCoreLength pairBoundaryWidth finiteCameraWindow
  rcases le_total (cameraSlope camera₁) (cameraSlope camera₂) with h | h
  · rw [min_eq_left h]
    exact le_trans (min_le_left _ _)
      (Nat.add_le_add_left (le_max_left _ _) _)
  · rw [min_eq_right h]
    exact le_trans (min_le_right _ _)
      (Nat.add_le_add_left (le_max_right _ _) _)

theorem pairBoundaryLength_le (camera₁ camera₂ cutoff : ℕ) :
    pairFiniteWindow camera₁ camera₂ cutoff -
        pairCoreLength camera₁ camera₂ cutoff ≤
      pairBoundaryWidth camera₁ camera₂ := by
  exact Nat.sub_le_iff_le_add'.2
    (pairFiniteWindow_le_core_add_boundary camera₁ camera₂ cutoff)

/-- Extending a pairwise coefficient sum to the common family window adds
only zeros. -/
theorem sum_finiteFamilyWindow_eq_pairFiniteWindow
    {index : Type*} [Fintype index] {camera : index → ℕ}
    (hcamera : ∀ i, 2 ≤ camera i) (cutoff : ℕ) (weight : ℕ → ℂ)
    (i j : index) :
    (∑ n ∈ Finset.range (finiteFamilyWindow cutoff camera),
        weight n * (finiteCoefficientAt (camera i) cutoff n : ℂ) *
          (finiteCoefficientAt (camera j) cutoff n : ℂ)) =
      ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
        weight n * (finiteCoefficientAt (camera i) cutoff n : ℂ) *
          (finiteCoefficientAt (camera j) cutoff n : ℂ) := by
  symm
  apply Finset.sum_subset
  · apply Finset.range_mono
    exact le_trans (min_le_left _ _)
      (finiteCameraWindow_le_finiteFamilyWindow cutoff camera i)
  · intro n hnFamily hnPair
    simp only [Finset.mem_range] at hnFamily hnPair
    have hn : pairFiniteWindow (camera i) (camera j) cutoff ≤ n := by omega
    rcases le_total (finiteCameraWindow (camera i) cutoff)
        (finiteCameraWindow (camera j) cutoff) with hij | hji
    · have hwindow : finiteCameraWindow (camera i) cutoff ≤ n := by
        rw [pairFiniteWindow, min_eq_left hij] at hn
        exact hn
      rw [finiteCoefficientAt_eq_zero_of_window_le (hcamera i) hwindow]
      simp
    · have hwindow : finiteCameraWindow (camera j) cutoff ≤ n := by
        rw [pairFiniteWindow, min_eq_right hji] at hn
        exact hn
      rw [finiteCoefficientAt_eq_zero_of_window_le (hcamera j) hwindow]
      simp

/-- Literal normalized covariance of the complete finite coefficient stencils.
The summation range is exactly the overlap of their emitted windows. -/
def finiteCoefficientCovariance {index : Type*} (weight : ℕ → ℝ)
    (cutoff : ℕ) (camera : index → ℕ) : Matrix index index ℝ :=
  fun i j =>
    (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
      ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
        weight n * finiteCoefficientAt (camera i) cutoff n *
          finiteCoefficientAt (camera j) cutoff n

/-- Normalized direct covariance of the literal finite camera matrix and the
finite diagonal resolvent. -/
def normalizedFiniteDirectCovariance {index : Type*} [Fintype index]
    (z : ℂ) (cutoff : ℕ) (camera : index → ℕ) : Matrix index index ℂ :=
  fun i j =>
    ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
      directResolventCovariance
        (finiteCameraMatrix cutoff camera)
        (finiteResolventMatrix z (finiteFamilyWindow cutoff camera)) i j

/-- The normalized direct matrix product is exactly the complexification of
the literal finite coefficient covariance. -/
theorem normalizedFiniteDirectCovariance_eq_finiteCoefficientCovariance
    {index : Type*} [Fintype index] {camera : index → ℕ}
    (hcamera : ∀ i, 2 ≤ camera i) (z : ℂ) (cutoff : ℕ) :
    normalizedFiniteDirectCovariance z cutoff camera =
      fun i j =>
        (finiteCoefficientCovariance (resolventWeight z) cutoff camera i j : ℂ) := by
  ext i j
  rw [normalizedFiniteDirectCovariance, directResolventCovariance]
  calc
    ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
        (((finiteCameraMatrix cutoff camera *
            finiteResolventMatrix z (finiteFamilyWindow cutoff camera)) *
          (finiteResolventMatrix z (finiteFamilyWindow cutoff camera))ᴴ) *
          (finiteCameraMatrix cutoff camera)ᴴ) i j =
      ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
        (finiteCameraMatrix cutoff camera *
          (finiteResolventMatrix z (finiteFamilyWindow cutoff camera) *
            (finiteResolventMatrix z (finiteFamilyWindow cutoff camera))ᴴ) *
          (finiteCameraMatrix cutoff camera)ᴴ) i j := by
            simp only [Matrix.mul_assoc]
    _ = ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
        (finiteCameraMatrix cutoff camera *
          Matrix.diagonal (fun n : Fin (finiteFamilyWindow cutoff camera) =>
            (resolventWeight z n.val : ℂ)) *
          (finiteCameraMatrix cutoff camera)ᴴ) i j := by
            rw [finiteResolventMatrix_mul_conjTranspose]
    _ = _ := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
        finiteCameraMatrix, Complex.star_def, Complex.conj_ofReal]
      have hsum :
          (∑ n : Fin (finiteFamilyWindow cutoff camera),
              (finiteCoefficientAt (camera i) cutoff n.val : ℂ) *
                (resolventWeight z n.val : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n.val : ℂ)) =
            ∑ n ∈ Finset.range
                (pairFiniteWindow (camera i) (camera j) cutoff),
              (resolventWeight z n : ℂ) *
                (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n : ℂ) := by
        calc
          (∑ n : Fin (finiteFamilyWindow cutoff camera),
              (finiteCoefficientAt (camera i) cutoff n.val : ℂ) *
                (resolventWeight z n.val : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n.val : ℂ)) =
            ∑ n ∈ Finset.range (finiteFamilyWindow cutoff camera),
              (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                (resolventWeight z n : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n : ℂ) := by
                  simpa only using Fin.sum_univ_eq_sum_range
                    (fun n : ℕ =>
                      (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                        (resolventWeight z n : ℂ) *
                        (finiteCoefficientAt (camera j) cutoff n : ℂ))
                    (finiteFamilyWindow cutoff camera)
          _ = (∑ n ∈ Finset.range (finiteFamilyWindow cutoff camera),
              (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                (resolventWeight z n : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n : ℂ)) := rfl
          _ =
            ∑ n ∈ Finset.range (finiteFamilyWindow cutoff camera),
              (resolventWeight z n : ℂ) *
                (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n : ℂ) := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  ring
          _ = _ := sum_finiteFamilyWindow_eq_pairFiniteWindow
            hcamera cutoff (fun n => (resolventWeight z n : ℂ)) i j
      rw [hsum]
      simp only [finiteCoefficientCovariance, resolventMass]
      norm_cast

/-- Normalized covariance of the literal finite source probe in the endpoint
return metric. -/
def normalizedFiniteReturnMetricCovariance
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    (z : ℂ) (cutoff : ℕ) (camera : index → ℕ)
    (endpointMap :
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : Matrix bulk endpoint ℂ) : Matrix index index ℂ :=
  fun i j =>
    ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
      returnMetricCovariance
        (finiteCameraMatrix cutoff camera)
        (finiteResolventMatrix z (finiteFamilyWindow cutoff camera))
        endpointMap poisson i j

/-- Exact finite bridge from the endpoint return-metric probe to the literal
camera coefficients.  The only hypotheses are the two finite colligation
identities `P E = B` and `Eᴴ E + Bᴴ B = I`. -/
theorem normalizedFiniteReturnMetricCovariance_eq_finiteCoefficientCovariance
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {camera : index → ℕ} (hcamera : ∀ i, 2 ≤ camera i)
    (z : ℂ) (cutoff : ℕ)
    (endpointMap :
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (bulkMap : Matrix bulk (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    normalizedFiniteReturnMetricCovariance z cutoff camera endpointMap poisson =
      fun i j =>
        (finiteCoefficientCovariance (resolventWeight z) cutoff camera i j : ℂ) := by
  ext i j
  simp only [normalizedFiniteReturnMetricCovariance]
  rw [returnMetricCovariance_eq_directResolventCovariance
    (finiteCameraMatrix cutoff camera)
    (finiteResolventMatrix z (finiteFamilyWindow cutoff camera))
    endpointMap bulkMap poisson hpoisson hisometry]
  have hdirect := normalizedFiniteDirectCovariance_eq_finiteCoefficientCovariance
    hcamera z cutoff
  simpa only [normalizedFiniteDirectCovariance] using
    congr_fun (congr_fun hdirect i) j

/-- Shifted periodic covariance on the exact common core. -/
def shiftedCoreCameraCovariance {index : Type*} (weight : ℕ → ℝ)
    (cutoff : ℕ) (camera : index → ℕ) : Matrix index index ℝ :=
  fun i j =>
    (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
      ∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
        weight n * realProfileProduct (camera i) (camera j) (n + 1)

/-- A periodic weighted sum whose cutoff is multiplied by a fixed positive
natural scale converges, after normalization by the base mass, to that scale
times the period mean. -/
theorem tendsto_scaled_periodic_weightedMean_of_eventually_antitone
    {q : ℕ → ℝ} {period scale : ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    (hq : Function.Periodic q period)
    (hweightAnti : ∃ offset : ℕ, Antitone (fun n => weight (n + offset)))
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop)
    (hmassLinear : HasAsymptoticallyLinearMass weight) :
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff), weight n * q n)
      atTop (nhds ((scale : ℝ) * periodMean q period)) := by
  have havg := tendsto_periodic_weightedMean_of_eventually_antitone
    hperiod hq hweightAnti hweightZero hmass
  have hscaledAvg : Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff), weight n)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff), weight n * q n)
      atTop (nhds (periodMean q period)) := by
    have hcomp := havg.comp (tendsto_nat_const_mul_atTop hscale)
    change Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff), weight n)⁻¹ •
        ∑ n ∈ Finset.range (scale * cutoff), weight n • q n)
      atTop (nhds (periodMean q period)) at hcomp
    simpa only [smul_eq_mul] using hcomp
  have hratio := hmassLinear scale hscale
  have hproductLimit := hratio.mul hscaledAvg
  have hscaledMass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range (scale * cutoff), weight n) atTop atTop :=
    hmass.comp (tendsto_nat_const_mul_atTop hscale)
  apply hproductLimit.congr'
  filter_upwards [hscaledMass.eventually_gt_atTop 0] with cutoff hpositive
  field_simp [ne_of_gt hpositive]

/-- Entrywise limit of the shifted periodic core. -/
theorem tendsto_shiftedCoreCameraCovariance_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {weight : ℕ → ℝ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (hweightAnti : ∃ offset : ℕ, Antitone (fun n => weight (n + offset)))
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop)
    (hmassLinear : HasAsymptoticallyLinearMass weight) (i j : index) :
    Tendsto (fun cutoff => shiftedCoreCameraCovariance weight cutoff camera i j)
      atTop (nhds (periodicGramMatrix period camera i j)) := by
  let scale := min (cameraSlope (camera i)) (cameraSlope (camera j))
  have hslope (k : index) : 0 < cameraSlope (camera k) := by
    rw [cameraSlope]
    split_ifs
    · norm_num
    · exact lt_of_lt_of_le (by norm_num) (hcamera k)
  have hscale : 0 < scale := lt_min (hslope i) (hslope j)
  have hproduct : Function.Periodic
      (realProfileProduct (camera i) (camera j)) period :=
    realProfileProduct_periodic (hcamera i) (hcamera j) (hcommon i) (hcommon j)
  have hshifted : Function.Periodic
      (fun n => realProfileProduct (camera i) (camera j) (n + 1)) period := by
    intro n
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hproduct (n + 1)
  have hmean : periodMean
      (fun n => realProfileProduct (camera i) (camera j) (n + 1)) period =
        periodicProductMean period (camera i) (camera j) := by
    have h := periodMean_natAdd hproduct 1
    rw [periodMean_realProfileProduct] at h
    simpa only [Nat.add_comm] using h
  have hlimit := tendsto_scaled_periodic_weightedMean_of_eventually_antitone
    hperiod hscale hshifted hweightAnti hweightZero hmass hmassLinear
  rw [hmean] at hlimit
  simpa only [shiftedCoreCameraCovariance, pairCoreLength, scale,
    periodicGramMatrix_apply] using hlimit

/-- One padded boundary term.  The fixed range
`pairBoundaryWidth camera₁ camera₂` contains the whole moving tail; entries
past its actual length are set to zero. -/
def finiteBoundaryTerm (weight : ℕ → ℝ) (cutoff camera₁ camera₂ r : ℕ) : ℝ :=
  if r < pairFiniteWindow camera₁ camera₂ cutoff -
      pairCoreLength camera₁ camera₂ cutoff then
    weight (pairCoreLength camera₁ camera₂ cutoff + r) *
      finiteCoefficientAt camera₁ cutoff
        (pairCoreLength camera₁ camera₂ cutoff + r) *
      finiteCoefficientAt camera₂ cutoff
        (pairCoreLength camera₁ camera₂ cutoff + r)
  else 0

/-- Complete seed/tail correction written on a cutoff-independent finite
range. -/
def finiteBoundarySum (weight : ℕ → ℝ) (cutoff camera₁ camera₂ : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (pairBoundaryWidth camera₁ camera₂),
    finiteBoundaryTerm weight cutoff camera₁ camera₂ r

/-- Exact decomposition of the complete literal coefficient sum into its
shifted periodic core and its uniformly finite boundary correction. -/
theorem finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary
    {weight : ℕ → ℝ} {cutoff camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂) :
    (∑ n ∈ Finset.range (pairFiniteWindow camera₁ camera₂ cutoff),
        weight n * finiteCoefficientAt camera₁ cutoff n *
          finiteCoefficientAt camera₂ cutoff n) =
      (∑ n ∈ Finset.range (pairCoreLength camera₁ camera₂ cutoff),
        weight n * realProfileProduct camera₁ camera₂ (n + 1)) +
        finiteBoundarySum weight cutoff camera₁ camera₂ := by
  let core := pairCoreLength camera₁ camera₂ cutoff
  let window := pairFiniteWindow camera₁ camera₂ cutoff
  let tail := window - core
  let boundary := pairBoundaryWidth camera₁ camera₂
  have hcoreWindow : core ≤ window :=
    pairCoreLength_le_pairFiniteWindow camera₁ camera₂ cutoff
  have hwindow : window = core + tail := by
    exact (Nat.add_sub_of_le hcoreWindow).symm
  have htail : tail ≤ boundary :=
    pairBoundaryLength_le camera₁ camera₂ cutoff
  have hcore₁ : core ≤ cameraSlope camera₁ * cutoff :=
    Nat.mul_le_mul_right cutoff (min_le_left _ _)
  have hcore₂ : core ≤ cameraSlope camera₂ * cutoff :=
    Nat.mul_le_mul_right cutoff (min_le_right _ _)
  have htailSum :
      (∑ r ∈ Finset.range tail,
        weight (core + r) * finiteCoefficientAt camera₁ cutoff (core + r) *
          finiteCoefficientAt camera₂ cutoff (core + r)) =
        finiteBoundarySum weight cutoff camera₁ camera₂ := by
    calc
      (∑ r ∈ Finset.range tail,
          weight (core + r) * finiteCoefficientAt camera₁ cutoff (core + r) *
            finiteCoefficientAt camera₂ cutoff (core + r)) =
        ∑ r ∈ Finset.range tail,
          if r < tail then
            weight (core + r) * finiteCoefficientAt camera₁ cutoff (core + r) *
              finiteCoefficientAt camera₂ cutoff (core + r)
          else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            simp only [Finset.mem_range] at hr
            simp [hr]
      _ = ∑ r ∈ Finset.range boundary,
          if r < tail then
            weight (core + r) * finiteCoefficientAt camera₁ cutoff (core + r) *
              finiteCoefficientAt camera₂ cutoff (core + r)
          else 0 := by
            apply Finset.sum_subset (Finset.range_mono htail)
            intro r hrboundary hrtail
            simp only [Finset.mem_range] at hrboundary hrtail
            simp [hrtail]
      _ = finiteBoundarySum weight cutoff camera₁ camera₂ := by
        simp only [finiteBoundarySum, finiteBoundaryTerm, core, window, tail, boundary]
  rw [show pairFiniteWindow camera₁ camera₂ cutoff = core + tail by
    simpa only [window] using hwindow, Finset.sum_range_add]
  calc
    (∑ x ∈ Finset.range core,
        weight x * finiteCoefficientAt camera₁ cutoff x *
          finiteCoefficientAt camera₂ cutoff x) +
      ∑ x ∈ Finset.range tail,
        weight (core + x) * finiteCoefficientAt camera₁ cutoff (core + x) *
          finiteCoefficientAt camera₂ cutoff (core + x) =
      (∑ x ∈ Finset.range core,
        weight x * realProfileProduct camera₁ camera₂ (x + 1)) +
      ∑ x ∈ Finset.range tail,
        weight (core + x) * finiteCoefficientAt camera₁ cutoff (core + x) *
          finiteCoefficientAt camera₂ cutoff (core + x) := by
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        simp only [Finset.mem_range] at hn
        rw [finiteCoefficientAt_eq_profile_of_lt_core hcamera₁
            (hn.trans_le hcore₁),
          finiteCoefficientAt_eq_profile_of_lt_core hcamera₂
            (hn.trans_le hcore₂)]
        simp [realProfileProduct, mul_assoc]
    _ = _ := by rw [htailSum]

/-- Entrywise exact version of the core-plus-boundary decomposition. -/
theorem finiteCoefficientCovariance_eq_shiftedCore_add_boundary
    {index : Type*} {weight : ℕ → ℝ} {cutoff : ℕ} {camera : index → ℕ}
    (hcamera : ∀ i, 2 ≤ camera i) (i j : index) :
    finiteCoefficientCovariance weight cutoff camera i j =
      shiftedCoreCameraCovariance weight cutoff camera i j +
        (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
          finiteBoundarySum weight cutoff (camera i) (camera j) := by
  rw [finiteCoefficientCovariance, shiftedCoreCameraCovariance,
    finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary (hcamera i) (hcamera j)]
  ring

/-- Every fixed padded literal boundary term vanishes for the concrete
resolvent weight. -/
theorem tendsto_resolvent_finiteBoundaryTerm_zero {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (r : ℕ) :
    Tendsto (fun cutoff =>
      finiteBoundaryTerm (resolventWeight z) cutoff camera₁ camera₂ r)
      atTop (nhds 0) := by
  let scale := min (cameraSlope camera₁) (cameraSlope camera₂)
  have hslope₁ : 0 < cameraSlope camera₁ := by
    rw [cameraSlope]
    split_ifs
    · norm_num
    · omega
  have hslope₂ : 0 < cameraSlope camera₂ := by
    rw [cameraSlope]
    split_ifs
    · norm_num
    · omega
  have hscale : 0 < scale := lt_min hslope₁ hslope₂
  have hindex : Tendsto (fun cutoff : ℕ => scale * cutoff + r) atTop atTop :=
    (tendsto_add_atTop_nat r).comp (tendsto_nat_const_mul_atTop hscale)
  have hweight : Tendsto (fun cutoff : ℕ =>
      resolventWeight z (scale * cutoff + r)) atTop (nhds 0) :=
    (tendsto_resolventWeight_zero z).comp hindex
  let coefficientBound : ℝ := (camera₁ + 4 : ℕ) * (camera₂ + 4 : ℕ)
  have hmajorant : Tendsto (fun cutoff : ℕ =>
      coefficientBound * resolventWeight z (scale * cutoff + r))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hweight.const_mul coefficientBound
  have hdom : ∀ cutoff : ℕ,
      |finiteBoundaryTerm (resolventWeight z) cutoff camera₁ camera₂ r| ≤
        coefficientBound * resolventWeight z (scale * cutoff + r) := by
    intro cutoff
    rw [finiteBoundaryTerm]
    split_ifs
    · have hbound₁ := abs_finiteCoefficientAt_le
        (cutoff := cutoff) (n := scale * cutoff + r) hcamera₁
      have hbound₂ := abs_finiteCoefficientAt_le
        (cutoff := cutoff) (n := scale * cutoff + r) hcamera₂
      have hproduct :
          |finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)| ≤
            coefficientBound := by
        exact mul_le_mul hbound₁ hbound₂ (abs_nonneg _) (by positivity)
      simp only [pairCoreLength, scale]
      rw [abs_mul, abs_mul, abs_of_pos (resolventWeight_pos hz _)]
      calc
        resolventWeight z (scale * cutoff + r) *
              |finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
            |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)| =
          (|finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)|) *
            resolventWeight z (scale * cutoff + r) := by ring
        _ ≤ coefficientBound * resolventWeight z (scale * cutoff + r) :=
          mul_le_mul_of_nonneg_right hproduct (resolventWeight_pos hz _).le
    · simp only [abs_zero]
      exact mul_nonneg (by positivity) (resolventWeight_pos hz _).le
  have habs : Tendsto (fun cutoff : ℕ =>
      |finiteBoundaryTerm (resolventWeight z) cutoff camera₁ camera₂ r|)
      atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hdom) hmajorant
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa only [Real.norm_eq_abs] using habs

/-- The complete finite seed/tail correction vanishes before mass
normalization. -/
theorem tendsto_resolvent_finiteBoundarySum_zero {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) :
    Tendsto (fun cutoff =>
      finiteBoundarySum (resolventWeight z) cutoff camera₁ camera₂)
      atTop (nhds 0) := by
  have hsum := tendsto_finsetSum
    (Finset.range (pairBoundaryWidth camera₁ camera₂))
    (fun r _ => tendsto_resolvent_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r)
  simpa only [finiteBoundarySum, Finset.sum_const_zero] using hsum

/-- The normalized literal finite-coefficient covariance has the same
entrywise limit as the periodic camera Gram. -/
theorem tendsto_resolvent_finiteCoefficientCovariance_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff =>
      finiteCoefficientCovariance (resolventWeight z) cutoff camera i j)
      atTop (nhds (periodicGramMatrix period camera i j)) := by
  obtain ⟨offset, hanti⟩ := exists_resolventWeight_antitone_natAdd hz
  have hcore := tendsto_shiftedCoreCameraCovariance_apply
    hperiod hcamera hcommon ⟨offset, by simpa only [Nat.add_comm] using hanti⟩
      (tendsto_resolventWeight_zero z) (tendsto_resolventMass_atTop hz)
      (resolventWeight_hasAsymptoticallyLinearMass hz) i j
  have hboundary := tendsto_resolvent_finiteBoundarySum_zero
    hz (hcamera i) (hcamera j)
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hcorrection : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        finiteBoundarySum (resolventWeight z) cutoff (camera i) (camera j))
      atTop (nhds 0) := by simpa using hinvMass.mul hboundary
  have hsum := hcore.add hcorrection
  have hsum' : Tendsto (fun cutoff : ℕ =>
      shiftedCoreCameraCovariance (resolventWeight z) cutoff camera i j +
        (resolventMass z cutoff)⁻¹ *
          finiteBoundarySum (resolventWeight z) cutoff (camera i) (camera j))
      atTop (nhds (periodicGramMatrix period camera i j)) := by
    simpa only [add_zero] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [finiteCoefficientCovariance_eq_shiftedCore_add_boundary hcamera i j]
  simp only [resolventMass]

/-- Simultaneous finite-matrix convergence of the complete literal camera
coefficients. -/
theorem tendsto_resolvent_finiteCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      finiteCoefficientCovariance (resolventWeight z) cutoff camera)
      atTop (nhds (periodicGramMatrix period camera)) := by
  change Tendsto
    (fun cutoff i j => finiteCoefficientCovariance (resolventWeight z) cutoff camera i j)
    atTop (nhds fun i j => periodicGramMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_resolvent_finiteCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j

/-- Complexification of the periodic limiting Gram matrix. -/
def complexPeriodicGramMatrix {index : Type*} (period : ℕ)
    (camera : index → ℕ) : Matrix index index ℂ :=
  fun i j => (periodicGramMatrix period camera i j : ℂ)

/-- The concrete normalized finite matrix product converges to the
complexified periodic Gram matrix. -/
theorem tendsto_normalizedFiniteDirectCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff => normalizedFiniteDirectCovariance z cutoff camera)
      atTop (nhds (complexPeriodicGramMatrix period camera)) := by
  change Tendsto
    (fun cutoff i j => normalizedFiniteDirectCovariance z cutoff camera i j)
    atTop (nhds fun i j => (periodicGramMatrix period camera i j : ℂ))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hreal := tendsto_resolvent_finiteCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j
  have hcomplex := (Complex.continuous_ofReal.tendsto
    (periodicGramMatrix period camera i j)).comp hreal
  apply hcomplex.congr'
  filter_upwards with cutoff
  have hexact := normalizedFiniteDirectCovariance_eq_finiteCoefficientCovariance
    hcamera z cutoff
  exact (congr_fun (congr_fun hexact i) j).symm

/-- Uniform finite-matrix norm convergence of the concrete normalized matrix
product. -/
theorem tendsto_norm_normalizedFiniteDirectCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteDirectCovariance z cutoff camera -
        complexPeriodicGramMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_normalizedFiniteDirectCovariance
    hz hperiod hcamera hcommon
  have hconstant : Tendsto (fun _ : ℕ => complexPeriodicGramMatrix period camera)
      atTop (nhds (complexPeriodicGramMatrix period camera)) := tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Every cutoff-indexed family of finite colligations satisfying the exact
Poisson and Pythagorean identities inherits the concrete covariance limit. -/
theorem tendsto_normalizedFiniteReturnMetricCovariance
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (endpointMap : ∀ cutoff,
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (bulkMap : ∀ cutoff,
      Matrix bulk (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : ℕ → Matrix bulk endpoint ℂ)
    (hpoisson : ∀ cutoff, poisson cutoff * endpointMap cutoff = bulkMap cutoff)
    (hisometry : ∀ cutoff,
      (endpointMap cutoff)ᴴ * endpointMap cutoff +
        (bulkMap cutoff)ᴴ * bulkMap cutoff = 1) :
    Tendsto (fun cutoff =>
      normalizedFiniteReturnMetricCovariance z cutoff camera
        (endpointMap cutoff) (poisson cutoff))
      atTop (nhds (complexPeriodicGramMatrix period camera)) := by
  have hdirect := tendsto_normalizedFiniteDirectCovariance
    hz hperiod hcamera hcommon
  apply hdirect.congr'
  filter_upwards with cutoff
  have hdirectExact :=
    normalizedFiniteDirectCovariance_eq_finiteCoefficientCovariance
      hcamera z cutoff
  have hreturnExact :=
    normalizedFiniteReturnMetricCovariance_eq_finiteCoefficientCovariance
      hcamera z cutoff (endpointMap cutoff) (bulkMap cutoff) (poisson cutoff)
      (hpoisson cutoff) (hisometry cutoff)
  exact hdirectExact.trans hreturnExact.symm

/-- Uniform matrix-norm form of the return-metric covariance limit. -/
theorem tendsto_norm_normalizedFiniteReturnMetricCovariance_sub
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (endpointMap : ∀ cutoff,
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (bulkMap : ∀ cutoff,
      Matrix bulk (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : ℕ → Matrix bulk endpoint ℂ)
    (hpoisson : ∀ cutoff, poisson cutoff * endpointMap cutoff = bulkMap cutoff)
    (hisometry : ∀ cutoff,
      (endpointMap cutoff)ᴴ * endpointMap cutoff +
        (bulkMap cutoff)ᴴ * bulkMap cutoff = 1) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteReturnMetricCovariance z cutoff camera
          (endpointMap cutoff) (poisson cutoff) -
        complexPeriodicGramMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_normalizedFiniteReturnMetricCovariance
    hz hperiod hcamera hcommon endpointMap bulkMap poisson hpoisson hisometry
  have hconstant : Tendsto (fun _ : ℕ => complexPeriodicGramMatrix period camera)
      atTop (nhds (complexPeriodicGramMatrix period camera)) := tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Uniform finite-matrix norm convergence of the complete literal camera
coefficients. -/
theorem tendsto_norm_resolvent_finiteCoefficientCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖finiteCoefficientCovariance (resolventWeight z) cutoff camera -
        periodicGramMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_resolvent_finiteCoefficientCovariance
    hz hperiod hcamera hcommon
  have hconstant : Tendsto (fun _ : ℕ => periodicGramMatrix period camera)
      atTop (nhds (periodicGramMatrix period camera)) := tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Exact six-camera specialization of the literal finite defect covariance. -/
theorem tendsto_norm_sixCamera_resolvent_finiteCoefficientCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖finiteCoefficientCovariance (resolventWeight z) cutoff sixCamera -
        sixCameraGram‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [sixCameraGram_eq] using
    (tendsto_norm_resolvent_finiteCoefficientCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Complex form of the exact six-camera Gram target. -/
def complexSixCameraGram : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (sixCameraGram i j : ℂ)

@[simp] theorem complexPeriodicGramMatrix_sixCamera :
    complexPeriodicGramMatrix 420 sixCamera = complexSixCameraGram := by
  unfold complexPeriodicGramMatrix complexSixCameraGram
  rw [sixCameraGram_eq]

/-- The literal six-camera matrix and finite diagonal resolvent converge in
matrix norm to the exact six-camera Gram. -/
theorem tendsto_norm_sixCamera_normalizedFiniteDirectCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteDirectCovariance z cutoff sixCamera -
        complexSixCameraGram‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexPeriodicGramMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteDirectCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Exact passage to the six-camera limit for any finite colligation family
satisfying `P_M E_M = B_M` and `E_Mᴴ E_M + B_Mᴴ B_M = I`. -/
theorem tendsto_norm_sixCamera_normalizedFiniteReturnMetricCovariance_sub
    {endpoint bulk : Type*} [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint] {z : ℂ} (hz : z.im ≠ 0)
    (endpointMap : ∀ cutoff,
      Matrix endpoint (Fin (finiteFamilyWindow cutoff sixCamera)) ℂ)
    (bulkMap : ∀ cutoff,
      Matrix bulk (Fin (finiteFamilyWindow cutoff sixCamera)) ℂ)
    (poisson : ℕ → Matrix bulk endpoint ℂ)
    (hpoisson : ∀ cutoff, poisson cutoff * endpointMap cutoff = bulkMap cutoff)
    (hisometry : ∀ cutoff,
      (endpointMap cutoff)ᴴ * endpointMap cutoff +
        (bulkMap cutoff)ᴴ * bulkMap cutoff = 1) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteReturnMetricCovariance z cutoff sixCamera
          (endpointMap cutoff) (poisson cutoff) -
        complexSixCameraGram‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexPeriodicGramMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteReturnMetricCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod endpointMap bulkMap poisson hpoisson hisometry)

end

end NativeCarrySpectralWeyl.Limits
