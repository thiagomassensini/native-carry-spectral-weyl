import NativeCarrySpectralWeyl.Finite.Gram
import NativeCarrySpectralWeyl.Limits.PeriodicMean
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The countable all-bases Gram kernel

This file begins the passage from a fixed finite camera family to the
countable family of every native camera `b >= 2`.  The periodic product mean
of two cameras is computed over the least common multiple of their slopes;
the result is independent of every larger common period.  The corresponding
slope-weighted kernel therefore restricts to the previously constructed
finite Gram matrix on every finite support.

The eventual camera Hilbert space is not the standard unweighted `l2` space.
Its algebraic core is the finitely supported space equipped with the Gram
form defined below.
-/

open scoped BigOperators Matrix

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits

/-- The countable type of all supported native cameras. -/
abbrev CameraIndex := {camera : ℕ // 2 ≤ camera}

/-- The natural-number label of an all-bases camera. -/
def cameraLabel (camera : CameraIndex) : ℕ := camera.1

/-- Every supported camera slope is positive. -/
theorem cameraSlope_pos (camera : CameraIndex) : 0 < cameraSlope (cameraLabel camera) := by
  simp only [cameraLabel]
  by_cases htwo : (camera : ℕ) = 2
  · simp [htwo]
  · rw [cameraSlope_of_ne_two htwo]
    omega

/-- Every supported camera slope is at least two. -/
theorem two_le_cameraSlope (camera : CameraIndex) :
    2 ≤ cameraSlope (cameraLabel camera) := by
  simp only [cameraLabel]
  by_cases htwo : (camera : ℕ) = 2
  · simp [htwo]
  · rw [cameraSlope_of_ne_two htwo]
    exact camera.property

/-- Slope four is the sole duplicated slope: it belongs exactly to cameras
two and four. -/
theorem cameraSlope_eq_four_iff (camera : CameraIndex) :
    cameraSlope (cameraLabel camera) = 4 ↔
      cameraLabel camera = 2 ∨ cameraLabel camera = 4 := by
  constructor
  · intro hslope
    by_cases htwo : cameraLabel camera = 2
    · exact Or.inl htwo
    · exact Or.inr (by simpa [cameraSlope_of_ne_two htwo] using hslope)
  · rintro (htwo | hfour)
    · simp [htwo]
    · simp [hfour]

/-- Away from the exceptional slope four, a slope determines its camera. -/
theorem camera_eq_of_slope_eq_of_ne_four {camera₁ camera₂ : CameraIndex}
    (hslope : cameraSlope (cameraLabel camera₁) =
      cameraSlope (cameraLabel camera₂))
    (hne : cameraSlope (cameraLabel camera₁) ≠ 4) :
    camera₁ = camera₂ := by
  have hne₁ : cameraLabel camera₁ ≠ 2 := by
    intro htwo
    apply hne
    simp [htwo]
  have hne₂ : cameraLabel camera₂ ≠ 2 := by
    intro htwo
    apply hne
    rw [hslope]
    simp [htwo]
  apply Subtype.ext
  change (camera₁ : ℕ) = (camera₂ : ℕ)
  change cameraSlope (camera₁ : ℕ) = cameraSlope (camera₂ : ℕ) at hslope
  rw [cameraSlope_of_ne_two (by simpa [cameraLabel] using hne₁),
    cameraSlope_of_ne_two (by simpa [cameraLabel] using hne₂)] at hslope
  exact hslope

/-- Every supported profile is nonzero at residue zero. -/
theorem profile_zero_ne_zero (camera : CameraIndex) :
    profile (cameraLabel camera) 0 ≠ 0 := by
  have hcamera : 2 ≤ cameraLabel camera := camera.property
  by_cases htwo : cameraLabel camera = 2
  · rw [htwo]
    norm_num [profile, c2Profile, dvdIndicator]
  · rcases Nat.even_or_odd (cameraLabel camera) with heven | hodd
    · rw [profile_of_even htwo heven]
      simp only [evenProfile, dvdIndicator, dvd_zero, if_true]
      push_cast
      omega
    · rw [profile_of_odd htwo hodd]
      simp only [oddProfile, dvdIndicator, dvd_zero, if_true]
      omega

/-- At residue two the aligned C2 profile vanishes. -/
@[simp] theorem profile_two_at_two : profile 2 2 = 0 := by
  norm_num [profile, c2Profile, dvdIndicator]

/-- At residue two the C4 profile has value two. -/
@[simp] theorem profile_four_at_two : profile 4 2 = 2 := by
  norm_num [profile, evenProfile, dvdIndicator]

/-- Canonical joint period of a pair of native cameras. -/
def pairPeriod (camera₁ camera₂ : CameraIndex) : ℕ :=
  Nat.lcm (cameraSlope (cameraLabel camera₁))
    (cameraSlope (cameraLabel camera₂))

/-- A pair period is positive. -/
theorem pairPeriod_pos (camera₁ camera₂ : CameraIndex) :
    0 < pairPeriod camera₁ camera₂ := by
  exact Nat.lcm_pos (cameraSlope_pos camera₁) (cameraSlope_pos camera₂)

/-- The first camera slope divides the canonical pair period. -/
theorem cameraSlope_dvd_pairPeriod_left (camera₁ camera₂ : CameraIndex) :
    cameraSlope (cameraLabel camera₁) ∣ pairPeriod camera₁ camera₂ :=
  Nat.dvd_lcm_left _ _

/-- The second camera slope divides the canonical pair period. -/
theorem cameraSlope_dvd_pairPeriod_right (camera₁ camera₂ : CameraIndex) :
    cameraSlope (cameraLabel camera₂) ∣ pairPeriod camera₁ camera₂ :=
  Nat.dvd_lcm_right _ _

/-- The product of two supported profiles is periodic with the pair period. -/
theorem profileProduct_periodic (camera₁ camera₂ : CameraIndex) :
    Function.Periodic
      (fun residue =>
        profile (cameraLabel camera₁) residue *
          profile (cameraLabel camera₂) residue)
      (pairPeriod camera₁ camera₂) := by
  intro residue
  change
    profile (cameraLabel camera₁) (residue + pairPeriod camera₁ camera₂) *
        profile (cameraLabel camera₂) (residue + pairPeriod camera₁ camera₂) =
      profile (cameraLabel camera₁) residue * profile (cameraLabel camera₂) residue
  exact congrArg₂ (· * ·)
    (profile_add_commonPeriod camera₁.property
      (cameraSlope_dvd_pairPeriod_left camera₁ camera₂) residue)
    (profile_add_commonPeriod camera₂.property
      (cameraSlope_dvd_pairPeriod_right camera₁ camera₂) residue)

/-- Repeating a pair period repeats its unnormalized profile-product sum. -/
theorem periodicProductSum_mul_pairPeriod (camera₁ camera₂ : CameraIndex)
    (blocks : ℕ) :
    periodicProductSum (blocks * pairPeriod camera₁ camera₂)
        (cameraLabel camera₁) (cameraLabel camera₂) =
      (blocks : ℤ) * periodicProductSum (pairPeriod camera₁ camera₂)
        (cameraLabel camera₁) (cameraLabel camera₂) := by
  simpa [periodicProductSum, nsmul_eq_mul] using
    (sum_range_mul_period (profileProduct_periodic camera₁ camera₂) blocks)

/-- Normalized profile-product means do not change when a positive number of
complete pair periods is used. -/
theorem periodicProductMean_mul_pairPeriod (camera₁ camera₂ : CameraIndex)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    periodicProductMean (blocks * pairPeriod camera₁ camera₂)
        (cameraLabel camera₁) (cameraLabel camera₂) =
      periodicProductMean (pairPeriod camera₁ camera₂)
        (cameraLabel camera₁) (cameraLabel camera₂) := by
  rw [periodicProductMean, periodicProductMean,
    periodicProductSum_mul_pairPeriod]
  push_cast
  field_simp [hblocks.ne', (pairPeriod_pos camera₁ camera₂).ne']

/-- The pair-period mean agrees with the mean over every positive common
multiple of the pair period. -/
theorem periodicProductMean_eq_pairPeriod (camera₁ camera₂ : CameraIndex)
    {period : ℕ} (hperiod : pairPeriod camera₁ camera₂ ∣ period)
    (hperiod_pos : 0 < period) :
    periodicProductMean period (cameraLabel camera₁) (cameraLabel camera₂) =
      periodicProductMean (pairPeriod camera₁ camera₂)
        (cameraLabel camera₁) (cameraLabel camera₂) := by
  obtain ⟨blocks, rfl⟩ := hperiod
  have hblocks : 0 < blocks := by
    apply Nat.pos_of_ne_zero
    intro hzero
    subst blocks
    simp at hperiod_pos
  rw [Nat.mul_comm]
  exact periodicProductMean_mul_pairPeriod camera₁ camera₂ hblocks

/-- Canonical all-bases periodic product-mean kernel. -/
def periodicMeanKernel (camera₁ camera₂ : CameraIndex) : ℝ :=
  periodicProductMean (pairPeriod camera₁ camera₂)
    (cameraLabel camera₁) (cameraLabel camera₂)

/-- Canonical all-bases slope-weighted Gram kernel. -/
def gramKernel (camera₁ camera₂ : CameraIndex) : ℝ :=
  (min (cameraSlope (cameraLabel camera₁))
      (cameraSlope (cameraLabel camera₂)) : ℕ) *
    periodicMeanKernel camera₁ camera₂

/-- The pair period is symmetric. -/
theorem pairPeriod_comm (camera₁ camera₂ : CameraIndex) :
    pairPeriod camera₁ camera₂ = pairPeriod camera₂ camera₁ := by
  simp [pairPeriod, Nat.lcm_comm]

/-- The canonical periodic mean kernel is symmetric. -/
theorem periodicMeanKernel_comm (camera₁ camera₂ : CameraIndex) :
    periodicMeanKernel camera₁ camera₂ = periodicMeanKernel camera₂ camera₁ := by
  simp only [periodicMeanKernel, periodicProductMean, periodicProductSum]
  rw [pairPeriod_comm]
  congr 1
  norm_cast
  apply Finset.sum_congr rfl
  intro residue _
  ring

/-- The two cameras sharing slope four, ordered as C2 and C4. -/
def slopeFourCamera : Fin 2 → CameraIndex :=
  ![⟨2, by omega⟩, ⟨4, by omega⟩]

/-- Periodic-mean block carried by the two slope-four cameras. -/
def slopeFourPeriodicMeanMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => periodicMeanKernel (slopeFourCamera i) (slopeFourCamera j)

/-- Exact research-note certificate for the exceptional C2/C4 block. -/
theorem slopeFourPeriodicMeanMatrix_eq :
    slopeFourPeriodicMeanMatrix = !![3 / 2, 5 / 2; 5 / 2, 11 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [slopeFourPeriodicMeanMatrix, slopeFourCamera,
      periodicMeanKernel, pairPeriod, periodicProductMean,
      periodicProductSum, cameraLabel, cameraSlope, profile, c2Profile,
      evenProfile, dvdIndicator, Finset.sum_range_succ]

/-- The exceptional C2/C4 periodic-mean block has determinant exactly two. -/
theorem slopeFourPeriodicMeanMatrix_det :
    slopeFourPeriodicMeanMatrix.det = 2 := by
  rw [slopeFourPeriodicMeanMatrix_eq]
  norm_num [Matrix.det_fin_two]

/-- The exceptional block is the ordinary period-four profile-mean matrix. -/
theorem slopeFourPeriodicMeanMatrix_eq_periodicMeanMatrix :
    slopeFourPeriodicMeanMatrix =
      periodicMeanMatrix 4 (fun i => cameraLabel (slopeFourCamera i)) := by
  ext i j
  rw [periodicMeanMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [slopeFourPeriodicMeanMatrix, periodicMeanKernel,
      slopeFourCamera, pairPeriod, cameraLabel, cameraSlope]

/-- The exceptional C2/C4 periodic-mean block is positive semidefinite by its
rank-one periodic realization. -/
theorem slopeFourPeriodicMeanMatrix_posSemidef :
    slopeFourPeriodicMeanMatrix.PosSemidef := by
  rw [slopeFourPeriodicMeanMatrix_eq_periodicMeanMatrix]
  exact periodicMeanMatrix_posSemidef 4 _

/-- The exceptional C2/C4 periodic-mean block is positive definite. -/
theorem slopeFourPeriodicMeanMatrix_posDef :
    slopeFourPeriodicMeanMatrix.PosDef := by
  rw [slopeFourPeriodicMeanMatrix_posSemidef.posDef_iff_det_ne_zero,
    slopeFourPeriodicMeanMatrix_det]
  norm_num

/-- The all-bases Gram kernel is symmetric. -/
theorem gramKernel_comm (camera₁ camera₂ : CameraIndex) :
    gramKernel camera₁ camera₂ = gramKernel camera₂ camera₁ := by
  rw [gramKernel, gramKernel, periodicMeanKernel_comm]
  simp [min_comm]

/-- A finite set of cameras has a canonical positive common period: the
product of all slopes in the set. -/
def finiteSupportPeriod (support : Finset CameraIndex) : ℕ :=
  ∏ camera ∈ support, cameraSlope (cameraLabel camera)

/-- The canonical period of every finite camera set is positive, including
the empty set (whose period is one). -/
theorem finiteSupportPeriod_pos (support : Finset CameraIndex) :
    0 < finiteSupportPeriod support := by
  apply Finset.prod_pos
  intro camera hcamera
  exact cameraSlope_pos camera

/-- Every slope represented in a finite camera set divides its canonical
common period. -/
theorem cameraSlope_dvd_finiteSupportPeriod {support : Finset CameraIndex}
    {camera : CameraIndex} (hcamera : camera ∈ support) :
    cameraSlope (cameraLabel camera) ∣ finiteSupportPeriod support := by
  exact Finset.dvd_prod_of_mem (fun c => cameraSlope (cameraLabel c)) hcamera

/-- Every pair drawn from a finite camera set has pair period dividing the
set's canonical common period. -/
theorem pairPeriod_dvd_finiteSupportPeriod {support : Finset CameraIndex}
    {camera₁ camera₂ : CameraIndex} (hcamera₁ : camera₁ ∈ support)
    (hcamera₂ : camera₂ ∈ support) :
    pairPeriod camera₁ camera₂ ∣ finiteSupportPeriod support := by
  exact Nat.lcm_dvd
    (cameraSlope_dvd_finiteSupportPeriod hcamera₁)
    (cameraSlope_dvd_finiteSupportPeriod hcamera₂)

/-- On a finite camera set, the canonical kernel can be evaluated using the
single common period attached to that set. -/
theorem gramKernel_eq_commonPeriod {support : Finset CameraIndex}
    {camera₁ camera₂ : CameraIndex} (hcamera₁ : camera₁ ∈ support)
    (hcamera₂ : camera₂ ∈ support) :
    gramKernel camera₁ camera₂ =
      (min (cameraSlope (cameraLabel camera₁))
          (cameraSlope (cameraLabel camera₂)) : ℕ) *
        periodicProductMean (finiteSupportPeriod support)
          (cameraLabel camera₁) (cameraLabel camera₂) := by
  rw [gramKernel, periodicMeanKernel,
    periodicProductMean_eq_pairPeriod camera₁ camera₂
      (pairPeriod_dvd_finiteSupportPeriod hcamera₁ hcamera₂)
      (finiteSupportPeriod_pos support)]

/-- Principal finite restriction of the all-bases Gram kernel. -/
def finiteGramMatrix (support : Finset CameraIndex) :
    Matrix support support ℝ :=
  fun camera₁ camera₂ => gramKernel camera₁.1 camera₂.1

/-- The principal finite restriction is exactly the previously defined
finite periodic Gram matrix over the canonical common period. -/
theorem finiteGramMatrix_eq_periodicGramMatrix (support : Finset CameraIndex) :
    finiteGramMatrix support =
      periodicGramMatrix (finiteSupportPeriod support)
        (fun camera : support => cameraLabel camera.1) := by
  ext camera₁ camera₂
  rw [finiteGramMatrix, periodicGramMatrix_apply,
    gramKernel_eq_commonPeriod camera₁.property camera₂.property]

/-- Every finite principal restriction of the all-bases kernel is positive
semidefinite. -/
theorem finiteGramMatrix_posSemidef (support : Finset CameraIndex) :
    (finiteGramMatrix support).PosSemidef := by
  rw [finiteGramMatrix_eq_periodicGramMatrix]
  exact periodicGramMatrix_posSemidef _ _

/-- Bilinear Gram form on finitely supported all-bases camera coefficients. -/
def gramForm (u v : CameraIndex →₀ ℝ) : ℝ :=
  u.sum fun camera₁ coefficient₁ =>
    v.sum fun camera₂ coefficient₂ =>
      coefficient₁ * gramKernel camera₁ camera₂ * coefficient₂

/-- Restriction of a finitely supported coefficient vector to the subtype of
its own support. -/
def supportCoefficients (u : CameraIndex →₀ ℝ) : u.support →₀ ℝ :=
  Finsupp.subtypeDomain (fun camera => camera ∈ u.support) u

/-- The all-bases Gram form is symmetric. -/
theorem gramForm_comm (u v : CameraIndex →₀ ℝ) :
    gramForm u v = gramForm v u := by
  classical
  simp only [gramForm, Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro camera₂ hcamera₂
  apply Finset.sum_congr rfl
  intro camera₁ hcamera₁
  rw [gramKernel_comm]
  ring

/-- The Gram form of a vector equals the `Finsupp` quadratic form of the
finite principal matrix on its support. -/
theorem gramForm_self_eq_finiteGramMatrix (u : CameraIndex →₀ ℝ) :
    gramForm u u =
      (supportCoefficients u).sum fun camera₁ coefficient₁ =>
        (supportCoefficients u).sum fun camera₂ coefficient₂ =>
          star coefficient₁ * finiteGramMatrix u.support camera₁ camera₂ *
            coefficient₂ := by
  classical
  simp [gramForm, supportCoefficients, finiteGramMatrix, Finsupp.sum,
    ← Finset.sum_attach u.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain]

/-- The all-bases Gram form is nonnegative on every finitely supported
coefficient vector. -/
theorem gramForm_nonneg (u : CameraIndex →₀ ℝ) : 0 ≤ gramForm u u := by
  rw [gramForm_self_eq_finiteGramMatrix]
  exact (finiteGramMatrix_posSemidef u.support).2 (supportCoefficients u)

/-- Sum of the slopes represented in a finite camera set.  This is a
convenient finite level bound for the minimum-kernel decomposition. -/
def finiteSlopeBound (support : Finset CameraIndex) : ℕ :=
  ∑ camera ∈ support, cameraSlope (cameraLabel camera)

/-- Every slope in a finite camera set lies below its total slope bound. -/
theorem cameraSlope_le_finiteSlopeBound {support : Finset CameraIndex}
    (camera : support) :
    cameraSlope (cameraLabel camera.1) ≤ finiteSlopeBound support := by
  exact Finset.single_le_sum
    (fun other _ => Nat.zero_le (cameraSlope (cameraLabel other)))
    camera.property

/-- Profile combination visible at a given slope level and residue. -/
def levelProfileCombination (support : Finset CameraIndex)
    (coefficient : support → ℝ) (level residue : ℕ) : ℝ :=
  ∑ camera : support,
    coefficient camera *
      (if level < cameraSlope (cameraLabel camera.1) then
        (profile (cameraLabel camera.1) residue : ℝ)
      else 0)

private theorem sum_four_comm {ι : Type*} [Fintype ι]
    (residues levels : Finset ℕ) (term : ι → ι → ℕ → ℕ → ℝ) :
    (∑ camera₁ : ι, ∑ camera₂ : ι,
      ∑ residue ∈ residues, ∑ level ∈ levels,
        term camera₁ camera₂ residue level) =
      ∑ level ∈ levels, ∑ residue ∈ residues,
        ∑ camera₁ : ι, ∑ camera₂ : ι,
          term camera₁ camera₂ residue level := by
  classical
  calc
    _ = ∑ camera₁ : ι, ∑ camera₂ : ι,
        ∑ level ∈ levels, ∑ residue ∈ residues,
          term camera₁ camera₂ residue level := by
      apply Fintype.sum_congr
      intro camera₁
      apply Fintype.sum_congr
      intro camera₂
      exact Finset.sum_comm
    _ = ∑ camera₁ : ι, ∑ level ∈ levels,
        ∑ camera₂ : ι, ∑ residue ∈ residues,
          term camera₁ camera₂ residue level := by
      apply Fintype.sum_congr
      intro camera₁
      exact Finset.sum_comm
    _ = ∑ level ∈ levels, ∑ camera₁ : ι,
        ∑ camera₂ : ι, ∑ residue ∈ residues,
          term camera₁ camera₂ residue level := Finset.sum_comm
    _ = ∑ level ∈ levels, ∑ camera₁ : ι,
        ∑ residue ∈ residues, ∑ camera₂ : ι,
          term camera₁ camera₂ residue level := by
      apply Finset.sum_congr rfl
      intro level hlevel
      apply Fintype.sum_congr
      intro camera₁
      exact Finset.sum_comm
    _ = ∑ level ∈ levels, ∑ residue ∈ residues,
        ∑ camera₁ : ι, ∑ camera₂ : ι,
          term camera₁ camera₂ residue level := by
      apply Finset.sum_congr rfl
      intro level hlevel
      exact Finset.sum_comm

/-- Exact sum-of-squares realization of every finite principal all-bases Gram
quadratic form.  It simultaneously realizes the periodic profile mean and the
level decomposition of `min(ell_b, ell_c)`. -/
theorem finiteGramMatrix_quadratic_eq_sum_sq (support : Finset CameraIndex)
    (coefficient : support → ℝ) :
    star coefficient ⬝ᵥ (finiteGramMatrix support *ᵥ coefficient) =
      (finiteSupportPeriod support : ℝ)⁻¹ *
        ∑ level ∈ Finset.range (finiteSlopeBound support),
          ∑ residue ∈ Finset.range (finiteSupportPeriod support),
            (levelProfileCombination support coefficient level residue) ^ 2 := by
  rw [finiteGramMatrix_eq_periodicGramMatrix]
  simp only [dotProduct, Matrix.mulVec, star_trivial, periodicGramMatrix_apply,
    periodicProductMean, periodicProductSum, Int.cast_sum, Int.cast_mul]
  have hmin (camera₁ camera₂ : support) :
      (min (cameraSlope (cameraLabel camera₁.1))
          (cameraSlope (cameraLabel camera₂.1)) : ℕ) =
        ∑ level ∈ Finset.range (finiteSlopeBound support),
          (if level < cameraSlope (cameraLabel camera₁.1) then (1 : ℝ) else 0) *
            (if level < cameraSlope (cameraLabel camera₂.1) then 1 else 0) := by
    exact (sum_indicator_eq_min
      (cameraSlope_le_finiteSlopeBound camera₁)).symm
  simp_rw [hmin]
  simp only [levelProfileCombination, pow_two]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro level hlevel
  apply Finset.sum_congr rfl
  intro residue hresidue
  apply Fintype.sum_congr
  intro camera₁
  apply Fintype.sum_congr
  intro camera₂
  by_cases hcamera₁ : level < cameraSlope (cameraLabel camera₁.1) <;>
    by_cases hcamera₂ : level < cameraSlope (cameraLabel camera₂.1) <;>
      simp [hcamera₁, hcamera₂]
  all_goals ring

/-- A nonzero coefficient family on a finite camera set has a nonzero entry
whose slope is maximal among all nonzero entries. -/
theorem exists_maximal_nonzero_slope {support : Finset CameraIndex}
    {coefficient : support → ℝ} (hne : coefficient ≠ 0) :
    ∃ cameraMax : support,
      coefficient cameraMax ≠ 0 ∧
        ∀ camera : support, coefficient camera ≠ 0 →
          cameraSlope (cameraLabel camera.1) ≤
            cameraSlope (cameraLabel cameraMax.1) := by
  classical
  let active : Finset support := Finset.univ.filter fun camera => coefficient camera ≠ 0
  have hactive : active.Nonempty := by
    by_contra hempty
    apply hne
    funext camera
    have hnot : camera ∉ active := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simpa [active] using hnot
  obtain ⟨cameraMax, hcameraMax, hmax⟩ :=
    Finset.exists_max_image active
      (fun camera => cameraSlope (cameraLabel camera.1)) hactive
  refine ⟨cameraMax, ?_, ?_⟩
  · simpa [active] using hcameraMax
  · intro camera hcamera
    exact hmax camera (by simp [active, hcamera])

/-- At a nonexceptional maximal slope, the top level contains exactly one
nonzero camera coefficient, hence its residue-zero profile combination cannot
vanish. -/
theorem levelProfileCombination_max_ne_zero_of_slope_ne_four
    {support : Finset CameraIndex} {coefficient : support → ℝ}
    {cameraMax : support} (hcameraMax : coefficient cameraMax ≠ 0)
    (hmax : ∀ camera : support, coefficient camera ≠ 0 →
      cameraSlope (cameraLabel camera.1) ≤
        cameraSlope (cameraLabel cameraMax.1))
    (hneFour : cameraSlope (cameraLabel cameraMax.1) ≠ 4) :
    levelProfileCombination support coefficient
      (cameraSlope (cameraLabel cameraMax.1) - 1) 0 ≠ 0 := by
  classical
  rw [levelProfileCombination, Fintype.sum_eq_single cameraMax]
  · have hslopePos := cameraSlope_pos cameraMax.1
    simp only [Nat.sub_lt_iff_lt_add hslopePos, lt_add_iff_pos_right,
      Nat.lt_one_iff, if_true]
    exact mul_ne_zero hcameraMax
      (Int.cast_ne_zero.mpr (profile_zero_ne_zero cameraMax.1))
  · intro camera hneCamera
    by_cases hcoefficient : coefficient camera = 0
    · simp [hcoefficient]
    · have hslopeLe := hmax camera hcoefficient
      have hnotLevel :
          ¬cameraSlope (cameraLabel cameraMax.1) - 1 <
            cameraSlope (cameraLabel camera.1) := by
        intro hlevel
        have hslopeEq :
            cameraSlope (cameraLabel cameraMax.1) =
              cameraSlope (cameraLabel camera.1) := by
          omega
        apply hneCamera
        apply Subtype.ext
        exact (camera_eq_of_slope_eq_of_ne_four hslopeEq hneFour).symm
      simp [hnotLevel]

/-- At the exceptional maximal slope four, residues zero and two separate the
C2 and C4 cameras.  At least one of the two top-level combinations is
nonzero. -/
theorem levelProfileCombination_max_ne_zero_of_slope_four
    {support : Finset CameraIndex} {coefficient : support → ℝ}
    {cameraMax : support} (hcameraMax : coefficient cameraMax ≠ 0)
    (hmax : ∀ camera : support, coefficient camera ≠ 0 →
      cameraSlope (cameraLabel camera.1) ≤
        cameraSlope (cameraLabel cameraMax.1))
    (hslopeFour : cameraSlope (cameraLabel cameraMax.1) = 4) :
    levelProfileCombination support coefficient 3 0 ≠ 0 ∨
      levelProfileCombination support coefficient 3 2 ≠ 0 := by
  classical
  by_cases hactiveFour : ∃ cameraFour : support,
      cameraLabel cameraFour.1 = 4 ∧ coefficient cameraFour ≠ 0
  · right
    obtain ⟨cameraFour, hlabelFour, hcameraFour⟩ := hactiveFour
    rw [levelProfileCombination, Fintype.sum_eq_single cameraFour]
    · simp [hlabelFour, hcameraFour]
    · intro camera hneCamera
      by_cases hcoefficient : coefficient camera = 0
      · simp [hcoefficient]
      · have hslopeLe : cameraSlope (cameraLabel camera.1) ≤ 4 := by
          simpa [hslopeFour] using hmax camera hcoefficient
        by_cases hlevel : 3 < cameraSlope (cameraLabel camera.1)
        · have hslope : cameraSlope (cameraLabel camera.1) = 4 := by omega
          rcases (cameraSlope_eq_four_iff camera.1).mp hslope with hlabelTwo | hlabelFour'
          · have hprofile : profile (cameraLabel camera.1) 2 = 0 := by
              rw [hlabelTwo]
              exact profile_two_at_two
            simp [hlevel, hprofile]
          · exfalso
            apply hneCamera
            apply Subtype.ext
            apply Subtype.ext
            simpa [cameraLabel] using hlabelFour'.trans hlabelFour.symm
        · simp [hlevel]
  · left
    have hlabelMax : cameraLabel cameraMax.1 = 2 := by
      rcases (cameraSlope_eq_four_iff cameraMax.1).mp hslopeFour with htwo | hfour
      · exact htwo
      · exact False.elim (hactiveFour ⟨cameraMax, hfour, hcameraMax⟩)
    rw [levelProfileCombination, Fintype.sum_eq_single cameraMax]
    · have hlevel : 3 < cameraSlope (cameraLabel cameraMax.1) := by
        omega
      simp only [hlevel, if_true]
      exact mul_ne_zero hcameraMax
        (Int.cast_ne_zero.mpr (profile_zero_ne_zero cameraMax.1))
    · intro camera hneCamera
      by_cases hcoefficient : coefficient camera = 0
      · simp [hcoefficient]
      · have hslopeLe : cameraSlope (cameraLabel camera.1) ≤ 4 := by
          simpa [hslopeFour] using hmax camera hcoefficient
        by_cases hlevel : 3 < cameraSlope (cameraLabel camera.1)
        · have hslope : cameraSlope (cameraLabel camera.1) = 4 := by omega
          rcases (cameraSlope_eq_four_iff camera.1).mp hslope with hlabelTwo | hlabelFour
          · exfalso
            apply hneCamera
            apply Subtype.ext
            apply Subtype.ext
            simpa [cameraLabel] using hlabelTwo.trans hlabelMax.symm
          · exact False.elim (hactiveFour ⟨camera, hlabelFour, hcoefficient⟩)
        · simp [hlevel]

/-- Every finite principal restriction of the all-bases kernel is strictly
positive definite.  The proof uses the maximal nonzero slope and handles the
sole duplicate slope `4` by the C2/C4 residue separation above. -/
theorem finiteGramMatrix_posDef (support : Finset CameraIndex) :
    (finiteGramMatrix support).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(finiteGramMatrix_posSemidef support).isHermitian, ?_⟩
  intro coefficient hcoefficient
  rw [finiteGramMatrix_quadratic_eq_sum_sq]
  apply mul_pos
  · exact inv_pos.mpr (Nat.cast_pos.mpr (finiteSupportPeriod_pos support))
  · refine Finset.sum_pos'
      (fun level _ => Finset.sum_nonneg fun residue _ => sq_nonneg
        (levelProfileCombination support coefficient level residue)) ?_
    obtain ⟨cameraMax, hcameraMax, hmax⟩ :=
      exists_maximal_nonzero_slope hcoefficient
    have hslopeLe := cameraSlope_le_finiteSlopeBound cameraMax
    by_cases hslopeFour : cameraSlope (cameraLabel cameraMax.1) = 4
    · have hlevel : 3 ∈ Finset.range (finiteSlopeBound support) := by
        simp only [Finset.mem_range]
        omega
      refine ⟨3, hlevel, ?_⟩
      refine Finset.sum_pos'
        (fun residue _ => sq_nonneg
          (levelProfileCombination support coefficient 3 residue)) ?_
      rcases levelProfileCombination_max_ne_zero_of_slope_four
          hcameraMax hmax hslopeFour with hzero | htwo
      · exact ⟨0, Finset.mem_range.mpr (finiteSupportPeriod_pos support),
          sq_pos_of_ne_zero hzero⟩
      · have hperiodGe : 4 ≤ finiteSupportPeriod support := by
          exact Nat.le_of_dvd (finiteSupportPeriod_pos support)
            (by simpa [hslopeFour] using
              (cameraSlope_dvd_finiteSupportPeriod cameraMax.property))
        exact ⟨2, Finset.mem_range.mpr (by omega), sq_pos_of_ne_zero htwo⟩
    · have hslopePos := cameraSlope_pos cameraMax.1
      have hlevel :
          cameraSlope (cameraLabel cameraMax.1) - 1 ∈
            Finset.range (finiteSlopeBound support) := by
        simp only [Finset.mem_range]
        omega
      refine ⟨cameraSlope (cameraLabel cameraMax.1) - 1, hlevel, ?_⟩
      refine Finset.sum_pos'
        (fun residue _ => sq_nonneg
          (levelProfileCombination support coefficient
            (cameraSlope (cameraLabel cameraMax.1) - 1) residue)) ?_
      exact ⟨0, Finset.mem_range.mpr (finiteSupportPeriod_pos support),
        sq_pos_of_ne_zero
          (levelProfileCombination_max_ne_zero_of_slope_ne_four
            hcameraMax hmax hslopeFour)⟩

/-- The all-bases Gram form is strictly positive on every nonzero finitely
supported coefficient vector. -/
theorem gramForm_pos {u : CameraIndex →₀ ℝ} (hu : u ≠ 0) :
    0 < gramForm u u := by
  rw [gramForm_self_eq_finiteGramMatrix]
  apply (finiteGramMatrix_posDef u.support).2
  intro hzero
  apply hu
  ext camera
  by_cases hcamera : camera ∈ u.support
  · have := DFunLike.congr_fun hzero (⟨camera, hcamera⟩ : u.support)
    simpa [supportCoefficients] using this
  · exact Finsupp.notMem_support_iff.mp hcamera

end NativeCarrySpectralWeyl.Infinite
