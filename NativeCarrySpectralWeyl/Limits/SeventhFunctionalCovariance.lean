import NativeCarrySpectralWeyl.Limits.SexticFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarSeventhFunctionalMoment
import Mathlib.Tactic

/-!
# Seventh functional covariance limit

This file connects the seventh scalar resolvent functional moment to the
periodic camera coefficients.  The leading periodic weight
`log(n+1)⁷ w_z(n)` grows like `log(n)⁵`.  It is eventually monotone because it
is the product of the nonnegative monotone logarithm with the eventually
monotone log-sixth weight.  Discrete Abel summation then controls the zero-mean
periodic residue.  The literal boundary is eliminated afterward, yielding
the complete coefficient, direct and compatible return-metric limits.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- Seventh centered logarithmic moment weight. -/
def seventhCenteredMomentWeight (slope : ℕ) : ℝ :=
  Real.log slope ^ 7 + 21 * Real.log slope ^ 5 -
    70 * Real.log slope ^ 4 + 315 * Real.log slope ^ 3 -
      924 * Real.log slope ^ 2 + 1855 * Real.log slope - 1854

/-- Seventh centered logarithmic camera moment. -/
def seventhCenteredMomentMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  weightedMomentMatrix period camera seventhCenteredMomentWeight

/-- Source formula
`M₇(i,j) = G(i,j) * (log(ell(i,j))⁷ + 21log(ell(i,j))⁵ -
70log(ell(i,j))⁴ + 315log(ell(i,j))³ - 924log(ell(i,j))² +
1855log(ell(i,j)) - 1854)`. -/
theorem seventhCenteredMomentMatrix_apply {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    seventhCenteredMomentMatrix period camera i j =
      periodicGramMatrix period camera i j *
        (Real.log (slopeOverlap camera i j) ^ 7 +
          21 * Real.log (slopeOverlap camera i j) ^ 5 -
            70 * Real.log (slopeOverlap camera i j) ^ 4 +
              315 * Real.log (slopeOverlap camera i j) ^ 3 -
                924 * Real.log (slopeOverlap camera i j) ^ 2 +
                  1855 * Real.log (slopeOverlap camera i j) - 1854) := by
  rfl

/-- The seventh centered logarithmic camera moment is Hermitian. -/
theorem seventhCenteredMomentMatrix_isHermitian {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (seventhCenteredMomentMatrix period camera).IsHermitian :=
  weightedMomentMatrix_isHermitian period camera seventhCenteredMomentWeight

/-- The seventh centered logarithmic camera moment is self-adjoint. -/
theorem seventhCenteredMomentMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    IsSelfAdjoint (seventhCenteredMomentMatrix period camera) :=
  (seventhCenteredMomentMatrix_isHermitian period camera).isSelfAdjoint

/-- Literal seventh centered moment for cameras `2, ..., 7`. -/
def sixCameraSeventhCenteredMoment : Matrix (Fin 6) (Fin 6) ℝ :=
  !![6 * seventhCenteredMomentWeight 4, 0,
       10 * seventhCenteredMomentWeight 4, 0,
       (16 / 3) * seventhCenteredMomentWeight 4, 0;
     0, 6 * seventhCenteredMomentWeight 3, 0, 0,
       6 * seventhCenteredMomentWeight 3, 0;
     10 * seventhCenteredMomentWeight 4, 0,
       22 * seventhCenteredMomentWeight 4, 0,
       (16 / 3) * seventhCenteredMomentWeight 4, 0;
     0, 0, 0, 20 * seventhCenteredMomentWeight 5, 0, 0;
     (16 / 3) * seventhCenteredMomentWeight 4,
       6 * seventhCenteredMomentWeight 3,
       (16 / 3) * seventhCenteredMomentWeight 4, 0,
       44 * seventhCenteredMomentWeight 6, 0;
     0, 0, 0, 0, 0, 42 * seventhCenteredMomentWeight 7]

/-- Exact recovery of the seventh centered moment for cameras `2, ..., 7`. -/
theorem sixCameraSeventhCenteredMoment_eq :
    seventhCenteredMomentMatrix 420 sixCamera = sixCameraSeventhCenteredMoment := by
  rw [seventhCenteredMomentMatrix, weightedMomentMatrix, sixCameraGram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraSeventhCenteredMoment, slopeWeightMatrix,
      seventhCenteredMomentWeight, slopeOverlap, sixCamera, sixCameraGram,
      sixCameraGramRat, cameraSlope]

/-- The exact six-camera seventh centered moment is self-adjoint. -/
theorem sixCameraSeventhCenteredMoment_isSelfAdjoint :
    IsSelfAdjoint sixCameraSeventhCenteredMoment := by
  rw [← sixCameraSeventhCenteredMoment_eq]
  exact seventhCenteredMomentMatrix_isSelfAdjoint 420 sixCamera

/-- The log-seventh resolvent weight. -/
def resolventLogSeventhWeight (z : ℂ) (n : ℕ) : ℝ :=
  Real.log (n + 1) ^ 7 * resolventWeight z n

theorem resolventLogSeventhWeight_nonneg {z : ℂ} (hz : z.im ≠ 0)
    (n : ℕ) : 0 ≤ resolventLogSeventhWeight z n := by
  exact mul_nonneg (pow_nonneg (Real.log_nonneg (by norm_num)) 7)
    (resolventWeight_pos hz n).le

/-- The log-seventh resolvent weight is eventually monotone. -/
theorem exists_resolventLogSeventhWeight_monotone_natAdd
    {z : ℂ} (hz : z.im ≠ 0) :
    ∃ offset : ℕ,
      Monotone (fun n : ℕ => resolventLogSeventhWeight z (offset + n)) := by
  obtain ⟨offset, hsixth⟩ :=
    exists_resolventLogSixthWeight_monotone_natAdd hz
  refine ⟨offset, ?_⟩
  intro m n hmn
  have hindexNat : offset + m + 1 ≤ offset + n + 1 :=
    Nat.add_le_add_right (Nat.add_le_add_left hmn offset) 1
  have hindex : ((offset + m + 1 : ℕ) : ℝ) ≤
      ((offset + n + 1 : ℕ) : ℝ) := by exact_mod_cast hindexNat
  have hlog : Real.log (((offset + m + 1 : ℕ) : ℝ)) ≤
      Real.log (((offset + n + 1 : ℕ) : ℝ)) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by exact Set.mem_Ioi.mpr (by positivity))
      (by exact Set.mem_Ioi.mpr (by positivity)) hindex
  have hlog0 : 0 ≤ Real.log (((offset + m + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (offset + m)))
  calc
    resolventLogSeventhWeight z (offset + m) =
        Real.log (((offset + m + 1 : ℕ) : ℝ)) *
          resolventLogSixthWeight z (offset + m) := by
            rw [resolventLogSeventhWeight, resolventLogSixthWeight]
            norm_num [Nat.cast_add]
            ring
    _ ≤ Real.log (((offset + n + 1 : ℕ) : ℝ)) *
          resolventLogSixthWeight z (offset + n) :=
      mul_le_mul hlog (hsixth hmn)
        (resolventLogSixthWeight_nonneg hz (offset + m)) (hlog0.trans hlog)
    _ = resolventLogSeventhWeight z (offset + n) := by
      rw [resolventLogSeventhWeight, resolventLogSixthWeight]
      norm_num [Nat.cast_add]
      ring

/-- `log(M+1)⁵ / A_M(z)` tends to zero. -/
theorem tendsto_log_succ_fifth_div_resolventMass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log (cutoff + 1) ^ 5 / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hfifth := tendsto_log_fifth_div_resolventMass_zero hz
  have hfourth := tendsto_log_fourth_div_resolventMass_zero hz
  have hcube := tendsto_log_cube_div_resolventMass_zero hz
  have hsq := tendsto_log_sq_div_resolventMass_zero hz
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hstep := Real.tendsto_log_nat_add_one_sub_log
  have hlimit :=
    (((((hfifth.add ((hstep.mul hfourth).const_mul 5)).add
      (((hstep.pow 2).mul hcube).const_mul 10)).add
        (((hstep.pow 3).mul hsq).const_mul 10)).add
          (((hstep.pow 4).mul hlog).const_mul 5)).add
            ((hstep.pow 5).mul hinvMass))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 5 / resolventMass z cutoff +
        5 * ((Real.log (cutoff + 1) - Real.log cutoff) *
          (Real.log cutoff ^ 4 / resolventMass z cutoff)) +
        10 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          (Real.log cutoff ^ 3 / resolventMass z cutoff)) +
        10 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          (Real.log cutoff ^ 2 / resolventMass z cutoff)) +
        5 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          (Real.log cutoff / resolventMass z cutoff)) +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

/-- The log-seventh endpoint weight is negligible relative to resolvent mass. -/
theorem tendsto_resolventLogSeventhWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogSeventhWeight z cutoff / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hproduct := (tendsto_log_succ_fifth_div_resolventMass_zero hz).mul
    (tendsto_resolventLogSqWeight_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) ^ 5 / resolventMass z cutoff) *
        resolventLogSqWeight z cutoff) atTop (nhds 0) := by
    simpa only [zero_mul] using hproduct
  apply hlimit.congr'
  filter_upwards with cutoff
  rw [resolventLogSeventhWeight, resolventLogSqWeight]
  ring

theorem tendsto_resolventLogSeventh_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff,
        resolventLogSeventhWeight z n * q n) / resolventMass z cutoff)
      atTop (nhds 0) := by
  apply tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
    hperiod hq hsum
  · exact resolventLogSeventhWeight_nonneg hz
  · exact exists_resolventLogSeventhWeight_monotone_natAdd hz
  · exact (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
  · exact tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  · exact tendsto_resolventLogSeventhWeight_div_mass_zero hz

/-- The logarithmic mean times the log-sixth endpoint weight is negligible
relative to resolvent mass. -/
theorem tendsto_resolventLogMean_mul_resolventLogSixthWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff * resolventLogSixthWeight z cutoff /
        resolventMass z cutoff) atTop (nhds 0) := by
  have hproduct := (tendsto_resolventLogMean_div_log_succ_one hz).mul
    (tendsto_resolventLogSeventhWeight_div_mass_zero hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / Real.log (cutoff + 1)) *
        (resolventLogSeventhWeight z cutoff / resolventMass z cutoff))
      atTop (nhds 0) := by
    simpa only [one_mul] using hproduct
  apply hlimit.congr'
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log (cutoff + 1))
      atTop atTop := by
    have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
        atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
    convert Real.tendsto_log_atTop.comp hcastSucc using 1
    ext cutoff
    norm_num [Nat.cast_add]
  filter_upwards [hlogTop.eventually_ne_atTop 0] with cutoff hlog
  rw [resolventLogSeventhWeight, resolventLogSixthWeight]
  field_simp [hlog]

/-- A zero-mean log-sixth periodic sum remains negligible after multiplication
by the logarithmic mean. -/
theorem tendsto_resolventLogMean_mul_resolventLogSixth_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range cutoff,
          resolventLogSixthWeight z n * q n)
      atTop (nhds 0) := by
  let modifiedMass : ℕ → ℝ := fun cutoff =>
    resolventMass z cutoff / resolventLogMean z cutoff
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmeanTopAux :=
    (tendsto_resolventLogMean_sub_log hz).add_atTop hlogTop
  have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
    have h : Tendsto (fun cutoff : ℕ =>
        (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
        atTop atTop := hmeanTopAux
    apply h.congr'
    filter_upwards with cutoff
    ring
  have hmeanNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventLogMean z cutoff ≠ 0 := hmeanTop.eventually_ne_atTop 0
  have hmassNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventMass z cutoff ≠ 0 :=
    (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
  have hmodifiedNe : ∀ᶠ cutoff : ℕ in atTop,
      modifiedMass cutoff ≠ 0 := by
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    exact div_ne_zero hmass hmean
  have hinvModified : Tendsto (fun cutoff : ℕ =>
      (modifiedMass cutoff)⁻¹) atTop (nhds 0) := by
    have h := tendsto_resolventLogMean_div_mass_zero hz
    apply h.congr'
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    simp only [modifiedMass]
    field_simp [hmass, hmean]
  have hweightModified : Tendsto (fun cutoff : ℕ =>
      resolventLogSixthWeight z cutoff / modifiedMass cutoff)
      atTop (nhds 0) := by
    have h :=
      tendsto_resolventLogMean_mul_resolventLogSixthWeight_div_mass_zero hz
    apply h.congr'
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    simp only [modifiedMass]
    field_simp [hmass, hmean]
  have hweighted :=
    tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
      hperiod hq hsum (resolventLogSixthWeight_nonneg hz)
      (exists_resolventLogSixthWeight_monotone_natAdd hz)
      hmodifiedNe hinvModified hweightModified
  apply hweighted.congr'
  filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
  simp only [modifiedMass]
  field_simp [hmass, hmean]

/-- The square of the logarithmic mean times the log-fifth endpoint weight is
negligible relative to resolvent mass. -/
theorem tendsto_resolventLogMean_sq_mul_resolventLogFifthWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 2 * resolventLogFifthWeight z cutoff /
        resolventMass z cutoff) atTop (nhds 0) := by
  have hproduct := (tendsto_resolventLogMean_div_log_succ_one hz).pow 2 |>.mul
    (tendsto_resolventLogSeventhWeight_div_mass_zero hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / Real.log (cutoff + 1)) ^ 2 *
        (resolventLogSeventhWeight z cutoff / resolventMass z cutoff))
      atTop (nhds 0) := by
    simpa only [one_pow, one_mul] using hproduct
  apply hlimit.congr'
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log (cutoff + 1))
      atTop atTop := by
    have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
        atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
    convert Real.tendsto_log_atTop.comp hcastSucc using 1
    ext cutoff
    norm_num [Nat.cast_add]
  filter_upwards [hlogTop.eventually_ne_atTop 0] with cutoff hlog
  rw [resolventLogSeventhWeight, resolventLogFifthWeight]
  field_simp [hlog]

/-- A zero-mean log-fifth periodic sum remains negligible after multiplication
by the square of the logarithmic mean. -/
theorem tendsto_resolventLogMean_sq_mul_resolventLogFifth_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range cutoff,
          resolventLogFifthWeight z n * q n)
      atTop (nhds 0) := by
  let modifiedMass : ℕ → ℝ := fun cutoff =>
    resolventMass z cutoff / resolventLogMean z cutoff ^ 2
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmeanTopAux :=
    (tendsto_resolventLogMean_sub_log hz).add_atTop hlogTop
  have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
    have h : Tendsto (fun cutoff : ℕ =>
        (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
        atTop atTop := hmeanTopAux
    apply h.congr'
    filter_upwards with cutoff
    ring
  have hmeanNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventLogMean z cutoff ≠ 0 := hmeanTop.eventually_ne_atTop 0
  have hmassNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventMass z cutoff ≠ 0 :=
    (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
  have hmodifiedNe : ∀ᶠ cutoff : ℕ in atTop,
      modifiedMass cutoff ≠ 0 := by
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    exact div_ne_zero hmass (pow_ne_zero 2 hmean)
  have hinvModified : Tendsto (fun cutoff : ℕ =>
      (modifiedMass cutoff)⁻¹) atTop (nhds 0) := by
    have h := tendsto_resolventLogMean_sq_div_mass_zero hz
    apply h.congr'
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    simp only [modifiedMass]
    field_simp [hmass, hmean]
  have hweightModified : Tendsto (fun cutoff : ℕ =>
      resolventLogFifthWeight z cutoff / modifiedMass cutoff)
      atTop (nhds 0) := by
    have h :=
      tendsto_resolventLogMean_sq_mul_resolventLogFifthWeight_div_mass_zero hz
    apply h.congr'
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    simp only [modifiedMass]
    field_simp [hmass, hmean]
  have hweighted :=
    tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
      hperiod hq hsum (resolventLogFifthWeight_nonneg hz)
      (exists_resolventLogFifthWeight_monotone_natAdd hz)
      hmodifiedNe hinvModified hweightModified
  apply hweighted.congr'
  filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
  simp only [modifiedMass]
  field_simp [hmass, hmean]

/-- The cube of the logarithmic mean times the log-fourth endpoint weight is
negligible relative to resolvent mass. -/
theorem tendsto_resolventLogMean_cube_mul_resolventLogFourthWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 3 * resolventLogFourthWeight z cutoff /
        resolventMass z cutoff) atTop (nhds 0) := by
  have hproduct := (tendsto_resolventLogMean_div_log_succ_one hz).pow 3 |>.mul
    (tendsto_resolventLogSeventhWeight_div_mass_zero hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / Real.log (cutoff + 1)) ^ 3 *
        (resolventLogSeventhWeight z cutoff / resolventMass z cutoff))
      atTop (nhds 0) := by
    simpa only [one_pow, one_mul] using hproduct
  apply hlimit.congr'
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log (cutoff + 1))
      atTop atTop := by
    have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
        atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
    convert Real.tendsto_log_atTop.comp hcastSucc using 1
    ext cutoff
    norm_num [Nat.cast_add]
  filter_upwards [hlogTop.eventually_ne_atTop 0] with cutoff hlog
  rw [resolventLogSeventhWeight, resolventLogFourthWeight]
  field_simp [hlog]

/-- A zero-mean log-fourth periodic sum remains negligible after multiplication
by the cube of the logarithmic mean. -/
theorem tendsto_resolventLogMean_cube_mul_resolventLogFourth_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 3 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range cutoff,
          resolventLogFourthWeight z n * q n)
      atTop (nhds 0) := by
  let modifiedMass : ℕ → ℝ := fun cutoff =>
    resolventMass z cutoff / resolventLogMean z cutoff ^ 3
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmeanTopAux :=
    (tendsto_resolventLogMean_sub_log hz).add_atTop hlogTop
  have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
    have h : Tendsto (fun cutoff : ℕ =>
        (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
        atTop atTop := hmeanTopAux
    apply h.congr'
    filter_upwards with cutoff
    ring
  have hmeanNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventLogMean z cutoff ≠ 0 := hmeanTop.eventually_ne_atTop 0
  have hmassNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventMass z cutoff ≠ 0 :=
    (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
  have hmodifiedNe : ∀ᶠ cutoff : ℕ in atTop,
      modifiedMass cutoff ≠ 0 := by
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    exact div_ne_zero hmass (pow_ne_zero 3 hmean)
  have hinvModified : Tendsto (fun cutoff : ℕ =>
      (modifiedMass cutoff)⁻¹) atTop (nhds 0) := by
    have h := tendsto_resolventLogMean_cube_div_mass_zero hz
    apply h.congr'
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    simp only [modifiedMass]
    field_simp [hmass, hmean]
  have hweightModified : Tendsto (fun cutoff : ℕ =>
      resolventLogFourthWeight z cutoff / modifiedMass cutoff)
      atTop (nhds 0) := by
    have h :=
      tendsto_resolventLogMean_cube_mul_resolventLogFourthWeight_div_mass_zero hz
    apply h.congr'
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    simp only [modifiedMass]
    field_simp [hmass, hmean]
  have hweighted :=
    tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
      hperiod hq hsum (resolventLogFourthWeight_nonneg hz)
      (exists_resolventLogFourthWeight_monotone_natAdd hz)
      hmodifiedNe hinvModified hweightModified
  apply hweighted.congr'
  filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
  simp only [modifiedMass]
  field_simp [hmass, hmean]

/-- The fourth power of the logarithmic mean times the log-cubic endpoint weight is
negligible relative to resolvent mass. -/
theorem tendsto_resolventLogMean_fourth_mul_resolventLogCubeWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 4 * resolventLogCubeWeight z cutoff /
        resolventMass z cutoff) atTop (nhds 0) := by
  have hproduct := (tendsto_resolventLogMean_div_log_succ_one hz).pow 4 |>.mul
    (tendsto_resolventLogSeventhWeight_div_mass_zero hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / Real.log (cutoff + 1)) ^ 4 *
        (resolventLogSeventhWeight z cutoff / resolventMass z cutoff))
      atTop (nhds 0) := by
    simpa only [one_pow, one_mul] using hproduct
  apply hlimit.congr'
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log (cutoff + 1))
      atTop atTop := by
    have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
        atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
    convert Real.tendsto_log_atTop.comp hcastSucc using 1
    ext cutoff
    norm_num [Nat.cast_add]
  filter_upwards [hlogTop.eventually_ne_atTop 0] with cutoff hlog
  rw [resolventLogSeventhWeight, resolventLogCubeWeight]
  field_simp [hlog]

/-- A zero-mean log-cubic periodic sum remains negligible after multiplication
by the fourth power of the logarithmic mean. -/
theorem tendsto_resolventLogMean_fourth_mul_resolventLogCube_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 4 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range cutoff,
          resolventLogCubeWeight z n * q n)
      atTop (nhds 0) := by
  let modifiedMass : ℕ → ℝ := fun cutoff =>
    resolventMass z cutoff / resolventLogMean z cutoff ^ 4
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmeanTopAux :=
    (tendsto_resolventLogMean_sub_log hz).add_atTop hlogTop
  have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
    have h : Tendsto (fun cutoff : ℕ =>
        (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
        atTop atTop := hmeanTopAux
    apply h.congr'
    filter_upwards with cutoff
    ring
  have hmeanNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventLogMean z cutoff ≠ 0 := hmeanTop.eventually_ne_atTop 0
  have hmassNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventMass z cutoff ≠ 0 :=
    (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
  have hmodifiedNe : ∀ᶠ cutoff : ℕ in atTop,
      modifiedMass cutoff ≠ 0 := by
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    exact div_ne_zero hmass (pow_ne_zero 4 hmean)
  have hinvModified : Tendsto (fun cutoff : ℕ =>
      (modifiedMass cutoff)⁻¹) atTop (nhds 0) := by
    have h := tendsto_resolventLogMean_fourth_div_mass_zero hz
    apply h.congr'
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    simp only [modifiedMass]
    field_simp [hmass, hmean]
  have hweightModified : Tendsto (fun cutoff : ℕ =>
      resolventLogCubeWeight z cutoff / modifiedMass cutoff)
      atTop (nhds 0) := by
    have h :=
      tendsto_resolventLogMean_fourth_mul_resolventLogCubeWeight_div_mass_zero hz
    apply h.congr'
    filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
    simp only [modifiedMass]
    field_simp [hmass, hmean]
  have hweighted :=
    tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
      hperiod hq hsum (resolventLogCubeWeight_nonneg hz)
      (exists_resolventLogCubeWeight_monotone_natAdd hz)
      hmodifiedNe hinvModified hweightModified
  apply hweighted.congr'
  filter_upwards [hmassNe, hmeanNe] with cutoff hmass hmean
  simp only [modifiedMass]
  field_simp [hmass, hmean]

/-- `log(M)⁷ / A_M(z)` tends to zero. -/
theorem tendsto_log_seventh_div_resolventMass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 7 / resolventMass z cutoff) atTop (nhds 0) := by
  have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
      atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hnonicSuccBase : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 9 / ((cutoff : ℝ) + 1))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 9 one_ne_zero).comp hcastSucc
    convert h using 1
    ext cutoff
    simp only [Function.comp_apply, one_mul, add_zero]
  have hsuccRatio : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) + 1) / cutoff) atTop (nhds 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (1 : ℝ) 0 1 (d := 1) (by norm_num)
    convert h using 1
    · ext cutoff
      ring
    · norm_num
  have hnonicSucc : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 9 / cutoff) atTop (nhds 0) := by
    have h := hnonicSuccBase.mul hsuccRatio
    have h' : Tendsto (fun cutoff : ℕ =>
        (Real.log ((cutoff : ℝ) + 1) ^ 9 / ((cutoff : ℝ) + 1)) *
          (((cutoff : ℝ) + 1) / cutoff)) atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
    have hcutoffNat : 0 < cutoff :=
      lt_of_lt_of_le Nat.zero_lt_one hcutoff
    have hcutoff0 : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat.ne'
    have hsucc0 : (cutoff : ℝ) + 1 ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast Nat.zero_lt_succ cutoff)
    field_simp [hcutoff0, hsucc0]
  have hlogFactor : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 7 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      exact div_nonneg
        (mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hcutoff)) 7)
          (sq_nonneg _))
        (by exact_mod_cast hcutoffNat.le)
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      have hcutoffPos : (0 : ℝ) < cutoff := by exact_mod_cast hcutoffNat
      have hlog0 : 0 ≤ Real.log (cutoff : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hcutoff)
      have hlogLe : Real.log (cutoff : ℝ) ≤
          Real.log ((cutoff : ℝ) + 1) := by
        exact Real.strictMonoOn_log.monotoneOn
          (by exact Set.mem_Ioi.mpr hcutoffPos)
          (by exact Set.mem_Ioi.mpr (by positivity)) (by linarith)
      exact div_le_div_of_nonneg_right (by
        calc
          Real.log (cutoff : ℝ) ^ 7 *
              Real.log ((cutoff : ℝ) + 1) ^ 2 ≤
            Real.log ((cutoff : ℝ) + 1) ^ 7 *
              Real.log ((cutoff : ℝ) + 1) ^ 2 := by
                gcongr
          _ = Real.log ((cutoff : ℝ) + 1) ^ 9 := by ring) hcutoffPos.le
    · exact hnonicSucc
  have hmassRatio := tendsto_resolventMass_div_nat_div_log_sq_one hz
  have hmassRatioInv := hmassRatio.inv₀ (by norm_num)
  have hproduct := hlogFactor.mul hmassRatioInv
  have hproduct' : Tendsto (fun cutoff : ℕ =>
      (Real.log cutoff ^ 7 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff) *
        (resolventMass z cutoff /
          ((cutoff : ℝ) / Real.log ((cutoff : ℝ) + 1) ^ 2))⁻¹)
      atTop (nhds 0) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [Ici_mem_atTop 1,
      (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hcutoff hmass
  have hcutoffNat : 0 < cutoff :=
    lt_of_lt_of_le Nat.zero_lt_one hcutoff
  have hcutoff0 : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat.ne'
  have hlogSucc : Real.log ((cutoff : ℝ) + 1) ≠ 0 := by
    rw [Real.log_ne_zero]
    refine ⟨ne_of_gt (by linarith), ?_, ?_⟩
    · intro h
      apply hcutoff0
      linarith
    · intro h
      have hpos : (0 : ℝ) < cutoff + 1 := by linarith
      linarith
  field_simp [hcutoff0, hlogSucc, hmass]

/-- The seventh power of the resolvent logarithmic mean is negligible relative
to resolvent mass. -/
theorem tendsto_resolventLogMean_seventh_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 7 / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hlogSeventh := tendsto_log_seventh_div_resolventMass_zero hz
  have hdelta := tendsto_resolventLogMean_sub_log hz
  have hlogSixth := tendsto_log_sixth_div_resolventMass_zero hz
  have hlogFifth := tendsto_log_fifth_div_resolventMass_zero hz
  have hlogFourth := tendsto_log_fourth_div_resolventMass_zero hz
  have hlogCube := tendsto_log_cube_div_resolventMass_zero hz
  have hlogSq := tendsto_log_sq_div_resolventMass_zero hz
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hlimit :=
    (((((((hlogSeventh.add ((hdelta.mul hlogSixth).const_mul 7)).add
      (((hdelta.pow 2).mul hlogFifth).const_mul 21)).add
        (((hdelta.pow 3).mul hlogFourth).const_mul 35)).add
          (((hdelta.pow 4).mul hlogCube).const_mul 35)).add
            (((hdelta.pow 5).mul hlogSq).const_mul 21)).add
              (((hdelta.pow 6).mul hlog).const_mul 7)).add
                ((hdelta.pow 7).mul hinvMass))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 7 / resolventMass z cutoff +
        7 * ((resolventLogMean z cutoff - Real.log cutoff) *
          (Real.log cutoff ^ 6 / resolventMass z cutoff)) +
        21 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 2 *
          (Real.log cutoff ^ 5 / resolventMass z cutoff)) +
        35 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 3 *
          (Real.log cutoff ^ 4 / resolventMass z cutoff)) +
        35 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 4 *
          (Real.log cutoff ^ 3 / resolventMass z cutoff)) +
        21 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 5 *
          (Real.log cutoff ^ 2 / resolventMass z cutoff)) +
        7 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 6 *
          (Real.log cutoff / resolventMass z cutoff)) +
        (resolventLogMean z cutoff - Real.log cutoff) ^ 7 *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

theorem tendsto_resolventCenteredLogSeventh_periodicResidue_zero
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 *
              (q n - periodMean q period))
      atTop (nhds 0) := by
  let centered : ℕ → ℝ := fun n => q n - periodMean q period
  have hcenteredPeriodic : Function.Periodic centered period := by
    intro n
    simp only [centered]
    rw [hq n]
  have hcenteredSum : ∑ r ∈ Finset.range period, centered r = 0 := by
    simpa only [centered] using sum_period_sub_periodMean (q := q) hperiod
  have hweightBound :=
    isBounded_range_periodic_weightedSum_of_eventually_antitone
      hperiod hcenteredPeriodic hcenteredSum
        (exists_resolventWeight_antitone_natAdd hz)
        (tendsto_resolventWeight_zero z)
  have hlogWeightBound :=
    isBounded_range_periodic_weightedSum_of_eventually_antitone
      hperiod hcenteredPeriodic hcenteredSum
        (exists_resolventLogWeight_antitone_natAdd hz)
        (tendsto_resolventLogWeight_zero hz)
  have hlogSqWeightBound :=
    isBounded_range_periodic_weightedSum_of_eventually_monotone_or_antitone
      hperiod hcenteredPeriodic hcenteredSum
        (exists_resolventLogSqWeight_monotone_or_antitone_natAdd hz)
        (tendsto_resolventLogSqWeight_one hz)
  have hscaleTop := tendsto_nat_const_mul_atTop hscale
  have hweightScaled : IsBoundedUnder (· ≤ ·) atTop
      (fun cutoff : ℕ =>
        ‖∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n * centered n‖) := by
    have h := hscaleTop.isBoundedUnder_comp hweightBound
    change IsBoundedUnder (· ≤ ·) atTop (fun cutoff : ℕ =>
      ‖∑ n ∈ Finset.range (scale * cutoff),
        resolventWeight z n * centered n‖) at h
    exact h
  have hlogWeightScaled : IsBoundedUnder (· ≤ ·) atTop
      (fun cutoff : ℕ =>
        ‖∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n‖) := by
    have h := hscaleTop.isBoundedUnder_comp hlogWeightBound
    change IsBoundedUnder (· ≤ ·) atTop (fun cutoff : ℕ =>
      ‖∑ n ∈ Finset.range (scale * cutoff),
        resolventLogWeight z n * centered n‖) at h
    exact h
  have hlogSqWeightScaled : IsBoundedUnder (· ≤ ·) atTop
      (fun cutoff : ℕ =>
        ‖∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSqWeight z n * centered n‖) := by
    have h := hscaleTop.isBoundedUnder_comp hlogSqWeightBound
    change IsBoundedUnder (· ≤ ·) atTop (fun cutoff : ℕ =>
      ‖∑ n ∈ Finset.range (scale * cutoff),
        resolventLogSqWeight z n * centered n‖) at h
    exact h
  have hseventhBase :=
    tendsto_resolventLogSeventh_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hseventhAtScale := hseventhBase.comp hscaleTop
  have hseventhAtScale' : Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff),
        resolventLogSeventhWeight z n * centered n) /
          resolventMass z (scale * cutoff)) atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff),
        resolventLogSeventhWeight z n * centered n) /
          resolventMass z (scale * cutoff)) atTop (nhds 0) at hseventhAtScale
    exact hseventhAtScale
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hseventhProduct := hseventhAtScale'.mul hmassRatio
  have hseventhPart : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSeventhWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSeventhWeight z n * centered n) /
          resolventMass z (scale * cutoff)) *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hseventhProduct
    apply hlimit.congr'
    filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
    have hcutoffNat : 0 < cutoff :=
      lt_of_lt_of_le Nat.zero_lt_one hcutoff
    have hmass : resolventMass z cutoff ≠ 0 := by
      rw [resolventMass]
      exact ne_of_gt (Finset.sum_pos'
        (fun n _ => (resolventWeight_pos hz n).le)
        ⟨0, Finset.mem_range.mpr hcutoffNat, resolventWeight_pos hz 0⟩)
    have hscaledNat : 0 < scale * cutoff := Nat.mul_pos hscale hcutoffNat
    have hmassScaled : resolventMass z (scale * cutoff) ≠ 0 := by
      rw [resolventMass]
      exact ne_of_gt (Finset.sum_pos'
        (fun n _ => (resolventWeight_pos hz n).le)
        ⟨0, Finset.mem_range.mpr hscaledNat, resolventWeight_pos hz 0⟩)
    field_simp [hmass, hmassScaled]
  have hsixthBase :=
    tendsto_resolventLogMean_mul_resolventLogSixth_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hsixthAtScale := hsixthBase.comp hscaleTop
  have hsixthAtScale' : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSixthWeight z n * centered n)
      atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSixthWeight z n * centered n)
      atTop (nhds 0) at hsixthAtScale
    exact hsixthAtScale
  have hmeanRatio := tendsto_resolventLogMean_nat_mul_div hz hscale
  have hmeanRatioInv := hmeanRatio.inv₀ (by norm_num)
  have hsixthProduct := (hsixthAtScale'.mul hmeanRatioInv).mul hmassRatio
  have hsixthPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSixthWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((resolventLogMean z (scale * cutoff) /
            resolventMass z (scale * cutoff)) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSixthWeight z n * centered n) *
        (resolventLogMean z (scale * cutoff) /
          resolventLogMean z cutoff)⁻¹ *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hsixthProduct
    have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
        atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hmeanTopAux :=
      (tendsto_resolventLogMean_sub_log hz).add_atTop hlogTop
    have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
      have h : Tendsto (fun cutoff : ℕ =>
          (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
          atTop atTop := hmeanTopAux
      apply h.congr'
      filter_upwards with cutoff
      ring
    have hmeanNe := hmeanTop.eventually_ne_atTop 0
    have hmeanScaledNe := (hmeanTop.comp hscaleTop).eventually_ne_atTop 0
    have hmassNe :=
      (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
    have hmassScaledNe :=
      ((tendsto_resolventMass_atTop hz).comp hscaleTop).eventually_ne_atTop 0
    apply hlimit.congr'
    filter_upwards [hmeanNe, hmeanScaledNe, hmassNe, hmassScaledNe]
      with cutoff hmean hmeanScaled hmass hmassScaled
    change resolventLogMean z (scale * cutoff) ≠ 0 at hmeanScaled
    change resolventMass z (scale * cutoff) ≠ 0 at hmassScaled
    rw [inv_div]
    field_simp [hmean, hmeanScaled, hmass, hmassScaled]
  have hfifthBase :=
    tendsto_resolventLogMean_sq_mul_resolventLogFifth_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hfifthAtScale := hfifthBase.comp hscaleTop
  have hfifthAtScale' : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 2 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFifthWeight z n * centered n)
      atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 2 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFifthWeight z n * centered n)
      atTop (nhds 0) at hfifthAtScale
    exact hfifthAtScale
  have hmeanRatioSqInv := hmeanRatioInv.pow 2
  have hfifthProduct := (hfifthAtScale'.mul hmeanRatioSqInv).mul hmassRatio
  have hfifthPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFifthWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((resolventLogMean z (scale * cutoff) ^ 2 /
            resolventMass z (scale * cutoff)) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFifthWeight z n * centered n) *
        (resolventLogMean z (scale * cutoff) /
          resolventLogMean z cutoff)⁻¹ ^ 2 *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hfifthProduct
    have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
        atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hmeanTopAux :=
      (tendsto_resolventLogMean_sub_log hz).add_atTop hlogTop
    have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
      have h : Tendsto (fun cutoff : ℕ =>
          (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
          atTop atTop := hmeanTopAux
      apply h.congr'
      filter_upwards with cutoff
      ring
    have hmeanNe := hmeanTop.eventually_ne_atTop 0
    have hmeanScaledNe := (hmeanTop.comp hscaleTop).eventually_ne_atTop 0
    have hmassNe :=
      (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
    have hmassScaledNe :=
      ((tendsto_resolventMass_atTop hz).comp hscaleTop).eventually_ne_atTop 0
    apply hlimit.congr'
    filter_upwards [hmeanNe, hmeanScaledNe, hmassNe, hmassScaledNe]
      with cutoff hmean hmeanScaled hmass hmassScaled
    change resolventLogMean z (scale * cutoff) ≠ 0 at hmeanScaled
    change resolventMass z (scale * cutoff) ≠ 0 at hmassScaled
    rw [inv_div]
    field_simp [hmean, hmeanScaled, hmass, hmassScaled]
  have hfourthBase :=
    tendsto_resolventLogMean_cube_mul_resolventLogFourth_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hfourthAtScale := hfourthBase.comp hscaleTop
  have hfourthAtScale' : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 3 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFourthWeight z n * centered n)
      atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 3 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFourthWeight z n * centered n)
      atTop (nhds 0) at hfourthAtScale
    exact hfourthAtScale
  have hmeanRatioCubeInv := hmeanRatioInv.pow 3
  have hfourthProduct := (hfourthAtScale'.mul hmeanRatioCubeInv).mul hmassRatio
  have hfourthPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 3 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFourthWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((resolventLogMean z (scale * cutoff) ^ 3 /
            resolventMass z (scale * cutoff)) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFourthWeight z n * centered n) *
        (resolventLogMean z (scale * cutoff) /
          resolventLogMean z cutoff)⁻¹ ^ 3 *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hfourthProduct
    have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
        atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hmeanTopAux :=
      (tendsto_resolventLogMean_sub_log hz).add_atTop hlogTop
    have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
      have h : Tendsto (fun cutoff : ℕ =>
          (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
          atTop atTop := hmeanTopAux
      apply h.congr'
      filter_upwards with cutoff
      ring
    have hmeanNe := hmeanTop.eventually_ne_atTop 0
    have hmeanScaledNe := (hmeanTop.comp hscaleTop).eventually_ne_atTop 0
    have hmassNe :=
      (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
    have hmassScaledNe :=
      ((tendsto_resolventMass_atTop hz).comp hscaleTop).eventually_ne_atTop 0
    apply hlimit.congr'
    filter_upwards [hmeanNe, hmeanScaledNe, hmassNe, hmassScaledNe]
      with cutoff hmean hmeanScaled hmass hmassScaled
    change resolventLogMean z (scale * cutoff) ≠ 0 at hmeanScaled
    change resolventMass z (scale * cutoff) ≠ 0 at hmassScaled
    rw [inv_div]
    field_simp [hmean, hmeanScaled, hmass, hmassScaled]
  have hcubicBase :=
    tendsto_resolventLogMean_fourth_mul_resolventLogCube_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hcubicAtScale := hcubicBase.comp hscaleTop
  have hcubicAtScale' : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 4 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 4 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) at hcubicAtScale
    exact hcubicAtScale
  have hmeanRatioFourthInv := hmeanRatioInv.pow 4
  have hcubicProduct := (hcubicAtScale'.mul hmeanRatioFourthInv).mul hmassRatio
  have hcubicPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 4 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((resolventLogMean z (scale * cutoff) ^ 4 /
            resolventMass z (scale * cutoff)) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogCubeWeight z n * centered n) *
        (resolventLogMean z (scale * cutoff) /
          resolventLogMean z cutoff)⁻¹ ^ 4 *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hcubicProduct
    have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
        atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hmeanTopAux :=
      (tendsto_resolventLogMean_sub_log hz).add_atTop hlogTop
    have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
      have h : Tendsto (fun cutoff : ℕ =>
          (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
          atTop atTop := hmeanTopAux
      apply h.congr'
      filter_upwards with cutoff
      ring
    have hmeanNe := hmeanTop.eventually_ne_atTop 0
    have hmeanScaledNe := (hmeanTop.comp hscaleTop).eventually_ne_atTop 0
    have hmassNe :=
      (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
    have hmassScaledNe :=
      ((tendsto_resolventMass_atTop hz).comp hscaleTop).eventually_ne_atTop 0
    apply hlimit.congr'
    filter_upwards [hmeanNe, hmeanScaledNe, hmassNe, hmassScaledNe]
      with cutoff hmean hmeanScaled hmass hmassScaled
    change resolventLogMean z (scale * cutoff) ≠ 0 at hmeanScaled
    change resolventMass z (scale * cutoff) ≠ 0 at hmassScaled
    rw [inv_div]
    field_simp [hmean, hmeanScaled, hmass, hmassScaled]
  have hquadraticCoefficient : Tendsto (fun cutoff : ℕ =>
      21 * resolventLogMean z cutoff ^ 5 / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_fifth_div_mass_zero hz).const_mul 21
    simpa only [mul_div_assoc, mul_zero] using h
  have hquadraticPart : Tendsto (fun cutoff : ℕ =>
      (21 * resolventLogMean z cutoff ^ 5 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSqWeight z n * centered n) atTop (nhds 0) :=
    hquadraticCoefficient.zero_mul_isBoundedUnder_le hlogSqWeightScaled
  have hlinearCoefficient : Tendsto (fun cutoff : ℕ =>
      7 * resolventLogMean z cutoff ^ 6 / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_sixth_div_mass_zero hz).const_mul 7
    simpa only [mul_div_assoc, mul_zero] using h
  have hlinearPart : Tendsto (fun cutoff : ℕ =>
      (7 * resolventLogMean z cutoff ^ 6 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n) atTop (nhds 0) :=
    hlinearCoefficient.zero_mul_isBoundedUnder_le hlogWeightScaled
  have hconstantPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 7 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n * centered n) atTop (nhds 0) :=
    (tendsto_resolventLogMean_seventh_div_mass_zero hz).zero_mul_isBoundedUnder_le
      hweightScaled
  have hlimit :=
    ((((((hseventhPart.sub (hsixthPart.const_mul 7)).add
      (hfifthPart.const_mul 21)).sub (hfourthPart.const_mul 35)).add
        (hcubicPart.const_mul 35)).sub hquadraticPart).add
          hlinearPart).sub hconstantPart
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSeventhWeight z n * centered n -
        7 * ((resolventLogMean z cutoff / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSixthWeight z n * centered n) +
        21 * ((resolventLogMean z cutoff ^ 2 /
            resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFifthWeight z n * centered n) -
        35 * ((resolventLogMean z cutoff ^ 3 /
            resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFourthWeight z n * centered n) +
        35 * ((resolventLogMean z cutoff ^ 4 /
            resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogCubeWeight z n * centered n) -
        (21 * resolventLogMean z cutoff ^ 5 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSqWeight z n * centered n +
        (7 * resolventLogMean z cutoff ^ 6 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogWeight z n * centered n -
        (resolventLogMean z cutoff ^ 7 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n * centered n) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 * centered n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSeventhWeight z n * centered n) -
          7 * resolventLogMean z cutoff *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogSixthWeight z n * centered n +
          21 * resolventLogMean z cutoff ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogFifthWeight z n * centered n -
          35 * resolventLogMean z cutoff ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogFourthWeight z n * centered n +
          35 * resolventLogMean z cutoff ^ 4 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogCubeWeight z n * centered n -
          21 * resolventLogMean z cutoff ^ 5 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogSqWeight z n * centered n +
          7 * resolventLogMean z cutoff ^ 6 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogWeight z n * centered n -
          resolventLogMean z cutoff ^ 7 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventWeight z n * centered n := by
    calc
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 * centered n) =
        ∑ n ∈ Finset.range (scale * cutoff),
          (resolventLogSeventhWeight z n * centered n -
            7 * resolventLogMean z cutoff *
              (resolventLogSixthWeight z n * centered n) +
            21 * resolventLogMean z cutoff ^ 2 *
              (resolventLogFifthWeight z n * centered n) -
            35 * resolventLogMean z cutoff ^ 3 *
              (resolventLogFourthWeight z n * centered n) +
            35 * resolventLogMean z cutoff ^ 4 *
              (resolventLogCubeWeight z n * centered n) -
            21 * resolventLogMean z cutoff ^ 5 *
              (resolventLogSqWeight z n * centered n) +
            7 * resolventLogMean z cutoff ^ 6 *
              (resolventLogWeight z n * centered n) -
            resolventLogMean z cutoff ^ 7 *
              (resolventWeight z n * centered n)) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [resolventLogSeventhWeight, resolventLogSixthWeight,
            resolventLogFifthWeight, resolventLogFourthWeight,
            resolventLogCubeWeight, resolventLogSqWeight, resolventLogWeight]
          ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
        simp_rw [← Finset.mul_sum]
  rw [hsum]
  ring

/-- Periodic averaging for the seventh centered logarithmic resolvent moment. -/
theorem tendsto_resolventCenteredLogSeventh_periodicWeightedSum
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 * q n)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 7 + 21 * Real.log scale ^ 5 -
          70 * Real.log scale ^ 4 + 315 * Real.log scale ^ 3 -
            924 * Real.log scale ^ 2 + 1855 * Real.log scale - 1854)) *
            periodMean q period)) := by
  have hscalar :=
    tendsto_resolventScaledCenteredLogSeventhMoment_div_mass hz hscale
  have hmain : Tendsto (fun cutoff : ℕ =>
      (resolventScaledCenteredLogSeventhMoment z scale cutoff /
        resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 7 + 21 * Real.log scale ^ 5 -
          70 * Real.log scale ^ 4 + 315 * Real.log scale ^ 3 -
            924 * Real.log scale ^ 2 + 1855 * Real.log scale - 1854)) *
            periodMean q period)) :=
    hscalar.mul_const (periodMean q period)
  have hresidue := tendsto_resolventCenteredLogSeventh_periodicResidue_zero
    hz hperiod hscale hq
  have hlimit := hresidue.add hmain
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 *
                (q n - periodMean q period) +
        (resolventScaledCenteredLogSeventhMoment z scale cutoff /
          resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 7 + 21 * Real.log scale ^ 5 -
          70 * Real.log scale ^ 4 + 315 * Real.log scale ^ 3 -
            924 * Real.log scale ^ 2 + 1855 * Real.log scale - 1854)) *
            periodMean q period)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 * q n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 *
              (q n - periodMean q period)) +
          periodMean q period *
            resolventScaledCenteredLogSeventhMoment z scale cutoff := by
    rw [resolventScaledCenteredLogSeventhMoment, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsum]
  ring

/-- The shifted periodic camera core with the centered seventh-power multiplier
converges entrywise to the seventh centered moment. -/
theorem tendsto_resolvent_shiftedCoreSeventhFunctional_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range
            (pairCoreLength (camera i) (camera j) cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 *
              realProfileProduct (camera i) (camera j) (n + 1))
      atTop (nhds (seventhCenteredMomentMatrix period camera i j)) := by
  let scale := min (cameraSlope (camera i)) (cameraSlope (camera j))
  let q : ℕ → ℝ := fun n =>
    realProfileProduct (camera i) (camera j) (n + 1)
  have hslope (k : index) : 0 < cameraSlope (camera k) := by
    rw [cameraSlope]
    split_ifs
    · norm_num
    · exact lt_of_lt_of_le (by norm_num) (hcamera k)
  have hscale : 0 < scale := lt_min (hslope i) (hslope j)
  have hproduct : Function.Periodic
      (realProfileProduct (camera i) (camera j)) period :=
    realProfileProduct_periodic (hcamera i) (hcamera j)
      (hcommon i) (hcommon j)
  have hq : Function.Periodic q period := by
    intro n
    simpa only [q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hproduct (n + 1)
  have hmean : periodMean q period =
      periodicProductMean period (camera i) (camera j) := by
    have h := periodMean_natAdd hproduct 1
    rw [periodMean_realProfileProduct] at h
    simpa only [q, Nat.add_comm] using h
  have hlimit := tendsto_resolventCenteredLogSeventh_periodicWeightedSum
    hz hperiod hscale hq
  rw [hmean] at hlimit
  have htarget :
      (((scale : ℝ) *
          (Real.log scale ^ 7 + 21 * Real.log scale ^ 5 -
            70 * Real.log scale ^ 4 + 315 * Real.log scale ^ 3 -
              924 * Real.log scale ^ 2 + 1855 * Real.log scale - 1854)) *
          periodicProductMean period (camera i) (camera j)) =
        seventhCenteredMomentMatrix period camera i j := by
    rw [seventhCenteredMomentMatrix_apply, periodicGramMatrix_apply]
    simp only [slopeOverlap, scale]
    ring
  rw [htarget] at hlimit
  simpa only [pairCoreLength, scale, q] using hlimit

/-- Seventh-power multiplier in the finite centered logarithmic coordinate. -/
def centeredSeventhMultiplier (z : ℂ) (cutoff n : ℕ) : ℝ :=
  (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7

/-- Product of the resolvent weight with the centered seventh-power
multiplier. -/
def resolventCenteredSeventhWeight (z : ℂ) (cutoff n : ℕ) : ℝ :=
  resolventWeight z n * centeredSeventhMultiplier z cutoff n

@[simp] theorem centeredPolynomialMultiplier_X_seventh
    (z : ℂ) (cutoff n : ℕ) :
    centeredPolynomialMultiplier (Polynomial.X ^ 7) z cutoff n =
      centeredSeventhMultiplier z cutoff n := by
  simp [centeredPolynomialMultiplier, centeredSeventhMultiplier]

/-- Every fixed literal seed/endpoint term vanishes for the centered
seventh-power functional weight. -/
theorem tendsto_resolventCenteredSeventh_finiteBoundaryTerm_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (r : ℕ) :
    Tendsto (fun cutoff =>
      finiteBoundaryTerm (resolventCenteredSeventhWeight z cutoff)
        cutoff camera₁ camera₂ r) atTop (nhds 0) := by
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
  have hlogDilated := tendsto_log_nat_mul_add_sub_log hscale r
  have hlogStep := Real.tendsto_log_nat_add_one_sub_log
  have hmean : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff - resolventLogMean z cutoff) atTop (nhds 1) := by
    have h := (tendsto_resolventLogMean_sub_log hz).neg
    simpa only [neg_sub, neg_neg] using h
  have hcoordinate : Tendsto (fun cutoff : ℕ =>
      Real.log (scale * cutoff + r + 1) - resolventLogMean z cutoff)
      atTop (nhds (Real.log scale + 1)) := by
    have hlimit := (hlogDilated.add hlogStep).add hmean
    have hlimit' : Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) +
          (Real.log (cutoff + 1) - Real.log cutoff) +
            (Real.log cutoff - resolventLogMean z cutoff))
        atTop (nhds (Real.log scale + 1)) := by
      convert hlimit using 1
      ring
    apply hlimit'.congr'
    filter_upwards with cutoff
    norm_num [Nat.cast_add, Nat.cast_mul]
  have hsixth :=
    tendsto_resolventCenteredSixth_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r
  have hproduct := hcoordinate.mul hsixth
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (scale * cutoff + r + 1) - resolventLogMean z cutoff) *
        finiteBoundaryTerm (resolventCenteredSixthWeight z cutoff)
          cutoff camera₁ camera₂ r) atTop (nhds 0) := by
    simpa only [mul_zero] using hproduct
  apply hlimit.congr'
  filter_upwards with cutoff
  rw [finiteBoundaryTerm, finiteBoundaryTerm]
  split_ifs
  · rw [resolventCenteredSeventhWeight, centeredSeventhMultiplier,
      resolventCenteredSixthWeight, centeredSixthMultiplier]
    simp only [pairCoreLength, scale]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  · ring

/-- The complete fixed-width literal boundary vanishes for the centered
seventh-power functional weight. -/
theorem tendsto_resolventCenteredSeventh_finiteBoundarySum_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) :
    Tendsto (fun cutoff =>
      finiteBoundarySum (resolventCenteredSeventhWeight z cutoff)
        cutoff camera₁ camera₂) atTop (nhds 0) := by
  have hsum := tendsto_finsetSum
    (Finset.range (pairBoundaryWidth camera₁ camera₂))
    (fun r _ => tendsto_resolventCenteredSeventh_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r)
  simpa only [finiteBoundarySum, Finset.sum_const_zero] using hsum

/-- Entrywise convergence of the complete literal centered-seventh-power
coefficient covariance to the seventh centered camera moment. -/
theorem tendsto_finiteCenteredSeventhCoefficientCovariance_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff camera i j)
      atTop (nhds (seventhCenteredMomentMatrix period camera i j)) := by
  have hcore := tendsto_resolvent_shiftedCoreSeventhFunctional_apply
    hz hperiod hcamera hcommon i j
  have hboundary := tendsto_resolventCenteredSeventh_finiteBoundarySum_zero
    hz (hcamera i) (hcamera j)
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hboundaryNormalized : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        finiteBoundarySum (resolventCenteredSeventhWeight z cutoff)
          cutoff (camera i) (camera j)) atTop (nhds 0) := by
    simpa only [zero_mul] using hinvMass.mul hboundary
  have hlimit := hcore.add hboundaryNormalized
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range
              (pairCoreLength (camera i) (camera j) cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 *
                realProfileProduct (camera i) (camera j) (n + 1) +
        (resolventMass z cutoff)⁻¹ *
          finiteBoundarySum (resolventCenteredSeventhWeight z cutoff)
            cutoff (camera i) (camera j))
      atTop (nhds (seventhCenteredMomentMatrix period camera i j)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  rw [finiteCenteredPolynomialCoefficientCovariance,
    finiteFunctionalCoefficientCovariance]
  simp only [centeredPolynomialMultiplier_X_seventh]
  have hnum :
      (∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventWeight z n * centeredSeventhMultiplier z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n) =
        ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventCenteredSeventhWeight z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredSeventhWeight]
  rw [hnum]
  rw [finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary
    (weight := resolventCenteredSeventhWeight z cutoff)
      (hcamera i) (hcamera j)]
  have hcoreEq :
      (∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventCenteredSeventhWeight z cutoff n *
            realProfileProduct (camera i) (camera j) (n + 1)) =
        ∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 *
              realProfileProduct (camera i) (camera j) (n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredSeventhWeight, centeredSeventhMultiplier]
  rw [hcoreEq]
  simp only [resolventMass]
  ring

/-- Matrix convergence of the complete literal centered-seventh-power
coefficient covariance. -/
theorem tendsto_finiteCenteredSeventhCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff camera)
      atTop (nhds (seventhCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff camera i j)
    atTop (nhds fun i j => seventhCenteredMomentMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_finiteCenteredSeventhCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j

/-- Finite entry-sup norm convergence of the literal centered-seventh-power
coefficient covariance. -/
theorem tendsto_norm_finiteCenteredSeventhCoefficientCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff camera -
        seventhCenteredMomentMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_finiteCenteredSeventhCoefficientCovariance
    hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => seventhCenteredMomentMatrix period camera)
        atTop (nhds (seventhCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- The literal six-camera centered-seventh-power covariance converges to the
exact documented matrix `sixCameraSeventhCenteredMoment`. -/
theorem
    tendsto_norm_sixCamera_finiteCenteredSeventhCoefficientCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff sixCamera -
        sixCameraSeventhCenteredMoment‖) atTop (nhds 0) := by
  rw [← sixCameraSeventhCenteredMoment_eq]
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  exact tendsto_norm_finiteCenteredSeventhCoefficientCovariance_sub
    hz (by norm_num : 0 < 420) hcamera sixCamera_commonPeriod

/-- Complexification of the seventh centered periodic camera moment. -/
def complexSeventhCenteredMomentMatrix {index : Type*} (period : ℕ)
    (camera : index → ℕ) : Matrix index index ℂ :=
  fun i j => (seventhCenteredMomentMatrix period camera i j : ℂ)

/-- Complexified convergence of the complete literal centered-seventh-power
coefficient covariance. -/
theorem tendsto_complex_finiteCenteredSeventhCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff i j =>
      (finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff camera i j : ℂ))
      atTop (nhds (complexSeventhCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    (finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff camera i j : ℂ))
    atTop (nhds fun i j =>
      (seventhCenteredMomentMatrix period camera i j : ℂ))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hreal := tendsto_finiteCenteredSeventhCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j
  exact (Complex.continuous_ofReal.tendsto
    (seventhCenteredMomentMatrix period camera i j)).comp hreal

/-- The normalized direct finite functional covariance for the centered
seventh-power multiplier converges to the complexified seventh centered
moment. -/
theorem tendsto_normalizedFiniteCenteredSeventhDirectCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalDirectCovariance z cutoff camera
        (centeredPolynomialMultiplier
          (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff))
      atTop (nhds (complexSeventhCenteredMomentMatrix period camera)) := by
  apply tendsto_normalizedFiniteFunctionalDirectCovariance_of_coefficients
    hcamera
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredSeventhCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of the normalized direct
centered-seventh-power functional covariance. -/
theorem tendsto_norm_normalizedFiniteCenteredSeventhDirectCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff camera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff) -
        complexSeventhCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredSeventhDirectCovariance
      hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => complexSeventhCenteredMomentMatrix period camera)
        atTop (nhds (complexSeventhCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Every compatible finite return-metric colligation family inherits the
centered seventh-moment limit. -/
theorem tendsto_normalizedFiniteCenteredSeventhReturnMetricCrossCovariance
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
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
      normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff camera
        (centeredPolynomialMultiplier
          (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff)
        (endpointMap cutoff) (poisson cutoff))
      atTop (nhds (complexSeventhCenteredMomentMatrix period camera)) := by
  apply
    tendsto_normalizedFiniteFunctionalReturnMetricCrossCovariance_of_coefficients
      hcamera endpointMap bulkMap poisson hpoisson hisometry
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredSeventhCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of every compatible centered-seventh
return-metric cross covariance family. -/
theorem
    tendsto_norm_normalizedFiniteCenteredSeventhReturnMetricCrossCovariance_sub
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
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
      ‖normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff camera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSeventhCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredSeventhReturnMetricCrossCovariance
      hz hperiod hcamera hcommon endpointMap bulkMap poisson hpoisson hisometry
  have hconstant :
      Tendsto (fun _ : ℕ => complexSeventhCenteredMomentMatrix period camera)
        atTop (nhds (complexSeventhCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Complex form of the exact documented six-camera seventh centered moment. -/
def complexSixCameraSeventhCenteredMoment : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (sixCameraSeventhCenteredMoment i j : ℂ)

@[simp] theorem complexSeventhCenteredMomentMatrix_sixCamera :
    complexSeventhCenteredMomentMatrix 420 sixCamera =
      complexSixCameraSeventhCenteredMoment := by
  unfold complexSeventhCenteredMomentMatrix
    complexSixCameraSeventhCenteredMoment
  rw [sixCameraSeventhCenteredMoment_eq]

/-- The literal six-camera direct centered-seventh-power covariance converges
in matrix norm to the exact documented seventh centered-moment matrix. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredSeventhDirectCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff sixCamera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff) -
        complexSixCameraSeventhCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexSeventhCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredSeventhDirectCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Exact passage to the six-camera seventh centered-moment limit for every
finite colligation family satisfying the Poisson and Pythagorean identities. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredSeventhReturnMetricCrossCovariance_sub
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
      ‖normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff sixCamera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 7 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSixCameraSeventhCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexSeventhCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredSeventhReturnMetricCrossCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod endpointMap bulkMap poisson hpoisson hisometry)

end

end NativeCarrySpectralWeyl.Limits
