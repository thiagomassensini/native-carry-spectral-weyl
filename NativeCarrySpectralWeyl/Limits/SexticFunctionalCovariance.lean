import NativeCarrySpectralWeyl.Limits.QuinticFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarSixthFunctionalMoment
import Mathlib.Tactic

/-!
# Sextic functional covariance limit

This file connects the sixth scalar resolvent functional moment to the
periodic camera coefficients.  The leading periodic weight
`log(n+1)⁶ w_z(n)` grows like `log(n)⁴`.  It is eventually monotone because it
is the product of the nonnegative monotone logarithm with the eventually
monotone log-fifth weight.  Discrete Abel summation then controls the zero-mean
periodic residue.  The literal boundary is eliminated afterward, yielding
the complete coefficient, direct and compatible return-metric limits.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- Sixth centered logarithmic moment weight. -/
def sixthCenteredMomentWeight (slope : ℕ) : ℝ :=
  Real.log slope ^ 6 + 15 * Real.log slope ^ 4 -
    40 * Real.log slope ^ 3 + 135 * Real.log slope ^ 2 -
      264 * Real.log slope + 265

/-- Sixth centered logarithmic camera moment. -/
def sixthCenteredMomentMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  weightedMomentMatrix period camera sixthCenteredMomentWeight

/-- Source formula
`M₆(i,j) = G(i,j) * (log(ell(i,j))⁶ + 15log(ell(i,j))⁴ -
40log(ell(i,j))³ + 135log(ell(i,j))² - 264log(ell(i,j)) + 265)`. -/
theorem sixthCenteredMomentMatrix_apply {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    sixthCenteredMomentMatrix period camera i j =
      periodicGramMatrix period camera i j *
        (Real.log (slopeOverlap camera i j) ^ 6 +
          15 * Real.log (slopeOverlap camera i j) ^ 4 -
            40 * Real.log (slopeOverlap camera i j) ^ 3 +
              135 * Real.log (slopeOverlap camera i j) ^ 2 -
                264 * Real.log (slopeOverlap camera i j) + 265) := by
  rfl

/-- The sixth centered logarithmic camera moment is Hermitian. -/
theorem sixthCenteredMomentMatrix_isHermitian {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (sixthCenteredMomentMatrix period camera).IsHermitian :=
  weightedMomentMatrix_isHermitian period camera sixthCenteredMomentWeight

/-- The sixth centered logarithmic camera moment is self-adjoint. -/
theorem sixthCenteredMomentMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    IsSelfAdjoint (sixthCenteredMomentMatrix period camera) :=
  (sixthCenteredMomentMatrix_isHermitian period camera).isSelfAdjoint

/-- Literal sixth centered moment for cameras `2, ..., 7`. -/
def sixCameraSixthCenteredMoment : Matrix (Fin 6) (Fin 6) ℝ :=
  !![6 * sixthCenteredMomentWeight 4, 0,
       10 * sixthCenteredMomentWeight 4, 0,
       (16 / 3) * sixthCenteredMomentWeight 4, 0;
     0, 6 * sixthCenteredMomentWeight 3, 0, 0,
       6 * sixthCenteredMomentWeight 3, 0;
     10 * sixthCenteredMomentWeight 4, 0,
       22 * sixthCenteredMomentWeight 4, 0,
       (16 / 3) * sixthCenteredMomentWeight 4, 0;
     0, 0, 0, 20 * sixthCenteredMomentWeight 5, 0, 0;
     (16 / 3) * sixthCenteredMomentWeight 4,
       6 * sixthCenteredMomentWeight 3,
       (16 / 3) * sixthCenteredMomentWeight 4, 0,
       44 * sixthCenteredMomentWeight 6, 0;
     0, 0, 0, 0, 0, 42 * sixthCenteredMomentWeight 7]

/-- Exact recovery of the sixth centered moment for cameras `2, ..., 7`. -/
theorem sixCameraSixthCenteredMoment_eq :
    sixthCenteredMomentMatrix 420 sixCamera = sixCameraSixthCenteredMoment := by
  rw [sixthCenteredMomentMatrix, weightedMomentMatrix, sixCameraGram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraSixthCenteredMoment, slopeWeightMatrix,
      sixthCenteredMomentWeight, slopeOverlap, sixCamera, sixCameraGram,
      sixCameraGramRat, cameraSlope]

/-- The exact six-camera sixth centered moment is self-adjoint. -/
theorem sixCameraSixthCenteredMoment_isSelfAdjoint :
    IsSelfAdjoint sixCameraSixthCenteredMoment := by
  rw [← sixCameraSixthCenteredMoment_eq]
  exact sixthCenteredMomentMatrix_isSelfAdjoint 420 sixCamera

/-- The log-sixth resolvent weight. -/
def resolventLogSixthWeight (z : ℂ) (n : ℕ) : ℝ :=
  Real.log (n + 1) ^ 6 * resolventWeight z n

theorem resolventLogSixthWeight_nonneg {z : ℂ} (hz : z.im ≠ 0)
    (n : ℕ) : 0 ≤ resolventLogSixthWeight z n := by
  exact mul_nonneg (pow_nonneg (Real.log_nonneg (by norm_num)) 6)
    (resolventWeight_pos hz n).le

/-- The log-sixth resolvent weight is eventually monotone. -/
theorem exists_resolventLogSixthWeight_monotone_natAdd
    {z : ℂ} (hz : z.im ≠ 0) :
    ∃ offset : ℕ,
      Monotone (fun n : ℕ => resolventLogSixthWeight z (offset + n)) := by
  obtain ⟨offset, hfifth⟩ :=
    exists_resolventLogFifthWeight_monotone_natAdd hz
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
    resolventLogSixthWeight z (offset + m) =
        Real.log (((offset + m + 1 : ℕ) : ℝ)) *
          resolventLogFifthWeight z (offset + m) := by
            rw [resolventLogSixthWeight, resolventLogFifthWeight]
            norm_num [Nat.cast_add]
            ring
    _ ≤ Real.log (((offset + n + 1 : ℕ) : ℝ)) *
          resolventLogFifthWeight z (offset + n) :=
      mul_le_mul hlog (hfifth hmn)
        (resolventLogFifthWeight_nonneg hz (offset + m)) (hlog0.trans hlog)
    _ = resolventLogSixthWeight z (offset + n) := by
      rw [resolventLogSixthWeight, resolventLogFifthWeight]
      norm_num [Nat.cast_add]
      ring

/-- `log(M+1)⁴ / A_M(z)` tends to zero. -/
theorem tendsto_log_succ_fourth_div_resolventMass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log (cutoff + 1) ^ 4 / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hfourth := tendsto_log_fourth_div_resolventMass_zero hz
  have hcube := tendsto_log_cube_div_resolventMass_zero hz
  have hsq := tendsto_log_sq_div_resolventMass_zero hz
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hstep := Real.tendsto_log_nat_add_one_sub_log
  have hlimit :=
    ((((hfourth.add ((hstep.mul hcube).const_mul 4)).add
      (((hstep.pow 2).mul hsq).const_mul 6)).add
        (((hstep.pow 3).mul hlog).const_mul 4)).add
          ((hstep.pow 4).mul hinvMass))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 4 / resolventMass z cutoff +
        4 * ((Real.log (cutoff + 1) - Real.log cutoff) *
          (Real.log cutoff ^ 3 / resolventMass z cutoff)) +
        6 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          (Real.log cutoff ^ 2 / resolventMass z cutoff)) +
        4 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          (Real.log cutoff / resolventMass z cutoff)) +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

/-- The log-sixth endpoint weight is negligible relative to resolvent mass. -/
theorem tendsto_resolventLogSixthWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogSixthWeight z cutoff / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hproduct := (tendsto_log_succ_fourth_div_resolventMass_zero hz).mul
    (tendsto_resolventLogSqWeight_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) ^ 4 / resolventMass z cutoff) *
        resolventLogSqWeight z cutoff) atTop (nhds 0) := by
    simpa only [zero_mul] using hproduct
  apply hlimit.congr'
  filter_upwards with cutoff
  rw [resolventLogSixthWeight, resolventLogSqWeight]
  ring

theorem tendsto_resolventLogSixth_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff,
        resolventLogSixthWeight z n * q n) / resolventMass z cutoff)
      atTop (nhds 0) := by
  apply tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
    hperiod hq hsum
  · exact resolventLogSixthWeight_nonneg hz
  · exact exists_resolventLogSixthWeight_monotone_natAdd hz
  · exact (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
  · exact tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  · exact tendsto_resolventLogSixthWeight_div_mass_zero hz

/-- The logarithmic mean times the log-fifth endpoint weight is negligible
relative to resolvent mass. -/
theorem tendsto_resolventLogMean_mul_resolventLogFifthWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff * resolventLogFifthWeight z cutoff /
        resolventMass z cutoff) atTop (nhds 0) := by
  have hproduct := (tendsto_resolventLogMean_div_log_succ_one hz).mul
    (tendsto_resolventLogSixthWeight_div_mass_zero hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / Real.log (cutoff + 1)) *
        (resolventLogSixthWeight z cutoff / resolventMass z cutoff))
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
  rw [resolventLogSixthWeight, resolventLogFifthWeight]
  field_simp [hlog]

/-- A zero-mean log-fifth periodic sum remains negligible after multiplication
by the logarithmic mean. -/
theorem tendsto_resolventLogMean_mul_resolventLogFifth_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range cutoff,
          resolventLogFifthWeight z n * q n)
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
      resolventLogFifthWeight z cutoff / modifiedMass cutoff)
      atTop (nhds 0) := by
    have h :=
      tendsto_resolventLogMean_mul_resolventLogFifthWeight_div_mass_zero hz
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

/-- The square of the logarithmic mean times the log-fourth endpoint weight is
negligible relative to resolvent mass. -/
theorem tendsto_resolventLogMean_sq_mul_resolventLogFourthWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 2 * resolventLogFourthWeight z cutoff /
        resolventMass z cutoff) atTop (nhds 0) := by
  have hproduct := (tendsto_resolventLogMean_div_log_succ_one hz).pow 2 |>.mul
    (tendsto_resolventLogSixthWeight_div_mass_zero hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / Real.log (cutoff + 1)) ^ 2 *
        (resolventLogSixthWeight z cutoff / resolventMass z cutoff))
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
  rw [resolventLogSixthWeight, resolventLogFourthWeight]
  field_simp [hlog]

/-- A zero-mean log-fourth periodic sum remains negligible after multiplication
by the square of the logarithmic mean. -/
theorem tendsto_resolventLogMean_sq_mul_resolventLogFourth_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range cutoff,
          resolventLogFourthWeight z n * q n)
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
      resolventLogFourthWeight z cutoff / modifiedMass cutoff)
      atTop (nhds 0) := by
    have h :=
      tendsto_resolventLogMean_sq_mul_resolventLogFourthWeight_div_mass_zero hz
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

/-- The cube of the logarithmic mean times the log-cubic endpoint weight is
negligible relative to resolvent mass. -/
theorem tendsto_resolventLogMean_cube_mul_resolventLogCubeWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 3 * resolventLogCubeWeight z cutoff /
        resolventMass z cutoff) atTop (nhds 0) := by
  have hproduct := (tendsto_resolventLogMean_div_log_succ_one hz).pow 3 |>.mul
    (tendsto_resolventLogSixthWeight_div_mass_zero hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / Real.log (cutoff + 1)) ^ 3 *
        (resolventLogSixthWeight z cutoff / resolventMass z cutoff))
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
  rw [resolventLogSixthWeight, resolventLogCubeWeight]
  field_simp [hlog]

/-- A zero-mean log-cubic periodic sum remains negligible after multiplication
by the cube of the logarithmic mean. -/
theorem tendsto_resolventLogMean_cube_mul_resolventLogCube_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 3 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range cutoff,
          resolventLogCubeWeight z n * q n)
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
      resolventLogCubeWeight z cutoff / modifiedMass cutoff)
      atTop (nhds 0) := by
    have h :=
      tendsto_resolventLogMean_cube_mul_resolventLogCubeWeight_div_mass_zero hz
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

/-- `log(M)⁶ / A_M(z)` tends to zero. -/
theorem tendsto_log_sixth_div_resolventMass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 6 / resolventMass z cutoff) atTop (nhds 0) := by
  have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
      atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hocticSuccBase : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 8 / ((cutoff : ℝ) + 1))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 8 one_ne_zero).comp hcastSucc
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
  have hocticSucc : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 8 / cutoff) atTop (nhds 0) := by
    have h := hocticSuccBase.mul hsuccRatio
    have h' : Tendsto (fun cutoff : ℕ =>
        (Real.log ((cutoff : ℝ) + 1) ^ 8 / ((cutoff : ℝ) + 1)) *
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
      Real.log cutoff ^ 6 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      exact div_nonneg
        (mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hcutoff)) 6)
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
          Real.log (cutoff : ℝ) ^ 6 *
              Real.log ((cutoff : ℝ) + 1) ^ 2 ≤
            Real.log ((cutoff : ℝ) + 1) ^ 6 *
              Real.log ((cutoff : ℝ) + 1) ^ 2 := by
                gcongr
          _ = Real.log ((cutoff : ℝ) + 1) ^ 8 := by ring) hcutoffPos.le
    · exact hocticSucc
  have hmassRatio := tendsto_resolventMass_div_nat_div_log_sq_one hz
  have hmassRatioInv := hmassRatio.inv₀ (by norm_num)
  have hproduct := hlogFactor.mul hmassRatioInv
  have hproduct' : Tendsto (fun cutoff : ℕ =>
      (Real.log cutoff ^ 6 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff) *
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

/-- The sixth power of the resolvent logarithmic mean is negligible relative
to resolvent mass. -/
theorem tendsto_resolventLogMean_sixth_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 6 / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hlogSixth := tendsto_log_sixth_div_resolventMass_zero hz
  have hdelta := tendsto_resolventLogMean_sub_log hz
  have hlogFifth := tendsto_log_fifth_div_resolventMass_zero hz
  have hlogFourth := tendsto_log_fourth_div_resolventMass_zero hz
  have hlogCube := tendsto_log_cube_div_resolventMass_zero hz
  have hlogSq := tendsto_log_sq_div_resolventMass_zero hz
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hlimit :=
    ((((((hlogSixth.add ((hdelta.mul hlogFifth).const_mul 6)).add
      (((hdelta.pow 2).mul hlogFourth).const_mul 15)).add
        (((hdelta.pow 3).mul hlogCube).const_mul 20)).add
          (((hdelta.pow 4).mul hlogSq).const_mul 15)).add
            (((hdelta.pow 5).mul hlog).const_mul 6)).add
              ((hdelta.pow 6).mul hinvMass))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 6 / resolventMass z cutoff +
        6 * ((resolventLogMean z cutoff - Real.log cutoff) *
          (Real.log cutoff ^ 5 / resolventMass z cutoff)) +
        15 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 2 *
          (Real.log cutoff ^ 4 / resolventMass z cutoff)) +
        20 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 3 *
          (Real.log cutoff ^ 3 / resolventMass z cutoff)) +
        15 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 4 *
          (Real.log cutoff ^ 2 / resolventMass z cutoff)) +
        6 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 5 *
          (Real.log cutoff / resolventMass z cutoff)) +
        (resolventLogMean z cutoff - Real.log cutoff) ^ 6 *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

theorem tendsto_resolventCenteredLogSixth_periodicResidue_zero
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 *
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
  have hsixthBase :=
    tendsto_resolventLogSixth_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hsixthAtScale := hsixthBase.comp hscaleTop
  have hsixthAtScale' : Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff),
        resolventLogSixthWeight z n * centered n) /
          resolventMass z (scale * cutoff)) atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff),
        resolventLogSixthWeight z n * centered n) /
          resolventMass z (scale * cutoff)) atTop (nhds 0) at hsixthAtScale
    exact hsixthAtScale
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hsixthProduct := hsixthAtScale'.mul hmassRatio
  have hsixthPart : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSixthWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSixthWeight z n * centered n) /
          resolventMass z (scale * cutoff)) *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hsixthProduct
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
  have hfifthBase :=
    tendsto_resolventLogMean_mul_resolventLogFifth_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hfifthAtScale := hfifthBase.comp hscaleTop
  have hfifthAtScale' : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFifthWeight z n * centered n)
      atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFifthWeight z n * centered n)
      atTop (nhds 0) at hfifthAtScale
    exact hfifthAtScale
  have hmeanRatio := tendsto_resolventLogMean_nat_mul_div hz hscale
  have hmeanRatioInv := hmeanRatio.inv₀ (by norm_num)
  have hfifthProduct := (hfifthAtScale'.mul hmeanRatioInv).mul hmassRatio
  have hfifthPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFifthWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((resolventLogMean z (scale * cutoff) /
            resolventMass z (scale * cutoff)) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFifthWeight z n * centered n) *
        (resolventLogMean z (scale * cutoff) /
          resolventLogMean z cutoff)⁻¹ *
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
    tendsto_resolventLogMean_sq_mul_resolventLogFourth_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hfourthAtScale := hfourthBase.comp hscaleTop
  have hfourthAtScale' : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 2 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFourthWeight z n * centered n)
      atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 2 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFourthWeight z n * centered n)
      atTop (nhds 0) at hfourthAtScale
    exact hfourthAtScale
  have hmeanRatioSqInv := hmeanRatioInv.pow 2
  have hfourthProduct := (hfourthAtScale'.mul hmeanRatioSqInv).mul hmassRatio
  have hfourthPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFourthWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((resolventLogMean z (scale * cutoff) ^ 2 /
            resolventMass z (scale * cutoff)) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFourthWeight z n * centered n) *
        (resolventLogMean z (scale * cutoff) /
          resolventLogMean z cutoff)⁻¹ ^ 2 *
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
  have hcubeBase :=
    tendsto_resolventLogMean_cube_mul_resolventLogCube_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hcubeAtScale := hcubeBase.comp hscaleTop
  have hcubeAtScale' : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 3 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) ^ 3 /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) at hcubeAtScale
    exact hcubeAtScale
  have hmeanRatioCubeInv := hmeanRatioInv.pow 3
  have hcubeProduct := (hcubeAtScale'.mul hmeanRatioCubeInv).mul hmassRatio
  have hcubePart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 3 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((resolventLogMean z (scale * cutoff) ^ 3 /
            resolventMass z (scale * cutoff)) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogCubeWeight z n * centered n) *
        (resolventLogMean z (scale * cutoff) /
          resolventLogMean z cutoff)⁻¹ ^ 3 *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hcubeProduct
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
      15 * resolventLogMean z cutoff ^ 4 / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_fourth_div_mass_zero hz).const_mul 15
    simpa only [mul_div_assoc, mul_zero] using h
  have hquadraticPart : Tendsto (fun cutoff : ℕ =>
      (15 * resolventLogMean z cutoff ^ 4 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSqWeight z n * centered n) atTop (nhds 0) :=
    hquadraticCoefficient.zero_mul_isBoundedUnder_le hlogSqWeightScaled
  have hlinearCoefficient : Tendsto (fun cutoff : ℕ =>
      6 * resolventLogMean z cutoff ^ 5 / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_fifth_div_mass_zero hz).const_mul 6
    simpa only [mul_div_assoc, mul_zero] using h
  have hlinearPart : Tendsto (fun cutoff : ℕ =>
      (6 * resolventLogMean z cutoff ^ 5 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n) atTop (nhds 0) :=
    hlinearCoefficient.zero_mul_isBoundedUnder_le hlogWeightScaled
  have hconstantPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 6 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n * centered n) atTop (nhds 0) :=
    (tendsto_resolventLogMean_sixth_div_mass_zero hz).zero_mul_isBoundedUnder_le
      hweightScaled
  have hlimit :=
    (((((hsixthPart.sub (hfifthPart.const_mul 6)).add
      (hfourthPart.const_mul 15)).sub (hcubePart.const_mul 20)).add
        hquadraticPart).sub hlinearPart).add hconstantPart
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSixthWeight z n * centered n -
        6 * ((resolventLogMean z cutoff / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFifthWeight z n * centered n) +
        15 * ((resolventLogMean z cutoff ^ 2 /
            resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFourthWeight z n * centered n) -
        20 * ((resolventLogMean z cutoff ^ 3 /
            resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogCubeWeight z n * centered n) +
        (15 * resolventLogMean z cutoff ^ 4 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSqWeight z n * centered n -
        (6 * resolventLogMean z cutoff ^ 5 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogWeight z n * centered n +
        (resolventLogMean z cutoff ^ 6 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n * centered n) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 * centered n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSixthWeight z n * centered n) -
          6 * resolventLogMean z cutoff *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogFifthWeight z n * centered n +
          15 * resolventLogMean z cutoff ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogFourthWeight z n * centered n -
          20 * resolventLogMean z cutoff ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogCubeWeight z n * centered n +
          15 * resolventLogMean z cutoff ^ 4 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogSqWeight z n * centered n -
          6 * resolventLogMean z cutoff ^ 5 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogWeight z n * centered n +
          resolventLogMean z cutoff ^ 6 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventWeight z n * centered n := by
    calc
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 * centered n) =
        ∑ n ∈ Finset.range (scale * cutoff),
          (resolventLogSixthWeight z n * centered n -
            6 * resolventLogMean z cutoff *
              (resolventLogFifthWeight z n * centered n) +
            15 * resolventLogMean z cutoff ^ 2 *
              (resolventLogFourthWeight z n * centered n) -
            20 * resolventLogMean z cutoff ^ 3 *
              (resolventLogCubeWeight z n * centered n) +
            15 * resolventLogMean z cutoff ^ 4 *
              (resolventLogSqWeight z n * centered n) -
            6 * resolventLogMean z cutoff ^ 5 *
              (resolventLogWeight z n * centered n) +
            resolventLogMean z cutoff ^ 6 *
              (resolventWeight z n * centered n)) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [resolventLogSixthWeight, resolventLogFifthWeight,
            resolventLogFourthWeight,
            resolventLogCubeWeight, resolventLogSqWeight, resolventLogWeight]
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp_rw [← Finset.mul_sum]
  rw [hsum]
  ring

/-- Periodic averaging for the sixth centered logarithmic resolvent moment. -/
theorem tendsto_resolventCenteredLogSixth_periodicWeightedSum
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 * q n)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 6 + 15 * Real.log scale ^ 4 -
          40 * Real.log scale ^ 3 + 135 * Real.log scale ^ 2 -
            264 * Real.log scale + 265)) *
            periodMean q period)) := by
  have hscalar :=
    tendsto_resolventScaledCenteredLogSixthMoment_div_mass hz hscale
  have hmain : Tendsto (fun cutoff : ℕ =>
      (resolventScaledCenteredLogSixthMoment z scale cutoff /
        resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 6 + 15 * Real.log scale ^ 4 -
          40 * Real.log scale ^ 3 + 135 * Real.log scale ^ 2 -
            264 * Real.log scale + 265)) *
            periodMean q period)) :=
    hscalar.mul_const (periodMean q period)
  have hresidue := tendsto_resolventCenteredLogSixth_periodicResidue_zero
    hz hperiod hscale hq
  have hlimit := hresidue.add hmain
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 *
                (q n - periodMean q period) +
        (resolventScaledCenteredLogSixthMoment z scale cutoff /
          resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 6 + 15 * Real.log scale ^ 4 -
          40 * Real.log scale ^ 3 + 135 * Real.log scale ^ 2 -
            264 * Real.log scale + 265)) *
            periodMean q period)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 * q n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 *
              (q n - periodMean q period)) +
          periodMean q period *
            resolventScaledCenteredLogSixthMoment z scale cutoff := by
    rw [resolventScaledCenteredLogSixthMoment, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsum]
  ring

/-- The shifted periodic camera core with the centered sixth-power multiplier
converges entrywise to the sixth centered moment. -/
theorem tendsto_resolvent_shiftedCoreSixthFunctional_apply
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
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 *
              realProfileProduct (camera i) (camera j) (n + 1))
      atTop (nhds (sixthCenteredMomentMatrix period camera i j)) := by
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
  have hlimit := tendsto_resolventCenteredLogSixth_periodicWeightedSum
    hz hperiod hscale hq
  rw [hmean] at hlimit
  have htarget :
      (((scale : ℝ) *
          (Real.log scale ^ 6 + 15 * Real.log scale ^ 4 -
            40 * Real.log scale ^ 3 + 135 * Real.log scale ^ 2 -
              264 * Real.log scale + 265)) *
          periodicProductMean period (camera i) (camera j)) =
        sixthCenteredMomentMatrix period camera i j := by
    rw [sixthCenteredMomentMatrix_apply, periodicGramMatrix_apply]
    simp only [slopeOverlap, scale]
    ring
  rw [htarget] at hlimit
  simpa only [pairCoreLength, scale, q] using hlimit

/-- Sixth-power multiplier in the finite centered logarithmic coordinate. -/
def centeredSixthMultiplier (z : ℂ) (cutoff n : ℕ) : ℝ :=
  (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6

/-- Product of the resolvent weight with the centered sixth-power
multiplier. -/
def resolventCenteredSixthWeight (z : ℂ) (cutoff n : ℕ) : ℝ :=
  resolventWeight z n * centeredSixthMultiplier z cutoff n

@[simp] theorem centeredPolynomialMultiplier_X_sixth
    (z : ℂ) (cutoff n : ℕ) :
    centeredPolynomialMultiplier (Polynomial.X ^ 6) z cutoff n =
      centeredSixthMultiplier z cutoff n := by
  simp [centeredPolynomialMultiplier, centeredSixthMultiplier]

/-- Every fixed literal seed/endpoint term vanishes for the centered
sixth-power functional weight. -/
theorem tendsto_resolventCenteredSixth_finiteBoundaryTerm_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (r : ℕ) :
    Tendsto (fun cutoff =>
      finiteBoundaryTerm (resolventCenteredSixthWeight z cutoff)
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
  have hfifth :=
    tendsto_resolventCenteredFifth_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r
  have hproduct := hcoordinate.mul hfifth
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (scale * cutoff + r + 1) - resolventLogMean z cutoff) *
        finiteBoundaryTerm (resolventCenteredFifthWeight z cutoff)
          cutoff camera₁ camera₂ r) atTop (nhds 0) := by
    simpa only [mul_zero] using hproduct
  apply hlimit.congr'
  filter_upwards with cutoff
  rw [finiteBoundaryTerm, finiteBoundaryTerm]
  split_ifs
  · rw [resolventCenteredSixthWeight, centeredSixthMultiplier,
      resolventCenteredFifthWeight, centeredFifthMultiplier]
    simp only [pairCoreLength, scale]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  · ring

/-- The complete fixed-width literal boundary vanishes for the centered
sixth-power functional weight. -/
theorem tendsto_resolventCenteredSixth_finiteBoundarySum_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) :
    Tendsto (fun cutoff =>
      finiteBoundarySum (resolventCenteredSixthWeight z cutoff)
        cutoff camera₁ camera₂) atTop (nhds 0) := by
  have hsum := tendsto_finsetSum
    (Finset.range (pairBoundaryWidth camera₁ camera₂))
    (fun r _ => tendsto_resolventCenteredSixth_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r)
  simpa only [finiteBoundarySum, Finset.sum_const_zero] using hsum

/-- Entrywise convergence of the complete literal centered-sixth-power
coefficient covariance to the sixth centered camera moment. -/
theorem tendsto_finiteCenteredSixthCoefficientCovariance_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff camera i j)
      atTop (nhds (sixthCenteredMomentMatrix period camera i j)) := by
  have hcore := tendsto_resolvent_shiftedCoreSixthFunctional_apply
    hz hperiod hcamera hcommon i j
  have hboundary := tendsto_resolventCenteredSixth_finiteBoundarySum_zero
    hz (hcamera i) (hcamera j)
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hboundaryNormalized : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        finiteBoundarySum (resolventCenteredSixthWeight z cutoff)
          cutoff (camera i) (camera j)) atTop (nhds 0) := by
    simpa only [zero_mul] using hinvMass.mul hboundary
  have hlimit := hcore.add hboundaryNormalized
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range
              (pairCoreLength (camera i) (camera j) cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 *
                realProfileProduct (camera i) (camera j) (n + 1) +
        (resolventMass z cutoff)⁻¹ *
          finiteBoundarySum (resolventCenteredSixthWeight z cutoff)
            cutoff (camera i) (camera j))
      atTop (nhds (sixthCenteredMomentMatrix period camera i j)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  rw [finiteCenteredPolynomialCoefficientCovariance,
    finiteFunctionalCoefficientCovariance]
  simp only [centeredPolynomialMultiplier_X_sixth]
  have hnum :
      (∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventWeight z n * centeredSixthMultiplier z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n) =
        ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventCenteredSixthWeight z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredSixthWeight]
  rw [hnum]
  rw [finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary
    (weight := resolventCenteredSixthWeight z cutoff)
      (hcamera i) (hcamera j)]
  have hcoreEq :
      (∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventCenteredSixthWeight z cutoff n *
            realProfileProduct (camera i) (camera j) (n + 1)) =
        ∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 *
              realProfileProduct (camera i) (camera j) (n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredSixthWeight, centeredSixthMultiplier]
  rw [hcoreEq]
  simp only [resolventMass]
  ring

/-- Matrix convergence of the complete literal centered-sixth-power
coefficient covariance. -/
theorem tendsto_finiteCenteredSixthCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff camera)
      atTop (nhds (sixthCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff camera i j)
    atTop (nhds fun i j => sixthCenteredMomentMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_finiteCenteredSixthCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j

/-- Finite entry-sup norm convergence of the literal centered-sixth-power
coefficient covariance. -/
theorem tendsto_norm_finiteCenteredSixthCoefficientCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff camera -
        sixthCenteredMomentMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_finiteCenteredSixthCoefficientCovariance
    hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => sixthCenteredMomentMatrix period camera)
        atTop (nhds (sixthCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- The literal six-camera centered-sixth-power covariance converges to the
exact documented matrix `sixCameraSixthCenteredMoment`. -/
theorem
    tendsto_norm_sixCamera_finiteCenteredSixthCoefficientCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff sixCamera -
        sixCameraSixthCenteredMoment‖) atTop (nhds 0) := by
  rw [← sixCameraSixthCenteredMoment_eq]
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  exact tendsto_norm_finiteCenteredSixthCoefficientCovariance_sub
    hz (by norm_num : 0 < 420) hcamera sixCamera_commonPeriod

/-- Complexification of the sixth centered periodic camera moment. -/
def complexSixthCenteredMomentMatrix {index : Type*} (period : ℕ)
    (camera : index → ℕ) : Matrix index index ℂ :=
  fun i j => (sixthCenteredMomentMatrix period camera i j : ℂ)

/-- Complexified convergence of the complete literal centered-sixth-power
coefficient covariance. -/
theorem tendsto_complex_finiteCenteredSixthCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff i j =>
      (finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff camera i j : ℂ))
      atTop (nhds (complexSixthCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    (finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff camera i j : ℂ))
    atTop (nhds fun i j =>
      (sixthCenteredMomentMatrix period camera i j : ℂ))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hreal := tendsto_finiteCenteredSixthCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j
  exact (Complex.continuous_ofReal.tendsto
    (sixthCenteredMomentMatrix period camera i j)).comp hreal

/-- The normalized direct finite functional covariance for the centered
sixth-power multiplier converges to the complexified sixth centered
moment. -/
theorem tendsto_normalizedFiniteCenteredSixthDirectCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalDirectCovariance z cutoff camera
        (centeredPolynomialMultiplier
          (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff))
      atTop (nhds (complexSixthCenteredMomentMatrix period camera)) := by
  apply tendsto_normalizedFiniteFunctionalDirectCovariance_of_coefficients
    hcamera
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredSixthCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of the normalized direct
centered-sixth-power functional covariance. -/
theorem tendsto_norm_normalizedFiniteCenteredSixthDirectCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff camera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff) -
        complexSixthCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredSixthDirectCovariance
      hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => complexSixthCenteredMomentMatrix period camera)
        atTop (nhds (complexSixthCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Every compatible finite return-metric colligation family inherits the
centered sixth-moment limit. -/
theorem tendsto_normalizedFiniteCenteredSixthReturnMetricCrossCovariance
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
          (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff)
        (endpointMap cutoff) (poisson cutoff))
      atTop (nhds (complexSixthCenteredMomentMatrix period camera)) := by
  apply
    tendsto_normalizedFiniteFunctionalReturnMetricCrossCovariance_of_coefficients
      hcamera endpointMap bulkMap poisson hpoisson hisometry
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredSixthCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of every compatible centered-sixth
return-metric cross covariance family. -/
theorem
    tendsto_norm_normalizedFiniteCenteredSixthReturnMetricCrossCovariance_sub
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
            (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSixthCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredSixthReturnMetricCrossCovariance
      hz hperiod hcamera hcommon endpointMap bulkMap poisson hpoisson hisometry
  have hconstant :
      Tendsto (fun _ : ℕ => complexSixthCenteredMomentMatrix period camera)
        atTop (nhds (complexSixthCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Complex form of the exact documented six-camera sixth centered moment. -/
def complexSixCameraSixthCenteredMoment : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (sixCameraSixthCenteredMoment i j : ℂ)

@[simp] theorem complexSixthCenteredMomentMatrix_sixCamera :
    complexSixthCenteredMomentMatrix 420 sixCamera =
      complexSixCameraSixthCenteredMoment := by
  unfold complexSixthCenteredMomentMatrix
    complexSixCameraSixthCenteredMoment
  rw [sixCameraSixthCenteredMoment_eq]

/-- The literal six-camera direct centered-sixth-power covariance converges
in matrix norm to the exact documented sixth centered-moment matrix. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredSixthDirectCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff sixCamera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff) -
        complexSixCameraSixthCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexSixthCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredSixthDirectCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Exact passage to the six-camera sixth centered-moment limit for every
finite colligation family satisfying the Poisson and Pythagorean identities. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredSixthReturnMetricCrossCovariance_sub
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
            (Polynomial.X ^ 6 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSixCameraSixthCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexSixthCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredSixthReturnMetricCrossCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod endpointMap bulkMap poisson hpoisson hisometry)

end

end NativeCarrySpectralWeyl.Limits
