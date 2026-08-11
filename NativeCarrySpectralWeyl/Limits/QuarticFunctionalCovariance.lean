import NativeCarrySpectralWeyl.Limits.CubicFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarFourthFunctionalMoment
import Mathlib.Tactic

/-!
# Quartic functional covariance limit

This file connects the fourth scalar resolvent functional moment to the
periodic camera coefficients.  The leading periodic weight
`log(n+1)⁴ w_z(n)` grows like `log(n)²`.  It is eventually monotone because it
is the product of the nonnegative monotone logarithm with the eventually
monotone cubic weight.  Discrete Abel summation then controls the zero-mean
periodic residue.  The literal boundary is eliminated afterward, yielding
the complete coefficient, direct and compatible return-metric limits.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- Fourth centered logarithmic moment weight. -/
def fourthCenteredMomentWeight (slope : ℕ) : ℝ :=
  Real.log slope ^ 4 + 6 * Real.log slope ^ 2 - 8 * Real.log slope + 9

/-- Fourth centered logarithmic camera moment `L`. -/
def fourthCenteredMomentMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  weightedMomentMatrix period camera fourthCenteredMomentWeight

/-- Source formula
`L(i,j) = G(i,j) * (log(ell(i,j))⁴ + 6log(ell(i,j))² -
8log(ell(i,j)) + 9)`. -/
theorem fourthCenteredMomentMatrix_apply {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    fourthCenteredMomentMatrix period camera i j =
      periodicGramMatrix period camera i j *
        (Real.log (slopeOverlap camera i j) ^ 4 +
          6 * Real.log (slopeOverlap camera i j) ^ 2 -
            8 * Real.log (slopeOverlap camera i j) + 9) := by
  rfl

/-- The fourth centered logarithmic camera moment is Hermitian. -/
theorem fourthCenteredMomentMatrix_isHermitian {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (fourthCenteredMomentMatrix period camera).IsHermitian :=
  weightedMomentMatrix_isHermitian period camera fourthCenteredMomentWeight

/-- The fourth centered logarithmic camera moment is self-adjoint. -/
theorem fourthCenteredMomentMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    IsSelfAdjoint (fourthCenteredMomentMatrix period camera) :=
  (fourthCenteredMomentMatrix_isHermitian period camera).isSelfAdjoint

/-- Literal fourth centered moment for cameras `2, ..., 7`. -/
def sixCameraFourthCenteredMoment : Matrix (Fin 6) (Fin 6) ℝ :=
  !![6 * (Real.log 4 ^ 4 + 6 * Real.log 4 ^ 2 - 8 * Real.log 4 + 9), 0,
       10 * (Real.log 4 ^ 4 + 6 * Real.log 4 ^ 2 - 8 * Real.log 4 + 9), 0,
       (16 / 3) *
         (Real.log 4 ^ 4 + 6 * Real.log 4 ^ 2 - 8 * Real.log 4 + 9), 0;
     0, 6 * (Real.log 3 ^ 4 + 6 * Real.log 3 ^ 2 - 8 * Real.log 3 + 9), 0, 0,
       6 * (Real.log 3 ^ 4 + 6 * Real.log 3 ^ 2 - 8 * Real.log 3 + 9), 0;
     10 * (Real.log 4 ^ 4 + 6 * Real.log 4 ^ 2 - 8 * Real.log 4 + 9), 0,
       22 * (Real.log 4 ^ 4 + 6 * Real.log 4 ^ 2 - 8 * Real.log 4 + 9), 0,
       (16 / 3) *
         (Real.log 4 ^ 4 + 6 * Real.log 4 ^ 2 - 8 * Real.log 4 + 9), 0;
     0, 0, 0,
       20 * (Real.log 5 ^ 4 + 6 * Real.log 5 ^ 2 - 8 * Real.log 5 + 9), 0, 0;
     (16 / 3) *
         (Real.log 4 ^ 4 + 6 * Real.log 4 ^ 2 - 8 * Real.log 4 + 9),
       6 * (Real.log 3 ^ 4 + 6 * Real.log 3 ^ 2 - 8 * Real.log 3 + 9),
       (16 / 3) *
         (Real.log 4 ^ 4 + 6 * Real.log 4 ^ 2 - 8 * Real.log 4 + 9), 0,
       44 * (Real.log 6 ^ 4 + 6 * Real.log 6 ^ 2 - 8 * Real.log 6 + 9), 0;
     0, 0, 0, 0, 0,
       42 * (Real.log 7 ^ 4 + 6 * Real.log 7 ^ 2 - 8 * Real.log 7 + 9)]

/-- Exact recovery of the fourth centered moment for cameras `2, ..., 7`. -/
theorem sixCameraFourthCenteredMoment_eq :
    fourthCenteredMomentMatrix 420 sixCamera = sixCameraFourthCenteredMoment := by
  rw [fourthCenteredMomentMatrix, weightedMomentMatrix, sixCameraGram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraFourthCenteredMoment, slopeWeightMatrix,
      fourthCenteredMomentWeight, slopeOverlap, sixCamera, sixCameraGram,
      sixCameraGramRat, cameraSlope]

/-- The exact six-camera fourth centered moment is self-adjoint. -/
theorem sixCameraFourthCenteredMoment_isSelfAdjoint :
    IsSelfAdjoint sixCameraFourthCenteredMoment := by
  rw [← sixCameraFourthCenteredMoment_eq]
  exact fourthCenteredMomentMatrix_isSelfAdjoint 420 sixCamera

/-- The log-fourth resolvent weight. -/
def resolventLogFourthWeight (z : ℂ) (n : ℕ) : ℝ :=
  Real.log (n + 1) ^ 4 * resolventWeight z n

theorem resolventLogFourthWeight_nonneg {z : ℂ} (hz : z.im ≠ 0)
    (n : ℕ) : 0 ≤ resolventLogFourthWeight z n := by
  exact mul_nonneg (pow_nonneg (Real.log_nonneg (by norm_num)) 4)
    (resolventWeight_pos hz n).le

/-- The log-fourth resolvent weight is eventually monotone. -/
theorem exists_resolventLogFourthWeight_monotone_natAdd
    {z : ℂ} (hz : z.im ≠ 0) :
    ∃ offset : ℕ,
      Monotone (fun n : ℕ => resolventLogFourthWeight z (offset + n)) := by
  obtain ⟨offset, hcube⟩ :=
    exists_resolventLogCubeWeight_monotone_natAdd hz
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
    resolventLogFourthWeight z (offset + m) =
        Real.log (((offset + m + 1 : ℕ) : ℝ)) *
          resolventLogCubeWeight z (offset + m) := by
            rw [resolventLogFourthWeight, resolventLogCubeWeight]
            norm_num [Nat.cast_add]
            ring
    _ ≤ Real.log (((offset + n + 1 : ℕ) : ℝ)) *
          resolventLogCubeWeight z (offset + n) :=
      mul_le_mul hlog (hcube hmn)
        (resolventLogCubeWeight_nonneg hz (offset + m)) (hlog0.trans hlog)
    _ = resolventLogFourthWeight z (offset + n) := by
      rw [resolventLogFourthWeight, resolventLogCubeWeight]
      norm_num [Nat.cast_add]
      ring

/-- `log(M+1)² / A_M(z)` tends to zero. -/
theorem tendsto_log_succ_sq_div_resolventMass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log (cutoff + 1) ^ 2 / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hsq := tendsto_log_sq_div_resolventMass_zero hz
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hstep := Real.tendsto_log_nat_add_one_sub_log
  have hlimit :=
    (hsq.add (((hstep.mul hlog).const_mul 2))).add
      ((hstep.pow 2).mul hinvMass)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 2 / resolventMass z cutoff +
        2 * ((Real.log (cutoff + 1) - Real.log cutoff) *
          (Real.log cutoff / resolventMass z cutoff)) +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

/-- The log-fourth endpoint weight is negligible relative to resolvent mass. -/
theorem tendsto_resolventLogFourthWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogFourthWeight z cutoff / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hproduct := (tendsto_log_succ_sq_div_resolventMass_zero hz).mul
    (tendsto_resolventLogSqWeight_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) ^ 2 / resolventMass z cutoff) *
        resolventLogSqWeight z cutoff) atTop (nhds 0) := by
    simpa only [zero_mul] using hproduct
  apply hlimit.congr'
  filter_upwards with cutoff
  rw [resolventLogFourthWeight, resolventLogSqWeight]
  ring

theorem tendsto_resolventLogFourth_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff,
        resolventLogFourthWeight z n * q n) / resolventMass z cutoff)
      atTop (nhds 0) := by
  apply tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
    hperiod hq hsum
  · exact resolventLogFourthWeight_nonneg hz
  · exact exists_resolventLogFourthWeight_monotone_natAdd hz
  · exact (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
  · exact tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  · exact tendsto_resolventLogFourthWeight_div_mass_zero hz

/-- The resolvent logarithmic mean times the log-cubic endpoint weight is
negligible relative to resolvent mass. -/
theorem tendsto_resolventLogMean_mul_resolventLogCubeWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff * resolventLogCubeWeight z cutoff /
        resolventMass z cutoff) atTop (nhds 0) := by
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hlogSq := tendsto_log_sq_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hstep := Real.tendsto_log_nat_add_one_sub_log
  have hlogSucc : Tendsto (fun cutoff : ℕ =>
      Real.log (cutoff + 1) / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := hlog.add (hstep.mul hinvMass)
    have h' : Tendsto (fun cutoff : ℕ =>
        Real.log cutoff / resolventMass z cutoff +
          (Real.log (cutoff + 1) - Real.log cutoff) *
            (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards with cutoff
    ring
  have hlogLogSucc : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff * Real.log (cutoff + 1) /
        resolventMass z cutoff) atTop (nhds 0) := by
    have h := hlogSq.add (hstep.mul hlog)
    have h' : Tendsto (fun cutoff : ℕ =>
        Real.log cutoff ^ 2 / resolventMass z cutoff +
          (Real.log (cutoff + 1) - Real.log cutoff) *
            (Real.log cutoff / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards with cutoff
    ring
  have hdelta := tendsto_resolventLogMean_sub_log hz
  have hmeanLogSucc : Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff * Real.log (cutoff + 1) /
        resolventMass z cutoff) atTop (nhds 0) := by
    have h := (hdelta.mul hlogSucc).add hlogLogSucc
    have h' : Tendsto (fun cutoff : ℕ =>
        (resolventLogMean z cutoff - Real.log cutoff) *
            (Real.log (cutoff + 1) / resolventMass z cutoff) +
          Real.log cutoff * Real.log (cutoff + 1) /
            resolventMass z cutoff) atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards with cutoff
    ring
  have hproduct := hmeanLogSucc.mul
    (tendsto_resolventLogSqWeight_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff * Real.log (cutoff + 1) /
          resolventMass z cutoff) * resolventLogSqWeight z cutoff)
      atTop (nhds 0) := by
    simpa only [zero_mul] using hproduct
  apply hlimit.congr'
  filter_upwards with cutoff
  rw [resolventLogCubeWeight, resolventLogSqWeight]
  ring

/-- A zero-mean log-cubic periodic sum remains negligible after multiplication
by the logarithmic mean. -/
theorem tendsto_resolventLogMean_mul_resolventLogCube_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range cutoff,
          resolventLogCubeWeight z n * q n)
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
      resolventLogCubeWeight z cutoff / modifiedMass cutoff)
      atTop (nhds 0) := by
    have h :=
      tendsto_resolventLogMean_mul_resolventLogCubeWeight_div_mass_zero hz
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

/-- `log(M)⁴ / A_M(z)` tends to zero. -/
theorem tendsto_log_fourth_div_resolventMass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 4 / resolventMass z cutoff) atTop (nhds 0) := by
  have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
      atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hsexticSuccBase : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 6 / ((cutoff : ℝ) + 1))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero).comp hcastSucc
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
  have hsexticSucc : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 6 / cutoff) atTop (nhds 0) := by
    have h := hsexticSuccBase.mul hsuccRatio
    have h' : Tendsto (fun cutoff : ℕ =>
        (Real.log ((cutoff : ℝ) + 1) ^ 6 / ((cutoff : ℝ) + 1)) *
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
      Real.log cutoff ^ 4 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      exact div_nonneg
        (mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hcutoff)) 4)
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
          Real.log (cutoff : ℝ) ^ 4 *
              Real.log ((cutoff : ℝ) + 1) ^ 2 ≤
            Real.log ((cutoff : ℝ) + 1) ^ 4 *
              Real.log ((cutoff : ℝ) + 1) ^ 2 := by
                gcongr
          _ = Real.log ((cutoff : ℝ) + 1) ^ 6 := by ring) hcutoffPos.le
    · exact hsexticSucc
  have hmassRatio := tendsto_resolventMass_div_nat_div_log_sq_one hz
  have hmassRatioInv := hmassRatio.inv₀ (by norm_num)
  have hproduct := hlogFactor.mul hmassRatioInv
  have hproduct' : Tendsto (fun cutoff : ℕ =>
      (Real.log cutoff ^ 4 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff) *
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

/-- The fourth power of the resolvent logarithmic mean is negligible relative
to resolvent mass. -/
theorem tendsto_resolventLogMean_fourth_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 4 / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hlogFourth := tendsto_log_fourth_div_resolventMass_zero hz
  have hdelta := tendsto_resolventLogMean_sub_log hz
  have hlogCube := tendsto_log_cube_div_resolventMass_zero hz
  have hlogSq := tendsto_log_sq_div_resolventMass_zero hz
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hlimit :=
    ((((hlogFourth.add ((hdelta.mul hlogCube).const_mul 4)).add
      (((hdelta.pow 2).mul hlogSq).const_mul 6)).add
        (((hdelta.pow 3).mul hlog).const_mul 4)).add
          ((hdelta.pow 4).mul hinvMass))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 4 / resolventMass z cutoff +
        4 * ((resolventLogMean z cutoff - Real.log cutoff) *
          (Real.log cutoff ^ 3 / resolventMass z cutoff)) +
        6 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 2 *
          (Real.log cutoff ^ 2 / resolventMass z cutoff)) +
        4 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 3 *
          (Real.log cutoff / resolventMass z cutoff)) +
        (resolventLogMean z cutoff - Real.log cutoff) ^ 4 *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

/-- The logarithmic mean is slowly varying under every fixed positive natural
dilation. -/
theorem tendsto_resolventLogMean_nat_mul_div {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z (scale * cutoff) / resolventLogMean z cutoff)
      atTop (nhds 1) := by
  have hscaleTop := tendsto_nat_const_mul_atTop hscale
  have hdelta := tendsto_resolventLogMean_sub_log hz
  have hdeltaScaled := hdelta.comp hscaleTop
  have hlogDifference : Tendsto (fun cutoff : ℕ =>
      Real.log (scale * cutoff) - Real.log cutoff)
      atTop (nhds (Real.log scale)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
    have hcutoffNat : 0 < cutoff :=
      lt_of_lt_of_le Nat.zero_lt_one hcutoff
    have hscaleReal : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale.ne'
    have hcutoffReal : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat.ne'
    norm_num [Nat.cast_mul, Real.log_mul hscaleReal hcutoffReal]
  have hdifference := (hdeltaScaled.add hlogDifference).sub hdelta
  have hdifference' : Tendsto (fun cutoff : ℕ =>
      resolventLogMean z (scale * cutoff) - resolventLogMean z cutoff)
      atTop (nhds (Real.log scale)) := by
    convert hdifference using 1
    · ext cutoff
      norm_num [Function.comp_apply, Nat.cast_mul]
    · ring
  have hlogTop : Tendsto (fun cutoff : ℕ => Real.log cutoff)
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmeanTopAux := hdelta.add_atTop hlogTop
  have hmeanTop : Tendsto (resolventLogMean z) atTop atTop := by
    have h : Tendsto (fun cutoff : ℕ =>
        (resolventLogMean z cutoff - Real.log cutoff) + Real.log cutoff)
        atTop atTop := hmeanTopAux
    apply h.congr'
    filter_upwards with cutoff
    ring
  have hinvMean : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hmeanTop
  have hcorrection := hdifference'.mul hinvMean
  have hlimit : Tendsto (fun cutoff : ℕ =>
      1 + (resolventLogMean z (scale * cutoff) -
        resolventLogMean z cutoff) * (resolventLogMean z cutoff)⁻¹)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hcorrection)
  have hmeanNe := hmeanTop.eventually_ne_atTop 0
  apply hlimit.congr'
  filter_upwards [hmeanNe] with cutoff hmean
  field_simp [hmean]
  ring

theorem tendsto_resolventCenteredLogFourth_periodicResidue_zero
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 *
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
  have hfourthBase :=
    tendsto_resolventLogFourth_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hfourthAtScale := hfourthBase.comp hscaleTop
  have hfourthAtScale' : Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff),
        resolventLogFourthWeight z n * centered n) /
          resolventMass z (scale * cutoff)) atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff),
        resolventLogFourthWeight z n * centered n) /
          resolventMass z (scale * cutoff)) atTop (nhds 0) at hfourthAtScale
    exact hfourthAtScale
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hfourthProduct := hfourthAtScale'.mul hmassRatio
  have hfourthPart : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFourthWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFourthWeight z n * centered n) /
          resolventMass z (scale * cutoff)) *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hfourthProduct
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
  have hcubeBase :=
    tendsto_resolventLogMean_mul_resolventLogCube_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hcubeAtScale := hcubeBase.comp hscaleTop
  have hcubeAtScale' : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z (scale * cutoff) /
          resolventMass z (scale * cutoff)) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) at hcubeAtScale
    exact hcubeAtScale
  have hmeanRatio := tendsto_resolventLogMean_nat_mul_div hz hscale
  have hmeanRatioInv := hmeanRatio.inv₀ (by norm_num)
  have hcubeProduct := (hcubeAtScale'.mul hmeanRatioInv).mul hmassRatio
  have hcubePart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((resolventLogMean z (scale * cutoff) /
            resolventMass z (scale * cutoff)) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogCubeWeight z n * centered n) *
        (resolventLogMean z (scale * cutoff) /
          resolventLogMean z cutoff)⁻¹ *
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
      6 * resolventLogMean z cutoff ^ 2 / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_sq_div_mass_zero hz).const_mul 6
    simpa only [mul_div_assoc, mul_zero] using h
  have hquadraticPart : Tendsto (fun cutoff : ℕ =>
      (6 * resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSqWeight z n * centered n) atTop (nhds 0) :=
    hquadraticCoefficient.zero_mul_isBoundedUnder_le hlogSqWeightScaled
  have hlinearCoefficient : Tendsto (fun cutoff : ℕ =>
      4 * resolventLogMean z cutoff ^ 3 / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_cube_div_mass_zero hz).const_mul 4
    simpa only [mul_div_assoc, mul_zero] using h
  have hlinearPart : Tendsto (fun cutoff : ℕ =>
      (4 * resolventLogMean z cutoff ^ 3 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n) atTop (nhds 0) :=
    hlinearCoefficient.zero_mul_isBoundedUnder_le hlogWeightScaled
  have hconstantPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 4 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n * centered n) atTop (nhds 0) :=
    (tendsto_resolventLogMean_fourth_div_mass_zero hz).zero_mul_isBoundedUnder_le
      hweightScaled
  have hlimit :=
    (((hfourthPart.sub (hcubePart.const_mul 4)).add hquadraticPart).sub
      hlinearPart).add hconstantPart
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogFourthWeight z n * centered n -
        4 * ((resolventLogMean z cutoff / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogCubeWeight z n * centered n) +
        (6 * resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSqWeight z n * centered n -
        (4 * resolventLogMean z cutoff ^ 3 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogWeight z n * centered n +
        (resolventLogMean z cutoff ^ 4 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n * centered n) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 * centered n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventLogFourthWeight z n * centered n) -
          4 * resolventLogMean z cutoff *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogCubeWeight z n * centered n +
          6 * resolventLogMean z cutoff ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogSqWeight z n * centered n -
          4 * resolventLogMean z cutoff ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogWeight z n * centered n +
          resolventLogMean z cutoff ^ 4 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventWeight z n * centered n := by
    calc
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 * centered n) =
        ∑ n ∈ Finset.range (scale * cutoff),
          (resolventLogFourthWeight z n * centered n -
            4 * resolventLogMean z cutoff *
              (resolventLogCubeWeight z n * centered n) +
            6 * resolventLogMean z cutoff ^ 2 *
              (resolventLogSqWeight z n * centered n) -
            4 * resolventLogMean z cutoff ^ 3 *
              (resolventLogWeight z n * centered n) +
            resolventLogMean z cutoff ^ 4 *
              (resolventWeight z n * centered n)) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [resolventLogFourthWeight, resolventLogCubeWeight,
            resolventLogSqWeight, resolventLogWeight]
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
  rw [hsum]
  ring

/-- Periodic averaging for the fourth centered logarithmic resolvent moment. -/
theorem tendsto_resolventCenteredLogFourth_periodicWeightedSum
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 * q n)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 4 + 6 * Real.log scale ^ 2 -
          8 * Real.log scale + 9)) * periodMean q period)) := by
  have hscalar :=
    tendsto_resolventScaledCenteredLogFourthMoment_div_mass hz hscale
  have hmain : Tendsto (fun cutoff : ℕ =>
      (resolventScaledCenteredLogFourthMoment z scale cutoff /
        resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 4 + 6 * Real.log scale ^ 2 -
          8 * Real.log scale + 9)) * periodMean q period)) :=
    hscalar.mul_const (periodMean q period)
  have hresidue := tendsto_resolventCenteredLogFourth_periodicResidue_zero
    hz hperiod hscale hq
  have hlimit := hresidue.add hmain
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 *
                (q n - periodMean q period) +
        (resolventScaledCenteredLogFourthMoment z scale cutoff /
          resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 4 + 6 * Real.log scale ^ 2 -
          8 * Real.log scale + 9)) * periodMean q period)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 * q n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 *
              (q n - periodMean q period)) +
          periodMean q period *
            resolventScaledCenteredLogFourthMoment z scale cutoff := by
    rw [resolventScaledCenteredLogFourthMoment, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsum]
  ring

/-- The shifted periodic camera core with the centered fourth-power multiplier
converges entrywise to the fourth centered moment. -/
theorem tendsto_resolvent_shiftedCoreFourthFunctional_apply
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
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 *
              realProfileProduct (camera i) (camera j) (n + 1))
      atTop (nhds (fourthCenteredMomentMatrix period camera i j)) := by
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
  have hlimit := tendsto_resolventCenteredLogFourth_periodicWeightedSum
    hz hperiod hscale hq
  rw [hmean] at hlimit
  have htarget :
      (((scale : ℝ) *
          (Real.log scale ^ 4 + 6 * Real.log scale ^ 2 -
            8 * Real.log scale + 9)) *
          periodicProductMean period (camera i) (camera j)) =
        fourthCenteredMomentMatrix period camera i j := by
    rw [fourthCenteredMomentMatrix_apply, periodicGramMatrix_apply]
    simp only [slopeOverlap, scale]
    ring
  rw [htarget] at hlimit
  simpa only [pairCoreLength, scale, q] using hlimit

/-- Fourth-power multiplier in the finite centered logarithmic coordinate. -/
def centeredFourthMultiplier (z : ℂ) (cutoff n : ℕ) : ℝ :=
  (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4

/-- Product of the resolvent weight with the centered fourth-power
multiplier. -/
def resolventCenteredFourthWeight (z : ℂ) (cutoff n : ℕ) : ℝ :=
  resolventWeight z n * centeredFourthMultiplier z cutoff n

@[simp] theorem centeredPolynomialMultiplier_X_fourth
    (z : ℂ) (cutoff n : ℕ) :
    centeredPolynomialMultiplier (Polynomial.X ^ 4) z cutoff n =
      centeredFourthMultiplier z cutoff n := by
  simp [centeredPolynomialMultiplier, centeredFourthMultiplier]

/-- Every fixed literal seed/endpoint term vanishes for the centered
fourth-power functional weight. -/
theorem tendsto_resolventCenteredFourth_finiteBoundaryTerm_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (r : ℕ) :
    Tendsto (fun cutoff =>
      finiteBoundaryTerm (resolventCenteredFourthWeight z cutoff)
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
  have hcubic :=
    tendsto_resolventCenteredCubic_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r
  have hproduct := hcoordinate.mul hcubic
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (scale * cutoff + r + 1) - resolventLogMean z cutoff) *
        finiteBoundaryTerm (resolventCenteredCubicWeight z cutoff)
          cutoff camera₁ camera₂ r) atTop (nhds 0) := by
    simpa only [mul_zero] using hproduct
  apply hlimit.congr'
  filter_upwards with cutoff
  rw [finiteBoundaryTerm, finiteBoundaryTerm]
  split_ifs
  · rw [resolventCenteredFourthWeight, centeredFourthMultiplier,
      resolventCenteredCubicWeight, centeredCubicMultiplier]
    simp only [pairCoreLength, scale]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  · ring

/-- The complete fixed-width literal boundary vanishes for the centered
fourth-power functional weight. -/
theorem tendsto_resolventCenteredFourth_finiteBoundarySum_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) :
    Tendsto (fun cutoff =>
      finiteBoundarySum (resolventCenteredFourthWeight z cutoff)
        cutoff camera₁ camera₂) atTop (nhds 0) := by
  have hsum := tendsto_finsetSum
    (Finset.range (pairBoundaryWidth camera₁ camera₂))
    (fun r _ => tendsto_resolventCenteredFourth_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r)
  simpa only [finiteBoundarySum, Finset.sum_const_zero] using hsum

/-- Entrywise convergence of the complete literal centered-fourth-power
coefficient covariance to the fourth centered camera moment. -/
theorem tendsto_finiteCenteredFourthCoefficientCovariance_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff camera i j)
      atTop (nhds (fourthCenteredMomentMatrix period camera i j)) := by
  have hcore := tendsto_resolvent_shiftedCoreFourthFunctional_apply
    hz hperiod hcamera hcommon i j
  have hboundary := tendsto_resolventCenteredFourth_finiteBoundarySum_zero
    hz (hcamera i) (hcamera j)
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hboundaryNormalized : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        finiteBoundarySum (resolventCenteredFourthWeight z cutoff)
          cutoff (camera i) (camera j)) atTop (nhds 0) := by
    simpa only [zero_mul] using hinvMass.mul hboundary
  have hlimit := hcore.add hboundaryNormalized
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range
              (pairCoreLength (camera i) (camera j) cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 *
                realProfileProduct (camera i) (camera j) (n + 1) +
        (resolventMass z cutoff)⁻¹ *
          finiteBoundarySum (resolventCenteredFourthWeight z cutoff)
            cutoff (camera i) (camera j))
      atTop (nhds (fourthCenteredMomentMatrix period camera i j)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  rw [finiteCenteredPolynomialCoefficientCovariance,
    finiteFunctionalCoefficientCovariance]
  simp only [centeredPolynomialMultiplier_X_fourth]
  have hnum :
      (∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventWeight z n * centeredFourthMultiplier z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n) =
        ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventCenteredFourthWeight z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredFourthWeight]
  rw [hnum]
  rw [finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary
    (weight := resolventCenteredFourthWeight z cutoff)
      (hcamera i) (hcamera j)]
  have hcoreEq :
      (∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventCenteredFourthWeight z cutoff n *
            realProfileProduct (camera i) (camera j) (n + 1)) =
        ∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 *
              realProfileProduct (camera i) (camera j) (n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredFourthWeight, centeredFourthMultiplier]
  rw [hcoreEq]
  simp only [resolventMass]
  ring

/-- Matrix convergence of the complete literal centered-fourth-power
coefficient covariance. -/
theorem tendsto_finiteCenteredFourthCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff camera)
      atTop (nhds (fourthCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff camera i j)
    atTop (nhds fun i j => fourthCenteredMomentMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_finiteCenteredFourthCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j

/-- Finite entry-sup norm convergence of the literal centered-fourth-power
coefficient covariance. -/
theorem tendsto_norm_finiteCenteredFourthCoefficientCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff camera -
        fourthCenteredMomentMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_finiteCenteredFourthCoefficientCovariance
    hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => fourthCenteredMomentMatrix period camera)
        atTop (nhds (fourthCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- The literal six-camera centered-fourth-power covariance converges to the
exact documented matrix `sixCameraFourthCenteredMoment`. -/
theorem
    tendsto_norm_sixCamera_finiteCenteredFourthCoefficientCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff sixCamera -
        sixCameraFourthCenteredMoment‖) atTop (nhds 0) := by
  rw [← sixCameraFourthCenteredMoment_eq]
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  exact tendsto_norm_finiteCenteredFourthCoefficientCovariance_sub
    hz (by norm_num : 0 < 420) hcamera sixCamera_commonPeriod

/-- Complexification of the fourth centered periodic camera moment. -/
def complexFourthCenteredMomentMatrix {index : Type*} (period : ℕ)
    (camera : index → ℕ) : Matrix index index ℂ :=
  fun i j => (fourthCenteredMomentMatrix period camera i j : ℂ)

/-- Complexified convergence of the complete literal centered-fourth-power
coefficient covariance. -/
theorem tendsto_complex_finiteCenteredFourthCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff i j =>
      (finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff camera i j : ℂ))
      atTop (nhds (complexFourthCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    (finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff camera i j : ℂ))
    atTop (nhds fun i j =>
      (fourthCenteredMomentMatrix period camera i j : ℂ))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hreal := tendsto_finiteCenteredFourthCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j
  exact (Complex.continuous_ofReal.tendsto
    (fourthCenteredMomentMatrix period camera i j)).comp hreal

/-- The normalized direct finite functional covariance for the centered
fourth-power multiplier converges to the complexified fourth centered
moment. -/
theorem tendsto_normalizedFiniteCenteredFourthDirectCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalDirectCovariance z cutoff camera
        (centeredPolynomialMultiplier
          (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff))
      atTop (nhds (complexFourthCenteredMomentMatrix period camera)) := by
  apply tendsto_normalizedFiniteFunctionalDirectCovariance_of_coefficients
    hcamera
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredFourthCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of the normalized direct
centered-fourth-power functional covariance. -/
theorem tendsto_norm_normalizedFiniteCenteredFourthDirectCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff camera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff) -
        complexFourthCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredFourthDirectCovariance
      hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => complexFourthCenteredMomentMatrix period camera)
        atTop (nhds (complexFourthCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Every compatible finite return-metric colligation family inherits the
centered fourth-moment limit. -/
theorem tendsto_normalizedFiniteCenteredFourthReturnMetricCrossCovariance
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
          (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff)
        (endpointMap cutoff) (poisson cutoff))
      atTop (nhds (complexFourthCenteredMomentMatrix period camera)) := by
  apply
    tendsto_normalizedFiniteFunctionalReturnMetricCrossCovariance_of_coefficients
      hcamera endpointMap bulkMap poisson hpoisson hisometry
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredFourthCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of every compatible centered-fourth
return-metric cross covariance family. -/
theorem
    tendsto_norm_normalizedFiniteCenteredFourthReturnMetricCrossCovariance_sub
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
            (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexFourthCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredFourthReturnMetricCrossCovariance
      hz hperiod hcamera hcommon endpointMap bulkMap poisson hpoisson hisometry
  have hconstant :
      Tendsto (fun _ : ℕ => complexFourthCenteredMomentMatrix period camera)
        atTop (nhds (complexFourthCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Complex form of the exact documented six-camera fourth centered moment. -/
def complexSixCameraFourthCenteredMoment : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (sixCameraFourthCenteredMoment i j : ℂ)

@[simp] theorem complexFourthCenteredMomentMatrix_sixCamera :
    complexFourthCenteredMomentMatrix 420 sixCamera =
      complexSixCameraFourthCenteredMoment := by
  unfold complexFourthCenteredMomentMatrix
    complexSixCameraFourthCenteredMoment
  rw [sixCameraFourthCenteredMoment_eq]

/-- The literal six-camera direct centered-fourth-power covariance converges
in matrix norm to the exact documented fourth centered-moment matrix. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredFourthDirectCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff sixCamera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff) -
        complexSixCameraFourthCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexFourthCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredFourthDirectCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Exact passage to the six-camera fourth centered-moment limit for every
finite colligation family satisfying the Poisson and Pythagorean identities. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredFourthReturnMetricCrossCovariance_sub
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
            (Polynomial.X ^ 4 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSixCameraFourthCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexFourthCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredFourthReturnMetricCrossCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod endpointMap bulkMap poisson hpoisson hisometry)

end

end NativeCarrySpectralWeyl.Limits
