import NativeCarrySpectralWeyl.Limits.LinearFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarSecondFunctionalMoment
import Mathlib.Tactic

/-!
# Quadratic functional covariance limit

This file connects the second scalar resolvent functional moment to the
periodic camera coefficients.  The new analytic point is the weight
`log(n+1)² w_z(n)`: it tends to one, rather than zero, but is eventually
monotone in one direction.  Subtracting its limit and applying Dirichlet's
test keeps every zero-mean periodic residue bounded.  The lower logarithmic
weights and the finite literal boundary are then controlled separately.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- Monotone form of the bounded periodic Dirichlet-sum theorem. -/
theorem isBounded_range_periodic_weightedSum_of_eventually_monotone
    {q weight : ℕ → ℝ} {period : ℕ}
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0)
    (hweightMono : ∃ offset : ℕ, Monotone (fun n => weight (offset + n)))
    (hweightZero : Tendsto weight atTop (nhds 0)) :
    IsBoundedUnder (· ≤ ·) atTop (norm ∘ (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n * q n)) := by
  obtain ⟨offset, hmono⟩ := hweightMono
  let shiftedWeight : ℕ → ℝ := fun n => weight (offset + n)
  let shiftedQ : ℕ → ℝ := fun n => q (offset + n)
  let numerator : ℕ → ℝ := fun cutoff =>
    ∑ n ∈ Finset.range cutoff, weight n * q n
  let shiftedNumerator : ℕ → ℝ := fun cutoff =>
    ∑ n ∈ Finset.range cutoff, shiftedWeight n * shiftedQ n
  let initialSum : ℝ := numerator offset
  have hshiftedQ : Function.Periodic shiftedQ period := by
    intro n
    simpa only [shiftedQ, Nat.add_assoc] using hq (offset + n)
  have hshiftedSum : ∑ r ∈ Finset.range period, shiftedQ r = 0 := by
    rw [show (∑ r ∈ Finset.range period, shiftedQ r) =
        ∑ r ∈ Finset.range period, q (offset + r) by rfl,
      sum_period_natAdd hq offset, hsum]
  have hprefixBound (cutoff : ℕ) :
      ‖∑ n ∈ Finset.range cutoff, shiftedQ n‖ ≤
        ∑ r ∈ Finset.range period, ‖shiftedQ r‖ :=
    norm_sum_range_le_period_norm_sum hperiod hshiftedQ hshiftedSum cutoff
  have hshiftedZero : Tendsto shiftedWeight atTop (nhds 0) := by
    have h := hweightZero.comp (tendsto_add_atTop_nat offset)
    convert h using 1
    ext n
    simp only [shiftedWeight, Function.comp_apply, Nat.add_comm]
  have hshiftedCauchy : CauchySeq shiftedNumerator := by
    have h := hmono.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      hshiftedZero hprefixBound
    simpa only [shiftedNumerator, smul_eq_mul] using h
  have hprefixEq (cutoff : ℕ) :
      numerator (cutoff + offset) = initialSum + shiftedNumerator cutoff := by
    simp only [numerator, initialSum, shiftedNumerator, shiftedWeight, shiftedQ]
    rw [Nat.add_comm cutoff offset, Finset.sum_range_add]
  have hshiftedOriginal : CauchySeq (fun cutoff => numerator (cutoff + offset)) := by
    have heq : (fun cutoff => numerator (cutoff + offset)) =
        fun cutoff => shiftedNumerator cutoff + initialSum := by
      funext cutoff
      rw [hprefixEq]
      ring
    rw [heq]
    exact hshiftedCauchy.add_const
  have horiginalCauchy : CauchySeq numerator :=
    (cauchySeq_shift offset).mp hshiftedOriginal
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.mp horiginalCauchy.isBounded_range
  change ∃ C : ℝ, ∀ᶠ cutoff : ℕ in atTop, ‖numerator cutoff‖ ≤ C
  exact ⟨C, Filter.Eventually.of_forall fun cutoff =>
    hC (numerator cutoff) ⟨cutoff, rfl⟩⟩

/-- A periodic weighted sum stays bounded when the scalar weight converges
and is eventually monotone in either direction. -/
theorem isBounded_range_periodic_weightedSum_of_eventually_monotone_or_antitone
    {q weight : ℕ → ℝ} {period : ℕ} {limit : ℝ}
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0)
    (hweightOrder :
      (∃ offset : ℕ, Monotone (fun n => weight (offset + n))) ∨
      (∃ offset : ℕ, Antitone (fun n => weight (offset + n))))
    (hweightLimit : Tendsto weight atTop (nhds limit)) :
    IsBoundedUnder (· ≤ ·) atTop (norm ∘ (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n * q n)) := by
  let shiftedWeight : ℕ → ℝ := fun n => weight n - limit
  have hshiftedZero : Tendsto shiftedWeight atTop (nhds 0) := by
    have h := hweightLimit.sub_const limit
    simpa only [shiftedWeight, sub_self] using h
  have hshiftedOrder :
      (∃ offset : ℕ, Monotone (fun n => shiftedWeight (offset + n))) ∨
      (∃ offset : ℕ, Antitone (fun n => shiftedWeight (offset + n))) := by
    rcases hweightOrder with ⟨offset, hmono⟩ | ⟨offset, hanti⟩
    · left
      exact ⟨offset, fun _ _ hmn => sub_le_sub_right (hmono hmn) limit⟩
    · right
      exact ⟨offset, fun _ _ hmn => sub_le_sub_right (hanti hmn) limit⟩
  have hshiftedBound : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ (fun cutoff : ℕ =>
        ∑ n ∈ Finset.range cutoff, shiftedWeight n * q n)) := by
    rcases hshiftedOrder with hmono | hanti
    · exact isBounded_range_periodic_weightedSum_of_eventually_monotone
        hperiod hq hsum hmono hshiftedZero
    · exact isBounded_range_periodic_weightedSum_of_eventually_antitone
        hperiod hq hsum hanti hshiftedZero
  obtain ⟨C, hC⟩ := hshiftedBound
  let B : ℝ := ∑ r ∈ Finset.range period, ‖q r‖
  change ∃ D : ℝ, ∀ᶠ cutoff : ℕ in atTop,
    ‖∑ n ∈ Finset.range cutoff, weight n * q n‖ ≤ D
  refine ⟨C + |limit| * B, ?_⟩
  filter_upwards [hC] with cutoff hcutoff
  have hprefix : ‖∑ n ∈ Finset.range cutoff, q n‖ ≤ B :=
    norm_sum_range_le_period_norm_sum hperiod hq hsum cutoff
  have hdecomp :
      (∑ n ∈ Finset.range cutoff, weight n * q n) =
        (∑ n ∈ Finset.range cutoff, shiftedWeight n * q n) +
          limit * ∑ n ∈ Finset.range cutoff, q n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [shiftedWeight]
    ring
  rw [hdecomp]
  calc
    ‖(∑ n ∈ Finset.range cutoff, shiftedWeight n * q n) +
        limit * ∑ n ∈ Finset.range cutoff, q n‖ ≤
      ‖∑ n ∈ Finset.range cutoff, shiftedWeight n * q n‖ +
        ‖limit * ∑ n ∈ Finset.range cutoff, q n‖ := norm_add_le _ _
    _ = ‖∑ n ∈ Finset.range cutoff, shiftedWeight n * q n‖ +
        |limit| * ‖∑ n ∈ Finset.range cutoff, q n‖ := by
          simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ C + |limit| * B :=
      add_le_add hcutoff
        (mul_le_mul_of_nonneg_left hprefix (abs_nonneg limit))

/-- Quadratically logarithmic resolvent weight. -/
def resolventLogSqWeight (z : ℂ) (n : ℕ) : ℝ :=
  Real.log (n + 1) ^ 2 * resolventWeight z n

/-- The quadratically logarithmic resolvent weight tends to one. -/
theorem tendsto_resolventLogSqWeight_one {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (resolventLogSqWeight z) atTop (nhds 1) := by
  change Tendsto (fun n : ℕ =>
    Real.log ((n : ℝ) + 1) ^ 2 * resolventWeight z n) atTop (nhds 1)
  simpa only [mul_comm] using
    tendsto_resolventWeight_mul_log_sq_one hz

/-- The quadratically logarithmic resolvent weight is eventually monotone in
one direction. -/
theorem exists_resolventLogSqWeight_monotone_or_antitone_natAdd
    {z : ℂ} (hz : z.im ≠ 0) :
    (∃ offset : ℕ,
      Monotone (fun n : ℕ => resolventLogSqWeight z (offset + n))) ∨
    (∃ offset : ℕ,
      Antitone (fun n : ℕ => resolventLogSqWeight z (offset + n))) := by
  let c : ℝ := z.re ^ 2 + z.im ^ 2
  have hc : 0 ≤ c := by
    simp only [c]
    positivity
  by_cases ha : z.re ≤ 0
  · left
    refine ⟨0, ?_⟩
    intro m n hmn
    let x : ℝ := Real.log (((m + 1 : ℕ) : ℝ))
    let y : ℝ := Real.log (((n + 1 : ℕ) : ℝ))
    have hindex : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hmn 1
    have hxy : x ≤ y := by
      exact Real.strictMonoOn_log.monotoneOn
        (by exact Set.mem_Ioi.mpr (by positivity))
        (by exact Set.mem_Ioi.mpr (by positivity)) hindex
    have hx0 : 0 ≤ x := by
      exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
    have hy0 : 0 ≤ y := hx0.trans hxy
    have hdenX : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by positivity
    have hdenY : 0 < (y - z.re) ^ 2 + z.im ^ 2 := by positivity
    have hineq :
        x ^ 2 / ((x - z.re) ^ 2 + z.im ^ 2) ≤
          y ^ 2 / ((y - z.re) ^ 2 + z.im ^ 2) := by
      rw [div_le_div_iff₀ hdenX hdenY]
      have hfactor :
          y ^ 2 * ((x - z.re) ^ 2 + z.im ^ 2) -
              x ^ 2 * ((y - z.re) ^ 2 + z.im ^ 2) =
            (y - x) * (c * (x + y) - 2 * z.re * x * y) := by
        simp only [c]
        ring
      rw [← sub_nonneg, hfactor]
      exact mul_nonneg (sub_nonneg.mpr hxy) (by
        have : 0 ≤ c * (x + y) := mul_nonneg hc (add_nonneg hx0 hy0)
        nlinarith [mul_nonneg hx0 hy0])
    simp only [resolventLogSqWeight, zero_add]
    rw [resolventWeight_eq, resolventWeight_eq]
    simpa only [x, y, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hineq
  · right
    have haPos : 0 < z.re := lt_of_not_ge ha
    have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp hcast
    obtain ⟨offset, hoffset⟩ :=
      eventually_atTop.1 (hlog.eventually_ge_atTop (c / z.re + 1))
    refine ⟨offset, ?_⟩
    intro m n hmn
    let x : ℝ := Real.log (((offset + m + 1 : ℕ) : ℝ))
    let y : ℝ := Real.log (((offset + n + 1 : ℕ) : ℝ))
    have hindexNat : offset + m + 1 ≤ offset + n + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left hmn offset) 1
    have hindex : ((offset + m + 1 : ℕ) : ℝ) ≤
        ((offset + n + 1 : ℕ) : ℝ) := by exact_mod_cast hindexNat
    have hxy : x ≤ y := by
      exact Real.strictMonoOn_log.monotoneOn
        (by exact Set.mem_Ioi.mpr (by positivity))
        (by exact Set.mem_Ioi.mpr (by positivity)) hindex
    have hcx : c / z.re + 1 ≤ x := by
      have h := hoffset (offset + m) (Nat.le_add_right offset m)
      simpa only [x, Nat.cast_add, Nat.cast_one] using h
    have hcy : c / z.re + 1 ≤ y := hcx.trans hxy
    have hdiv0 : 0 ≤ c / z.re := div_nonneg hc haPos.le
    have hx0 : 0 ≤ x := by linarith
    have hy0 : 0 ≤ y := by linarith
    have hcax : c ≤ z.re * x := by
      have := (div_le_iff₀ haPos).mp (by linarith : c / z.re ≤ x)
      nlinarith
    have hcay : c ≤ z.re * y := by
      have := (div_le_iff₀ haPos).mp (by linarith : c / z.re ≤ y)
      nlinarith
    have hmain : c * (x + y) ≤ 2 * z.re * x * y := by
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hcay),
        mul_nonneg hy0 (sub_nonneg.mpr hcax)]
    have hdenX : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by positivity
    have hdenY : 0 < (y - z.re) ^ 2 + z.im ^ 2 := by positivity
    have hineq :
        y ^ 2 / ((y - z.re) ^ 2 + z.im ^ 2) ≤
          x ^ 2 / ((x - z.re) ^ 2 + z.im ^ 2) := by
      rw [div_le_div_iff₀ hdenY hdenX]
      have hfactor :
          x ^ 2 * ((y - z.re) ^ 2 + z.im ^ 2) -
              y ^ 2 * ((x - z.re) ^ 2 + z.im ^ 2) =
            (y - x) * (2 * z.re * x * y - c * (x + y)) := by
        simp only [c]
        ring
      rw [← sub_nonneg, hfactor]
      exact mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hmain)
    simp only [resolventLogSqWeight]
    rw [resolventWeight_eq, resolventWeight_eq]
    simpa only [x, y, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hineq

/-- The squared logarithmic scale is negligible compared with the resolvent
mass. -/
theorem tendsto_log_sq_div_resolventMass_zero {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 2 / resolventMass z cutoff) atTop (nhds 0) := by
  have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
      atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hquarticSuccBase : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 4 / ((cutoff : ℝ) + 1))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp hcastSucc
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
  have hquarticSucc : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 4 / cutoff) atTop (nhds 0) := by
    have h := hquarticSuccBase.mul hsuccRatio
    have h' : Tendsto (fun cutoff : ℕ =>
        (Real.log ((cutoff : ℝ) + 1) ^ 4 / ((cutoff : ℝ) + 1)) *
          (((cutoff : ℝ) + 1) / cutoff)) atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
    have hcutoffNat : 0 < cutoff :=
      lt_of_lt_of_le Nat.zero_lt_one hcutoff
    have hcutoff0 : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat.ne'
    have hsucc0 : (cutoff : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hcutoff0, hsucc0]
  have hlogFactor : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 2 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (by exact_mod_cast hcutoffNat.le)
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      have hcutoffPos : (0 : ℝ) < cutoff := by exact_mod_cast hcutoffNat
      have hlog0 : 0 ≤ Real.log (cutoff : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hcutoff)
      have hlogSucc0 : 0 ≤ Real.log ((cutoff : ℝ) + 1) :=
        Real.log_nonneg (by linarith)
      have hlogLe : Real.log (cutoff : ℝ) ≤
          Real.log ((cutoff : ℝ) + 1) := by
        exact Real.strictMonoOn_log.monotoneOn
          (by exact Set.mem_Ioi.mpr hcutoffPos)
          (by exact Set.mem_Ioi.mpr (by positivity)) (by linarith)
      have hsqLe : Real.log (cutoff : ℝ) ^ 2 ≤
          Real.log ((cutoff : ℝ) + 1) ^ 2 :=
        (sq_le_sq₀ hlog0 hlogSucc0).2 hlogLe
      exact div_le_div_of_nonneg_right (by
        calc
          Real.log (cutoff : ℝ) ^ 2 *
                Real.log ((cutoff : ℝ) + 1) ^ 2 ≤
              Real.log ((cutoff : ℝ) + 1) ^ 2 *
                Real.log ((cutoff : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right hsqLe (sq_nonneg _)
          _ = Real.log ((cutoff : ℝ) + 1) ^ 4 := by ring) hcutoffPos.le
    · exact hquarticSucc
  have hmassRatio := tendsto_resolventMass_div_nat_div_log_sq_one hz
  have hmassRatioInv := hmassRatio.inv₀ (by norm_num)
  have hproduct := hlogFactor.mul hmassRatioInv
  have hproduct' : Tendsto (fun cutoff : ℕ =>
      (Real.log cutoff ^ 2 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff) *
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

/-- The square of the weighted logarithmic mean is negligible compared with
the resolvent mass. -/
theorem tendsto_resolventLogMean_sq_div_mass_zero {z : ℂ}
    (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 2 / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hlogSq := tendsto_log_sq_div_resolventMass_zero hz
  have hdelta := tendsto_resolventLogMean_sub_log hz
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hlimit := (hlogSq.add ((hdelta.mul hlog).const_mul 2)).add
    ((hdelta.pow 2).mul hinvMass)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 2 / resolventMass z cutoff +
        2 * ((resolventLogMean z cutoff - Real.log cutoff) *
          (Real.log cutoff / resolventMass z cutoff)) +
        (resolventLogMean z cutoff - Real.log cutoff) ^ 2 *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

/-- A centered zero-mean periodic factor contributes nothing to the second
scalar functional moment. -/
theorem tendsto_resolventCenteredLogSq_periodicResidue_zero
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 *
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
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hsqPart : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSqWeight z n * centered n) atTop (nhds 0) :=
    hinvMass.zero_mul_isBoundedUnder_le hlogSqWeightScaled
  have hlinearCoefficient : Tendsto (fun cutoff : ℕ =>
      2 * resolventLogMean z cutoff / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_div_mass_zero hz).const_mul 2
    simpa only [mul_div_assoc, mul_zero] using h
  have hlinearPart : Tendsto (fun cutoff : ℕ =>
      (2 * resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n) atTop (nhds 0) :=
    hlinearCoefficient.zero_mul_isBoundedUnder_le hlogWeightScaled
  have hconstantPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n * centered n) atTop (nhds 0) :=
    (tendsto_resolventLogMean_sq_div_mass_zero hz).zero_mul_isBoundedUnder_le
      hweightScaled
  have hlimit := (hsqPart.sub hlinearPart).add hconstantPart
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSqWeight z n * centered n -
        (2 * resolventLogMean z cutoff / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogWeight z n * centered n +
        (resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n * centered n) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 * centered n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSqWeight z n * centered n) -
          2 * resolventLogMean z cutoff *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogWeight z n * centered n +
          resolventLogMean z cutoff ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventWeight z n * centered n := by
    calc
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 * centered n) =
        ∑ n ∈ Finset.range (scale * cutoff),
          (resolventLogSqWeight z n * centered n -
            2 * resolventLogMean z cutoff *
              (resolventLogWeight z n * centered n) +
            resolventLogMean z cutoff ^ 2 *
              (resolventWeight z n * centered n)) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [resolventLogSqWeight, resolventLogWeight]
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsum]
  ring

/-- Periodic averaging for the second centered logarithmic resolvent
moment. -/
theorem tendsto_resolventCenteredLogSq_periodicWeightedSum
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 * q n)
      atTop (nhds (((scale : ℝ) * (1 + Real.log scale ^ 2)) *
        periodMean q period)) := by
  have hscalar :=
    tendsto_resolventScaledCenteredLogSqMoment_div_mass hz hscale
  have hmain : Tendsto (fun cutoff : ℕ =>
      (resolventScaledCenteredLogSqMoment z scale cutoff /
        resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) * (1 + Real.log scale ^ 2)) *
        periodMean q period)) :=
    hscalar.mul_const (periodMean q period)
  have hresidue := tendsto_resolventCenteredLogSq_periodicResidue_zero
    hz hperiod hscale hq
  have hlimit := hresidue.add hmain
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 *
                (q n - periodMean q period) +
        (resolventScaledCenteredLogSqMoment z scale cutoff /
          resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) * (1 + Real.log scale ^ 2)) *
        periodMean q period)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 * q n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 *
              (q n - periodMean q period)) +
          periodMean q period *
            resolventScaledCenteredLogSqMoment z scale cutoff := by
    rw [resolventScaledCenteredLogSqMoment, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsum]
  ring

/-- The shifted periodic camera core with the centered quadratic multiplier
converges entrywise to the documented second centered moment. -/
theorem tendsto_resolvent_shiftedCoreQuadraticFunctional_apply
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
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 *
              realProfileProduct (camera i) (camera j) (n + 1))
      atTop (nhds (secondCenteredMomentMatrix period camera i j)) := by
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
  have hlimit := tendsto_resolventCenteredLogSq_periodicWeightedSum
    hz hperiod hscale hq
  rw [hmean] at hlimit
  have htarget :
      (((scale : ℝ) * (1 + Real.log scale ^ 2)) *
          periodicProductMean period (camera i) (camera j)) =
        secondCenteredMomentMatrix period camera i j := by
    rw [secondCenteredMomentMatrix_apply, periodicGramMatrix_apply]
    simp only [slopeOverlap, scale]
    ring
  rw [htarget] at hlimit
  simpa only [pairCoreLength, scale, q] using hlimit

/-- Quadratic multiplier in the finite centered logarithmic coordinate. -/
def centeredQuadraticMultiplier (z : ℂ) (cutoff n : ℕ) : ℝ :=
  (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2

/-- Product of the resolvent weight with the centered quadratic multiplier. -/
def resolventCenteredQuadraticWeight (z : ℂ) (cutoff n : ℕ) : ℝ :=
  resolventWeight z n * centeredQuadraticMultiplier z cutoff n

@[simp] theorem centeredPolynomialMultiplier_X_sq (z : ℂ) (cutoff n : ℕ) :
    centeredPolynomialMultiplier (Polynomial.X ^ 2) z cutoff n =
      centeredQuadraticMultiplier z cutoff n := by
  simp [centeredPolynomialMultiplier, centeredQuadraticMultiplier]

/-- Every fixed literal seed/endpoint term vanishes for the centered
quadratic functional weight. -/
theorem tendsto_resolventCenteredQuadratic_finiteBoundaryTerm_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (r : ℕ) :
    Tendsto (fun cutoff =>
      finiteBoundaryTerm (resolventCenteredQuadraticWeight z cutoff)
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
  have hindex : Tendsto (fun cutoff : ℕ => scale * cutoff + r) atTop atTop :=
    (tendsto_add_atTop_nat r).comp (tendsto_nat_const_mul_atTop hscale)
  have hweight : Tendsto (fun cutoff : ℕ =>
      resolventWeight z (scale * cutoff + r)) atTop (nhds 0) :=
    (tendsto_resolventWeight_zero z).comp hindex
  have hlogDilated := tendsto_log_nat_mul_add_sub_log hscale r
  have hlogStep := Real.tendsto_log_nat_add_one_sub_log
  have hmean : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff - resolventLogMean z cutoff) atTop (nhds 1) := by
    have h := (tendsto_resolventLogMean_sub_log hz).neg
    simpa only [neg_sub, neg_neg] using h
  have hcoordinateLinear : Tendsto (fun cutoff : ℕ =>
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
  have hcoordinate : Tendsto (fun cutoff : ℕ =>
      centeredQuadraticMultiplier z cutoff (scale * cutoff + r))
      atTop (nhds ((Real.log scale + 1) ^ 2)) := by
    have h := hcoordinateLinear.pow 2
    apply h.congr'
    filter_upwards with cutoff
    rw [centeredQuadraticMultiplier]
    norm_num [Nat.cast_add, Nat.cast_mul]
  have heffective : Tendsto (fun cutoff : ℕ =>
      resolventCenteredQuadraticWeight z cutoff (scale * cutoff + r))
      atTop (nhds 0) := by
    simpa only [resolventCenteredQuadraticWeight, zero_mul] using
      hweight.mul hcoordinate
  have habsEffective : Tendsto (fun cutoff : ℕ =>
      |resolventCenteredQuadraticWeight z cutoff (scale * cutoff + r)|)
      atTop (nhds 0) := by
    simpa only [abs_zero] using heffective.abs
  let coefficientBound : ℝ := (camera₁ + 4 : ℕ) * (camera₂ + 4 : ℕ)
  have hmajorant : Tendsto (fun cutoff : ℕ =>
      coefficientBound *
        |resolventCenteredQuadraticWeight z cutoff (scale * cutoff + r)|)
      atTop (nhds 0) := by
    simpa only [mul_zero] using habsEffective.const_mul coefficientBound
  have hdom : ∀ cutoff : ℕ,
      |finiteBoundaryTerm (resolventCenteredQuadraticWeight z cutoff)
          cutoff camera₁ camera₂ r| ≤
        coefficientBound *
          |resolventCenteredQuadraticWeight z cutoff (scale * cutoff + r)| := by
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
      rw [abs_mul, abs_mul]
      calc
        |resolventCenteredQuadraticWeight z cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
            |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)| =
          (|finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)|) *
            |resolventCenteredQuadraticWeight z cutoff
              (scale * cutoff + r)| := by ring
        _ ≤ coefficientBound *
            |resolventCenteredQuadraticWeight z cutoff
              (scale * cutoff + r)| :=
          mul_le_mul_of_nonneg_right hproduct (abs_nonneg _)
    · simp only [abs_zero]
      exact mul_nonneg (by positivity) (abs_nonneg _)
  have habs : Tendsto (fun cutoff : ℕ =>
      |finiteBoundaryTerm (resolventCenteredQuadraticWeight z cutoff)
        cutoff camera₁ camera₂ r|) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hdom) hmajorant
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa only [Real.norm_eq_abs] using habs

/-- The complete fixed-width literal boundary vanishes for the centered
quadratic functional weight. -/
theorem tendsto_resolventCenteredQuadratic_finiteBoundarySum_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) :
    Tendsto (fun cutoff =>
      finiteBoundarySum (resolventCenteredQuadraticWeight z cutoff)
        cutoff camera₁ camera₂) atTop (nhds 0) := by
  have hsum := tendsto_finsetSum
    (Finset.range (pairBoundaryWidth camera₁ camera₂))
    (fun r _ => tendsto_resolventCenteredQuadratic_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r)
  simpa only [finiteBoundarySum, Finset.sum_const_zero] using hsum

/-- Entrywise convergence of the complete literal centered-quadratic
coefficient covariance to the second centered camera moment. -/
theorem tendsto_finiteCenteredQuadraticCoefficientCovariance_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff camera i j)
      atTop (nhds (secondCenteredMomentMatrix period camera i j)) := by
  have hcore := tendsto_resolvent_shiftedCoreQuadraticFunctional_apply
    hz hperiod hcamera hcommon i j
  have hboundary := tendsto_resolventCenteredQuadratic_finiteBoundarySum_zero
    hz (hcamera i) (hcamera j)
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hboundaryNormalized : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        finiteBoundarySum (resolventCenteredQuadraticWeight z cutoff)
          cutoff (camera i) (camera j)) atTop (nhds 0) := by
    simpa only [zero_mul] using hinvMass.mul hboundary
  have hlimit := hcore.add hboundaryNormalized
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range
              (pairCoreLength (camera i) (camera j) cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 *
                realProfileProduct (camera i) (camera j) (n + 1) +
        (resolventMass z cutoff)⁻¹ *
          finiteBoundarySum (resolventCenteredQuadraticWeight z cutoff)
            cutoff (camera i) (camera j))
      atTop (nhds (secondCenteredMomentMatrix period camera i j)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  rw [finiteCenteredPolynomialCoefficientCovariance,
    finiteFunctionalCoefficientCovariance]
  simp only [centeredPolynomialMultiplier_X_sq]
  have hnum :
      (∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventWeight z n * centeredQuadraticMultiplier z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n) =
        ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventCenteredQuadraticWeight z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredQuadraticWeight]
  rw [hnum]
  rw [finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary
    (weight := resolventCenteredQuadraticWeight z cutoff)
      (hcamera i) (hcamera j)]
  have hcoreEq :
      (∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventCenteredQuadraticWeight z cutoff n *
            realProfileProduct (camera i) (camera j) (n + 1)) =
        ∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 *
              realProfileProduct (camera i) (camera j) (n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredQuadraticWeight, centeredQuadraticMultiplier]
  rw [hcoreEq]
  simp only [resolventMass]
  ring

/-- Matrix convergence of the complete literal centered-quadratic
coefficient covariance. -/
theorem tendsto_finiteCenteredQuadraticCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff camera)
      atTop (nhds (secondCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff camera i j)
    atTop (nhds fun i j => secondCenteredMomentMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_finiteCenteredQuadraticCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j

/-- Finite entry-sup norm convergence of the literal centered-quadratic
coefficient covariance. -/
theorem tendsto_norm_finiteCenteredQuadraticCoefficientCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff camera -
        secondCenteredMomentMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_finiteCenteredQuadraticCoefficientCovariance
    hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => secondCenteredMomentMatrix period camera)
        atTop (nhds (secondCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- The literal six-camera centered-quadratic covariance converges to the
exact documented matrix `sixCameraSecondCenteredMoment`. -/
theorem
    tendsto_norm_sixCamera_finiteCenteredQuadraticCoefficientCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff sixCamera -
        sixCameraSecondCenteredMoment‖) atTop (nhds 0) := by
  rw [← sixCameraSecondCenteredMoment_eq]
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  exact tendsto_norm_finiteCenteredQuadraticCoefficientCovariance_sub
    hz (by norm_num : 0 < 420) hcamera sixCamera_commonPeriod

/-- Complexification of the second centered periodic camera moment. -/
def complexSecondCenteredMomentMatrix {index : Type*} (period : ℕ)
    (camera : index → ℕ) : Matrix index index ℂ :=
  fun i j => (secondCenteredMomentMatrix period camera i j : ℂ)

/-- Complexified convergence of the complete literal centered-quadratic
coefficient covariance. -/
theorem tendsto_complex_finiteCenteredQuadraticCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff i j =>
      (finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff camera i j : ℂ))
      atTop (nhds (complexSecondCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    (finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff camera i j : ℂ))
    atTop (nhds fun i j =>
      (secondCenteredMomentMatrix period camera i j : ℂ))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hreal := tendsto_finiteCenteredQuadraticCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j
  exact (Complex.continuous_ofReal.tendsto
    (secondCenteredMomentMatrix period camera i j)).comp hreal

/-- The normalized direct finite functional covariance for the centered
quadratic multiplier converges to the complexified second centered moment. -/
theorem tendsto_normalizedFiniteCenteredQuadraticDirectCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalDirectCovariance z cutoff camera
        (centeredPolynomialMultiplier
          (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff))
      atTop (nhds (complexSecondCenteredMomentMatrix period camera)) := by
  apply tendsto_normalizedFiniteFunctionalDirectCovariance_of_coefficients
    hcamera
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredQuadraticCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of the normalized direct
centered-quadratic functional covariance. -/
theorem tendsto_norm_normalizedFiniteCenteredQuadraticDirectCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff camera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff) -
        complexSecondCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredQuadraticDirectCovariance
      hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => complexSecondCenteredMomentMatrix period camera)
        atTop (nhds (complexSecondCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Every compatible finite return-metric colligation family inherits the
centered-quadratic second-moment limit. -/
theorem tendsto_normalizedFiniteCenteredQuadraticReturnMetricCrossCovariance
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
          (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff)
        (endpointMap cutoff) (poisson cutoff))
      atTop (nhds (complexSecondCenteredMomentMatrix period camera)) := by
  apply
    tendsto_normalizedFiniteFunctionalReturnMetricCrossCovariance_of_coefficients
      hcamera endpointMap bulkMap poisson hpoisson hisometry
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredQuadraticCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of every compatible centered-quadratic
return-metric cross covariance family. -/
theorem
    tendsto_norm_normalizedFiniteCenteredQuadraticReturnMetricCrossCovariance_sub
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
            (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSecondCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredQuadraticReturnMetricCrossCovariance
      hz hperiod hcamera hcommon endpointMap bulkMap poisson hpoisson hisometry
  have hconstant :
      Tendsto (fun _ : ℕ => complexSecondCenteredMomentMatrix period camera)
        atTop (nhds (complexSecondCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Complex form of the exact documented six-camera second centered moment. -/
def complexSixCameraSecondCenteredMoment : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (sixCameraSecondCenteredMoment i j : ℂ)

@[simp] theorem complexSecondCenteredMomentMatrix_sixCamera :
    complexSecondCenteredMomentMatrix 420 sixCamera =
      complexSixCameraSecondCenteredMoment := by
  unfold complexSecondCenteredMomentMatrix
    complexSixCameraSecondCenteredMoment
  rw [sixCameraSecondCenteredMoment_eq]

/-- The literal six-camera direct centered-quadratic covariance converges in
matrix norm to the exact documented second centered-moment matrix. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredQuadraticDirectCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff sixCamera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff) -
        complexSixCameraSecondCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexSecondCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredQuadraticDirectCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Exact passage to the six-camera second centered-moment limit for every
finite colligation family satisfying the Poisson and Pythagorean identities. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredQuadraticReturnMetricCrossCovariance_sub
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
            (Polynomial.X ^ 2 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSixCameraSecondCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexSecondCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredQuadraticReturnMetricCrossCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod endpointMap bulkMap poisson hpoisson hisometry)

end

end NativeCarrySpectralWeyl.Limits
