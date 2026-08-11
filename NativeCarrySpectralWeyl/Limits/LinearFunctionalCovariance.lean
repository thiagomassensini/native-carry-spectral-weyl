import NativeCarrySpectralWeyl.Limits.FiniteFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarFunctionalMoment
import NativeCarrySpectralWeyl.Finite.Moments
import Mathlib.Tactic

/-!
# Linear functional covariance limit

This file connects the first scalar resolvent functional moment to the
periodic camera coefficients.  A zero-mean periodic residue is split into two
Dirichlet sums, with scalar weights `w_z(n)` and `log(n+1) w_z(n)`.  Both
weighted residue prefixes are uniformly bounded, so normalization by the
divergent base mass kills the residue.  The fixed literal seed/endpoint tail
is handled separately.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- A Dirichlet sum of a zero-sum periodic real sequence has bounded partial
sums when its scalar weight is eventually antitone and tends to zero. -/
theorem isBounded_range_periodic_weightedSum_of_eventually_antitone
    {q weight : ℕ → ℝ} {period : ℕ}
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0)
    (hweightAnti : ∃ offset : ℕ, Antitone (fun n => weight (offset + n)))
    (hweightZero : Tendsto weight atTop (nhds 0)) :
    IsBoundedUnder (· ≤ ·) atTop (norm ∘ (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n * q n)) := by
  obtain ⟨offset, hanti⟩ := hweightAnti
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
  have hshiftedZero : Tendsto shiftedWeight atTop (nhds 0) :=
    by
      have h := hweightZero.comp (tendsto_add_atTop_nat offset)
      convert h using 1
      ext n
      simp only [shiftedWeight, Function.comp_apply, Nat.add_comm]
  have hshiftedCauchy : CauchySeq shiftedNumerator := by
    have h := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
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

/-- The auxiliary logarithmic resolvent weight used by the linear periodic
residue. -/
def resolventLogWeight (z : ℂ) (n : ℕ) : ℝ :=
  Real.log (n + 1) * resolventWeight z n

/-- The logarithmic resolvent weight tends to zero. -/
theorem tendsto_resolventLogWeight_zero {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (resolventLogWeight z) atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hinvLog : Tendsto (fun n : ℕ =>
      (Real.log ((n : ℝ) + 1))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hproduct := (tendsto_resolventWeight_mul_log_sq_one hz).mul hinvLog
  have hproduct' : Tendsto (fun n : ℕ =>
      (resolventWeight z n * Real.log ((n : ℝ) + 1) ^ 2) *
        (Real.log ((n : ℝ) + 1))⁻¹) atTop (nhds 0) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [hlog.eventually_ne_atTop 0] with n hlog0
  rw [resolventLogWeight]
  field_simp [hlog0]

/-- The logarithmic resolvent weight is antitone after a finite prefix. -/
theorem exists_resolventLogWeight_antitone_natAdd {z : ℂ}
    (hz : z.im ≠ 0) :
    ∃ offset : ℕ, Antitone (fun n : ℕ => resolventLogWeight z (offset + n)) := by
  let c : ℝ := z.re ^ 2 + z.im ^ 2
  have hc : 0 ≤ c := by
    simp only [c]
    positivity
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  obtain ⟨offset, hoffset⟩ :=
    eventually_atTop.1 (hlog.eventually_ge_atTop (c + 1))
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
  have hcx : c + 1 ≤ x := by
    have h := hoffset (offset + m) (Nat.le_add_right offset m)
    simpa only [x, Nat.cast_add, Nat.cast_one] using h
  have hx0 : 0 ≤ x := by linarith
  have hcx2 : c ≤ x ^ 2 := by
    nlinarith [sq_nonneg c]
  have hxxy : x ^ 2 ≤ x * y := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hxy hx0
  have hcxy : c ≤ x * y := hcx2.trans hxxy
  have hdenX : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by
    positivity
  have hdenY : 0 < (y - z.re) ^ 2 + z.im ^ 2 := by
    positivity
  simp only [resolventLogWeight]
  rw [resolventWeight_eq, resolventWeight_eq]
  have hmain : y * (((y - z.re) ^ 2 + z.im ^ 2)⁻¹) ≤
      x * (((x - z.re) ^ 2 + z.im ^ 2)⁻¹) := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv,
      div_le_div_iff₀ hdenY hdenX]
    have hnonneg : 0 ≤
        x * ((y - z.re) ^ 2 + z.im ^ 2) -
          y * ((x - z.re) ^ 2 + z.im ^ 2) := by
      rw [show
        x * ((y - z.re) ^ 2 + z.im ^ 2) -
            y * ((x - z.re) ^ 2 + z.im ^ 2) =
          (y - x) * (x * y - c) by
        simp only [c]
        ring]
      exact mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hcxy)
    exact sub_nonneg.mp hnonneg
  simpa only [x, y, Nat.cast_add, Nat.cast_one] using hmain

/-- The logarithmic scale is negligible compared with the resolvent mass. -/
theorem tendsto_log_div_resolventMass_zero {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log cutoff / resolventMass z cutoff) atTop (nhds 0) := by
  have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
      atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hcubicSuccBase : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 3 / ((cutoff : ℝ) + 1))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp hcastSucc
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
  have hcubicSucc : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 3 / cutoff) atTop (nhds 0) := by
    have h := hcubicSuccBase.mul hsuccRatio
    have h' : Tendsto (fun cutoff : ℕ =>
        (Real.log ((cutoff : ℝ) + 1) ^ 3 / ((cutoff : ℝ) + 1)) *
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
      Real.log cutoff * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      exact div_nonneg
        (mul_nonneg (Real.log_nonneg (by exact_mod_cast hcutoff)) (sq_nonneg _))
        (by exact_mod_cast hcutoffNat.le)
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      have hcutoffPos : (0 : ℝ) < cutoff := by exact_mod_cast hcutoffNat
      have hlogLe : Real.log (cutoff : ℝ) ≤
          Real.log ((cutoff : ℝ) + 1) := by
        exact Real.strictMonoOn_log.monotoneOn
          (by exact Set.mem_Ioi.mpr hcutoffPos)
          (by exact Set.mem_Ioi.mpr (by positivity)) (by linarith)
      exact div_le_div_of_nonneg_right (by
        calc
          Real.log (cutoff : ℝ) * Real.log ((cutoff : ℝ) + 1) ^ 2 ≤
              Real.log ((cutoff : ℝ) + 1) *
                Real.log ((cutoff : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right hlogLe (sq_nonneg _)
          _ = Real.log ((cutoff : ℝ) + 1) ^ 3 := by ring) hcutoffPos.le
    · exact hcubicSucc
  have hmassRatio := tendsto_resolventMass_div_nat_div_log_sq_one hz
  have hmassRatioInv := hmassRatio.inv₀ (by norm_num)
  have hproduct := hlogFactor.mul hmassRatioInv
  have hproduct' : Tendsto (fun cutoff : ℕ =>
      (Real.log cutoff * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff) *
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

/-- The weighted logarithmic mean itself is negligible compared with the
resolvent mass. -/
theorem tendsto_resolventLogMean_div_mass_zero {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hcorrection := (tendsto_resolventLogMean_sub_log hz).mul hinvMass
  have hlimit := hlog.add hcorrection
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff / resolventMass z cutoff +
        (resolventLogMean z cutoff - Real.log cutoff) *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

/-- A centered zero-mean periodic factor contributes nothing to the first
scalar functional moment. -/
theorem tendsto_resolventCenteredLog_periodicResidue_zero
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) *
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
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hlogPart : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n) atTop (nhds 0) :=
    hinvMass.zero_mul_isBoundedUnder_le hlogWeightScaled
  have hmeanPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n * centered n) atTop (nhds 0) :=
    (tendsto_resolventLogMean_div_mass_zero hz).zero_mul_isBoundedUnder_le
      hweightScaled
  have hlimit := hlogPart.sub hmeanPart
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogWeight z n * centered n -
        (resolventLogMean z cutoff / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n * centered n) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) * centered n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n) -
          resolventLogMean z cutoff *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventWeight z n * centered n := by
    calc
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) * centered n) =
        ∑ n ∈ Finset.range (scale * cutoff),
          (resolventLogWeight z n * centered n -
            resolventLogMean z cutoff *
              (resolventWeight z n * centered n)) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [resolventLogWeight]
          ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum]
  ring

/-- Periodic averaging for the first centered logarithmic resolvent moment. -/
theorem tendsto_resolventCenteredLog_periodicWeightedSum
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) * q n)
      atTop (nhds (((scale : ℝ) * Real.log scale) * periodMean q period)) := by
  have hscalar :=
    tendsto_resolventScaledCenteredLogMoment_div_mass hz hscale
  have hmain : Tendsto (fun cutoff : ℕ =>
      (resolventScaledCenteredLogMoment z scale cutoff /
        resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) * Real.log scale) * periodMean q period)) :=
    hscalar.mul_const (periodMean q period)
  have hresidue := tendsto_resolventCenteredLog_periodicResidue_zero
    hz hperiod hscale hq
  have hlimit := hresidue.add hmain
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) *
                (q n - periodMean q period) +
        (resolventScaledCenteredLogMoment z scale cutoff /
          resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) * Real.log scale) * periodMean q period)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) * q n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) *
              (q n - periodMean q period)) +
          periodMean q period *
            resolventScaledCenteredLogMoment z scale cutoff := by
    rw [resolventScaledCenteredLogMoment, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsum]
  ring

/-- The shifted periodic camera core with the centered linear multiplier
converges entrywise to the documented first moment. -/
theorem tendsto_resolvent_shiftedCoreLinearFunctional_apply
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
            (Real.log (n + 1) - resolventLogMean z cutoff) *
              realProfileProduct (camera i) (camera j) (n + 1))
      atTop (nhds (firstMomentMatrix period camera i j)) := by
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
  have hlimit := tendsto_resolventCenteredLog_periodicWeightedSum
    hz hperiod hscale hq
  rw [hmean] at hlimit
  have htarget :
      (((scale : ℝ) * Real.log scale) *
          periodicProductMean period (camera i) (camera j)) =
        firstMomentMatrix period camera i j := by
    rw [firstMomentMatrix_apply, periodicGramMatrix_apply]
    simp only [slopeOverlap, scale]
    ring
  rw [htarget] at hlimit
  simpa only [pairCoreLength, scale, q] using hlimit

/-- Linear multiplier in the finite centered logarithmic coordinate. -/
def centeredLinearMultiplier (z : ℂ) (cutoff n : ℕ) : ℝ :=
  Real.log (n + 1) - resolventLogMean z cutoff

/-- Product of the resolvent weight with the centered linear multiplier. -/
def resolventCenteredLinearWeight (z : ℂ) (cutoff n : ℕ) : ℝ :=
  resolventWeight z n * centeredLinearMultiplier z cutoff n

@[simp] theorem centeredPolynomialMultiplier_X (z : ℂ) (cutoff n : ℕ) :
    centeredPolynomialMultiplier Polynomial.X z cutoff n =
      centeredLinearMultiplier z cutoff n := by
  simp [centeredPolynomialMultiplier, centeredLinearMultiplier]

/-- Every fixed literal seed/endpoint term vanishes for the centered linear
functional weight. -/
theorem tendsto_resolventCenteredLinear_finiteBoundaryTerm_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (r : ℕ) :
    Tendsto (fun cutoff =>
      finiteBoundaryTerm (resolventCenteredLinearWeight z cutoff)
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
  have hcoordinate : Tendsto (fun cutoff : ℕ =>
      centeredLinearMultiplier z cutoff (scale * cutoff + r))
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
    rw [centeredLinearMultiplier]
    norm_num [Nat.cast_add, Nat.cast_mul]
  have heffective : Tendsto (fun cutoff : ℕ =>
      resolventCenteredLinearWeight z cutoff (scale * cutoff + r))
      atTop (nhds 0) := by
    simpa only [resolventCenteredLinearWeight, zero_mul] using
      hweight.mul hcoordinate
  have habsEffective : Tendsto (fun cutoff : ℕ =>
      |resolventCenteredLinearWeight z cutoff (scale * cutoff + r)|)
      atTop (nhds 0) := by
    simpa only [abs_zero] using heffective.abs
  let coefficientBound : ℝ := (camera₁ + 4 : ℕ) * (camera₂ + 4 : ℕ)
  have hmajorant : Tendsto (fun cutoff : ℕ =>
      coefficientBound *
        |resolventCenteredLinearWeight z cutoff (scale * cutoff + r)|)
      atTop (nhds 0) := by
    simpa only [mul_zero] using habsEffective.const_mul coefficientBound
  have hdom : ∀ cutoff : ℕ,
      |finiteBoundaryTerm (resolventCenteredLinearWeight z cutoff)
          cutoff camera₁ camera₂ r| ≤
        coefficientBound *
          |resolventCenteredLinearWeight z cutoff (scale * cutoff + r)| := by
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
        |resolventCenteredLinearWeight z cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
            |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)| =
          (|finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)|) *
            |resolventCenteredLinearWeight z cutoff (scale * cutoff + r)| := by
              ring
        _ ≤ coefficientBound *
            |resolventCenteredLinearWeight z cutoff (scale * cutoff + r)| :=
          mul_le_mul_of_nonneg_right hproduct (abs_nonneg _)
    · simp only [abs_zero]
      exact mul_nonneg (by positivity) (abs_nonneg _)
  have habs : Tendsto (fun cutoff : ℕ =>
      |finiteBoundaryTerm (resolventCenteredLinearWeight z cutoff)
        cutoff camera₁ camera₂ r|) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hdom) hmajorant
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa only [Real.norm_eq_abs] using habs

/-- The complete fixed-width literal boundary vanishes for the centered
linear functional weight. -/
theorem tendsto_resolventCenteredLinear_finiteBoundarySum_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) :
    Tendsto (fun cutoff =>
      finiteBoundarySum (resolventCenteredLinearWeight z cutoff)
        cutoff camera₁ camera₂) atTop (nhds 0) := by
  have hsum := tendsto_finsetSum
    (Finset.range (pairBoundaryWidth camera₁ camera₂))
    (fun r _ => tendsto_resolventCenteredLinear_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r)
  simpa only [finiteBoundarySum, Finset.sum_const_zero] using hsum

/-- Entrywise convergence of the complete literal centered-linear coefficient
covariance to the first camera moment. -/
theorem tendsto_finiteCenteredLinearCoefficientCovariance_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance Polynomial.X z cutoff
        camera i j) atTop (nhds (firstMomentMatrix period camera i j)) := by
  have hcore := tendsto_resolvent_shiftedCoreLinearFunctional_apply
    hz hperiod hcamera hcommon i j
  have hboundary := tendsto_resolventCenteredLinear_finiteBoundarySum_zero
    hz (hcamera i) (hcamera j)
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hboundaryNormalized : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        finiteBoundarySum (resolventCenteredLinearWeight z cutoff)
          cutoff (camera i) (camera j)) atTop (nhds 0) := by
    simpa only [zero_mul] using hinvMass.mul hboundary
  have hlimit := hcore.add hboundaryNormalized
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range
              (pairCoreLength (camera i) (camera j) cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) *
                realProfileProduct (camera i) (camera j) (n + 1) +
        (resolventMass z cutoff)⁻¹ *
          finiteBoundarySum (resolventCenteredLinearWeight z cutoff)
            cutoff (camera i) (camera j))
      atTop (nhds (firstMomentMatrix period camera i j)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  rw [finiteCenteredPolynomialCoefficientCovariance,
    finiteFunctionalCoefficientCovariance]
  simp only [centeredPolynomialMultiplier_X]
  have hnum :
      (∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventWeight z n * centeredLinearMultiplier z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n) =
        ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventCenteredLinearWeight z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredLinearWeight]
  rw [hnum]
  rw [finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary
    (weight := resolventCenteredLinearWeight z cutoff)
      (hcamera i) (hcamera j)]
  have hcoreEq :
      (∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventCenteredLinearWeight z cutoff n *
            realProfileProduct (camera i) (camera j) (n + 1)) =
        ∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) *
              realProfileProduct (camera i) (camera j) (n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredLinearWeight, centeredLinearMultiplier]
  rw [hcoreEq]
  simp only [resolventMass]
  ring

/-- Matrix convergence of the complete literal centered-linear coefficient
covariance. -/
theorem tendsto_finiteCenteredLinearCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance Polynomial.X z cutoff
        camera) atTop (nhds (firstMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    finiteCenteredPolynomialCoefficientCovariance Polynomial.X z cutoff
      camera i j) atTop (nhds fun i j => firstMomentMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_finiteCenteredLinearCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j

/-- Finite entry-sup norm convergence of the literal centered-linear
coefficient covariance. -/
theorem tendsto_norm_finiteCenteredLinearCoefficientCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance Polynomial.X z cutoff
          camera - firstMomentMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_finiteCenteredLinearCoefficientCovariance
    hz hperiod hcamera hcommon
  have hconstant : Tendsto (fun _ : ℕ => firstMomentMatrix period camera)
      atTop (nhds (firstMomentMatrix period camera)) := tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- The literal six-camera centered-linear covariance converges to the exact
documented matrix `sixCameraFirstMoment`. -/
theorem tendsto_norm_sixCamera_finiteCenteredLinearCoefficientCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance Polynomial.X z cutoff
          sixCamera - sixCameraFirstMoment‖) atTop (nhds 0) := by
  rw [← sixCameraFirstMoment_eq]
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  exact tendsto_norm_finiteCenteredLinearCoefficientCovariance_sub
    hz (by norm_num : 0 < 420) hcamera sixCamera_commonPeriod

/-- Complexification of the first periodic camera moment. -/
def complexFirstMomentMatrix {index : Type*} (period : ℕ)
    (camera : index → ℕ) : Matrix index index ℂ :=
  fun i j => (firstMomentMatrix period camera i j : ℂ)

/-- Complexified convergence of the complete literal centered-linear
coefficient covariance. -/
theorem tendsto_complex_finiteCenteredLinearCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff i j =>
      (finiteCenteredPolynomialCoefficientCovariance Polynomial.X z cutoff
        camera i j : ℂ)) atTop
      (nhds (complexFirstMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    (finiteCenteredPolynomialCoefficientCovariance Polynomial.X z cutoff
      camera i j : ℂ)) atTop
    (nhds fun i j => (firstMomentMatrix period camera i j : ℂ))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hreal := tendsto_finiteCenteredLinearCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j
  exact (Complex.continuous_ofReal.tendsto
    (firstMomentMatrix period camera i j)).comp hreal

/-- The normalized direct finite functional covariance for the centered
linear multiplier converges to the complexified first camera moment. -/
theorem tendsto_normalizedFiniteCenteredLinearDirectCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalDirectCovariance z cutoff camera
        (centeredPolynomialMultiplier Polynomial.X z cutoff))
      atTop (nhds (complexFirstMomentMatrix period camera)) := by
  apply tendsto_normalizedFiniteFunctionalDirectCovariance_of_coefficients
    hcamera
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredLinearCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of the normalized direct centered-linear
functional covariance. -/
theorem tendsto_norm_normalizedFiniteCenteredLinearDirectCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff camera
          (centeredPolynomialMultiplier Polynomial.X z cutoff) -
        complexFirstMomentMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_normalizedFiniteCenteredLinearDirectCovariance
    hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => complexFirstMomentMatrix period camera)
        atTop (nhds (complexFirstMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Every compatible finite return-metric colligation family inherits the
centered-linear first-moment limit. -/
theorem tendsto_normalizedFiniteCenteredLinearReturnMetricCrossCovariance
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
        (centeredPolynomialMultiplier Polynomial.X z cutoff)
        (endpointMap cutoff) (poisson cutoff))
      atTop (nhds (complexFirstMomentMatrix period camera)) := by
  apply
    tendsto_normalizedFiniteFunctionalReturnMetricCrossCovariance_of_coefficients
      hcamera endpointMap bulkMap poisson hpoisson hisometry
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredLinearCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of every compatible centered-linear
return-metric cross covariance family. -/
theorem
    tendsto_norm_normalizedFiniteCenteredLinearReturnMetricCrossCovariance_sub
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
          (centeredPolynomialMultiplier Polynomial.X z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexFirstMomentMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredLinearReturnMetricCrossCovariance
      hz hperiod hcamera hcommon endpointMap bulkMap poisson hpoisson hisometry
  have hconstant :
      Tendsto (fun _ : ℕ => complexFirstMomentMatrix period camera)
        atTop (nhds (complexFirstMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Complex form of the exact documented six-camera first-moment target. -/
def complexSixCameraFirstMoment : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (sixCameraFirstMoment i j : ℂ)

@[simp] theorem complexFirstMomentMatrix_sixCamera :
    complexFirstMomentMatrix 420 sixCamera = complexSixCameraFirstMoment := by
  unfold complexFirstMomentMatrix complexSixCameraFirstMoment
  rw [sixCameraFirstMoment_eq]

/-- The literal six-camera direct centered-linear covariance converges in
matrix norm to the exact documented first-moment matrix. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredLinearDirectCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff sixCamera
          (centeredPolynomialMultiplier Polynomial.X z cutoff) -
        complexSixCameraFirstMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexFirstMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredLinearDirectCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Exact passage to the six-camera first-moment limit for every finite
colligation family satisfying the Poisson and Pythagorean identities. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredLinearReturnMetricCrossCovariance_sub
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
          (centeredPolynomialMultiplier Polynomial.X z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSixCameraFirstMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexFirstMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredLinearReturnMetricCrossCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod endpointMap bulkMap poisson hpoisson hisometry)

end

end NativeCarrySpectralWeyl.Limits
