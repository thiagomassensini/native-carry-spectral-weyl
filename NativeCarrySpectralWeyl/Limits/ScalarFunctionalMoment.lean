import NativeCarrySpectralWeyl.Limits.ResolventLogMean
import Mathlib.Tactic

/-!
# First scalar moment of the resolvent functional limit

For a fixed positive natural scale `ℓ`, this file studies the scalar statistic

`A_M(z)⁻¹ ∑_{n < ℓ M} (log(n+1) - μ_M(z)) w_z(n)`.

The proof is discrete.  The increment of the same sum centered at `log M`
splits into a fixed-width boundary block and the change from `log M` to
`log(M+1)`.  Slow variation of the resolvent weight then gives the limiting
increment, and summation of a little-o remainder yields the first moment
predicted by the functional-limit notes.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- A fixed additive displacement after a positive natural dilation does not
change the resolvent weight asymptotically. -/
theorem tendsto_resolventWeight_nat_mul_add_div {z : ℂ} (hz : z.im ≠ 0)
    {scale : ℕ} (hscale : 0 < scale) (offset : ℕ) :
    Tendsto (fun cutoff : ℕ =>
      resolventWeight z (scale * cutoff + offset) / resolventWeight z cutoff)
      atTop (nhds 1) := by
  let base : ℕ → ℝ := fun n => (n : ℝ) + 1
  let dilated : ℕ → ℝ := fun n => (scale * n + offset : ℕ) + 1
  have hbase : Tendsto base atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hdilatedNat : Tendsto (fun n : ℕ => scale * n + offset) atTop atTop :=
    (tendsto_add_atTop_nat offset).comp (tendsto_nat_const_mul_atTop hscale)
  have hdilated : Tendsto dilated atTop atTop := by
    exact Filter.tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.comp hdilatedNat)
  have hbaseDen : Tendsto (fun n =>
      ((Real.log (base n) - z.re) ^ 2 + z.im ^ 2) / Real.log (base n) ^ 2)
      atTop (nhds 1) := (tendsto_resolventDenominator_div_log_sq z).comp hbase
  have hdilatedDen : Tendsto (fun n =>
      ((Real.log (dilated n) - z.re) ^ 2 + z.im ^ 2) /
        Real.log (dilated n) ^ 2) atTop (nhds 1) :=
    (tendsto_resolventDenominator_div_log_sq z).comp hdilated
  have hlinearRatio : Tendsto (fun n : ℕ => dilated n / base n)
      atTop (nhds (scale : ℝ)) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      ((offset : ℝ) + 1) 1 scale (d := 1) (by norm_num)
    convert h using 1
    · ext n
      simp only [base, dilated, Nat.cast_add, Nat.cast_mul]
      ring
    · norm_num
  have hlogDifference : Tendsto (fun n : ℕ =>
      Real.log (dilated n) - Real.log (base n)) atTop
      (nhds (Real.log scale)) := by
    have hlogRatio :=
      (Real.continuousAt_log (Nat.cast_ne_zero.mpr hscale.ne')).tendsto.comp
        hlinearRatio
    apply hlogRatio.congr'
    filter_upwards with n
    change Real.log (dilated n / base n) =
      Real.log (dilated n) - Real.log (base n)
    rw [Real.log_div (by positivity : dilated n ≠ 0)
      (by positivity : base n ≠ 0)]
  have hbaseLog : Tendsto (fun n => Real.log (base n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hbase
  have hbaseLogInv : Tendsto (fun n => (Real.log (base n))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hbaseLog
  have hlogRatio : Tendsto (fun n : ℕ =>
      Real.log (dilated n) / Real.log (base n)) atTop (nhds 1) := by
    have hcorrection := hlogDifference.mul hbaseLogInv
    have honeAdd : Tendsto (fun n : ℕ => 1 +
        (Real.log (dilated n) - Real.log (base n)) *
          (Real.log (base n))⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hcorrection
    apply honeAdd.congr'
    filter_upwards [hbaseLog.eventually_ne_atTop 0] with n hlog0
    field_simp [hlog0]
    ring
  have hdenRatio : Tendsto (fun n : ℕ =>
      (((Real.log (dilated n) - z.re) ^ 2 + z.im ^ 2) /
        ((Real.log (base n) - z.re) ^ 2 + z.im ^ 2))) atTop (nhds 1) := by
    have hcomb := (hdilatedDen.mul (hlogRatio.pow 2)).div hbaseDen (by norm_num)
    have hcomb' : Tendsto (fun n : ℕ =>
        ((((Real.log (dilated n) - z.re) ^ 2 + z.im ^ 2) /
            Real.log (dilated n) ^ 2) *
          (Real.log (dilated n) / Real.log (base n)) ^ 2) /
            (((Real.log (base n) - z.re) ^ 2 + z.im ^ 2) /
              Real.log (base n) ^ 2)) atTop (nhds 1) := by
      convert hcomb using 1
      · ext n
        rfl
      · norm_num
    apply hcomb'.congr'
    filter_upwards [hbaseLog.eventually_ne_atTop 0,
      (Real.tendsto_log_atTop.comp hdilated).eventually_ne_atTop 0]
      with n hb hd
    change Real.log (dilated n) ≠ 0 at hd
    have hbaseDen0 : (Real.log (base n) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
      ne_of_gt (by positivity)
    field_simp [hb, hd, hbaseDen0]
  have hdenRatioInv : Tendsto (fun n : ℕ =>
      (((Real.log (dilated n) - z.re) ^ 2 + z.im ^ 2) /
        ((Real.log (base n) - z.re) ^ 2 + z.im ^ 2))⁻¹) atTop (nhds 1) := by
    simpa using hdenRatio.inv₀ (by norm_num)
  apply hdenRatioInv.congr'
  filter_upwards with n
  simp only [resolventWeight_eq, base, dilated, Nat.cast_add, Nat.cast_mul]
  have hbaseDen0 : (Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  have hdilatedDen0 :
      (Real.log ((scale : ℝ) * n + offset + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  field_simp [hbaseDen0, hdilatedDen0]

/-- The logarithmic coordinate of a fixed displaced dilation differs from
`log M` by `log ℓ` asymptotically. -/
theorem tendsto_log_nat_mul_add_sub_log {scale : ℕ} (hscale : 0 < scale)
    (offset : ℕ) :
    Tendsto (fun cutoff : ℕ =>
      Real.log (scale * cutoff + offset + 1) - Real.log (cutoff + 1))
      atTop (nhds (Real.log scale)) := by
  let base : ℕ → ℝ := fun n => (n : ℝ) + 1
  let dilated : ℕ → ℝ := fun n => (scale * n + offset : ℕ) + 1
  have hlinearRatio : Tendsto (fun n : ℕ => dilated n / base n)
      atTop (nhds (scale : ℝ)) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      ((offset : ℝ) + 1) 1 scale (d := 1) (by norm_num)
    convert h using 1
    · ext n
      simp only [base, dilated, Nat.cast_add, Nat.cast_mul]
      ring
    · norm_num
  have hlogRatio :=
    (Real.continuousAt_log (Nat.cast_ne_zero.mpr hscale.ne')).tendsto.comp
      hlinearRatio
  apply hlogRatio.congr'
  filter_upwards with n
  simp only [Function.comp_apply, base, dilated, Nat.cast_add, Nat.cast_mul]
  change Real.log (((scale : ℝ) * n + offset + 1) / ((n : ℝ) + 1)) =
    Real.log (scale * n + offset + 1) - Real.log (n + 1)
  rw [Real.log_div (by positivity : (scale : ℝ) * n + offset + 1 ≠ 0)
    (by positivity : (n : ℝ) + 1 ≠ 0)]

/-- The new fixed-width block appearing when the cutoff changes from `M` to
`M+1`, centered at the new logarithmic scale. -/
def resolventScaledLogBoundary (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ r ∈ Finset.range scale,
    (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) *
      resolventWeight z (scale * cutoff + r)

/-- First logarithmic moment below `ℓ M`, centered at `log M`. -/
def resolventScaledLogMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - Real.log cutoff) * resolventWeight z n

/-- Exact increment identity for the scaled first logarithmic moment. -/
theorem resolventScaledLogMoment_succ (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogMoment z scale (cutoff + 1) -
        resolventScaledLogMoment z scale cutoff =
      resolventScaledLogBoundary z scale cutoff -
        (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventMass z (scale * cutoff) := by
  rw [resolventScaledLogMoment, resolventScaledLogMoment,
    resolventScaledLogBoundary, resolventMass]
  rw [Nat.mul_add, Nat.mul_one, Finset.sum_range_add]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcenter :
      (∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log (cutoff + 1)) * resolventWeight z n) -
        ∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log cutoff) * resolventWeight z n =
        -(Real.log (cutoff + 1) - Real.log cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff), resolventWeight z n := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [show
      (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) *
            resolventWeight z x) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) *
              resolventWeight z (scale * cutoff + x)) -
        (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log cutoff) * resolventWeight z x) =
        ((∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) *
              resolventWeight z x) -
          (∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log cutoff) *
              resolventWeight z x)) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) *
              resolventWeight z (scale * cutoff + x)) by ring]
  rw [hcenter]
  ring

/-- The new logarithmic boundary block, normalized by the endpoint weight,
converges to `ℓ log ℓ`. -/
theorem tendsto_resolventScaledLogBoundary_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogBoundary z scale cutoff / resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale)) := by
  have hterm : ∀ r ∈ Finset.range scale,
      Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
        atTop (nhds (Real.log scale)) := by
    intro r _
    simpa only [mul_one] using
      (tendsto_log_nat_mul_add_sub_log hscale r).mul
        (tendsto_resolventWeight_nat_mul_add_div hz hscale r)
  have hsum := tendsto_finsetSum (Finset.range scale) hterm
  have hsum' : Tendsto (fun cutoff : ℕ =>
      ∑ r ∈ Finset.range scale,
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [resolventScaledLogBoundary, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hweight]

/-- The change-of-center term at the scaled cutoff, normalized by the endpoint
weight, converges to `ℓ`. -/
theorem tendsto_resolventScaledLogCentering_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventMass z (scale * cutoff) / resolventWeight z cutoff)
      atTop (nhds (scale : ℝ)) := by
  have hproduct :=
    (tendsto_nat_mul_log_succ_sub_log_one.mul
      (tendsto_resolventMass_nat_mul_div hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff) *
          (resolventMass z cutoff / resolventScale z cutoff))
      atTop (nhds (scale : ℝ)) := by
    simpa using hproduct
  apply hlimit.congr'
  filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
  have hcutoffNat : 0 < cutoff := lt_of_lt_of_le Nat.zero_lt_one hcutoff
  have hcutoff0 : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat.ne'
  have hweight0 : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  have hmass0 : resolventMass z cutoff ≠ 0 := by
    rw [resolventMass]
    exact ne_of_gt (Finset.sum_pos' (fun n _ => (resolventWeight_pos hz n).le)
      ⟨0, Finset.mem_range.mpr hcutoffNat, resolventWeight_pos hz 0⟩)
  rw [resolventScale]
  field_simp [hcutoff0, hweight0, hmass0]

/-- Increment after subtracting the predicted first-moment main term. -/
def resolventScaledLogMomentIncrementError
    (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  resolventScaledLogBoundary z scale cutoff -
    (Real.log (cutoff + 1) - Real.log cutoff) *
      resolventMass z (scale * cutoff) -
    ((scale : ℝ) * (Real.log scale - 1)) * resolventWeight z cutoff

/-- Sum of the scaled first-moment increment errors. -/
def resolventScaledLogMomentError (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    resolventScaledLogMomentIncrementError z scale n

/-- Exact telescoping identity for the scaled first-moment error. -/
theorem resolventScaledLogMomentError_eq (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogMomentError z scale cutoff =
      resolventScaledLogMoment z scale cutoff -
        ((scale : ℝ) * (Real.log scale - 1)) * resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventScaledLogMomentError, resolventScaledLogMoment,
        resolventMass]
  | succ cutoff ih =>
      rw [resolventScaledLogMomentError, Finset.sum_range_succ]
      change resolventScaledLogMomentError z scale cutoff +
        resolventScaledLogMomentIncrementError z scale cutoff = _
      rw [ih, resolventScaledLogMomentIncrementError]
      have hmoment := resolventScaledLogMoment_succ z scale cutoff
      simp only [resolventMass, Finset.sum_range_succ]
      simp only [resolventMass] at hmoment
      change resolventScaledLogMoment z scale (cutoff + 1) -
          resolventScaledLogMoment z scale cutoff = _ at hmoment
      linarith

/-- The scaled logarithmic first moment centered at `log M` has limit
`ℓ (log ℓ - 1)` after normalization by the base mass `A_M`. -/
theorem tendsto_resolventScaledLogMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogMoment z scale cutoff / resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) * (Real.log scale - 1))) := by
  have hboundary := tendsto_resolventScaledLogBoundary_div_weight hz hscale
  have hcentering := tendsto_resolventScaledLogCentering_div_weight hz hscale
  have hconstant : Tendsto (fun _ : ℕ =>
      (scale : ℝ) * (Real.log scale - 1)) atTop
      (nhds ((scale : ℝ) * (Real.log scale - 1))) := tendsto_const_nhds
  have hincrementRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogMomentIncrementError z scale cutoff /
        resolventWeight z cutoff) atTop (nhds 0) := by
    have hlimit := (hboundary.sub hcentering).sub hconstant
    have hlimit' : Tendsto (fun cutoff : ℕ =>
        resolventScaledLogBoundary z scale cutoff / resolventWeight z cutoff -
          (Real.log (cutoff + 1) - Real.log cutoff) *
              resolventMass z (scale * cutoff) / resolventWeight z cutoff -
            (scale : ℝ) * (Real.log scale - 1))
        atTop (nhds 0) := by
      convert hlimit using 1
      ring
    apply hlimit'.congr'
    filter_upwards with cutoff
    have hweight : resolventWeight z cutoff ≠ 0 :=
      ne_of_gt (resolventWeight_pos hz cutoff)
    rw [resolventScaledLogMomentIncrementError]
    field_simp [hweight]
  have hincrementSmall :
      (resolventScaledLogMomentIncrementError z scale) =o[atTop]
        resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      (resolventScaledLogMomentError z scale) =o[atTop] resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff,
        resolventScaledLogMomentIncrementError z scale n) =o[atTop]
      (fun cutoff => ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogMomentError z scale cutoff / resolventMass z cutoff)
      atTop (nhds 0) := herrorSmall.tendsto_div_nhds_zero
  have hshifted := herrorRatio.add_const
    ((scale : ℝ) * (Real.log scale - 1))
  have hshifted' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogMomentError z scale cutoff / resolventMass z cutoff +
        (scale : ℝ) * (Real.log scale - 1)) atTop
      (nhds ((scale : ℝ) * (Real.log scale - 1))) := by
    convert hshifted using 1
    ring
  apply hshifted'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventScaledLogMomentError_eq]
  field_simp [hmass]
  ring

/-- First logarithmic moment below `ℓ M`, centered at the weighted logarithmic
mean `μ_M(z)`. -/
def resolventScaledCenteredLogMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - resolventLogMean z cutoff) * resolventWeight z n

/-- The first centered scalar moment from the functional-limit notes:
its limit is `ℓ log ℓ`. -/
theorem tendsto_resolventScaledCenteredLogMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledCenteredLogMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale)) := by
  have hraw := tendsto_resolventScaledLogMoment_div_mass hz hscale
  have hmean : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff - resolventLogMean z cutoff) atTop (nhds 1) := by
    have h := (tendsto_resolventLogMean_sub_log hz).neg
    simpa only [neg_sub, neg_neg] using h
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hcorrection := hmean.mul hmassRatio
  have hlimit := hraw.add hcorrection
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogMoment z scale cutoff / resolventMass z cutoff +
        (Real.log cutoff - resolventLogMean z cutoff) *
          (resolventMass z (scale * cutoff) / resolventMass z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale)) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  have hdecomp :
      resolventScaledCenteredLogMoment z scale cutoff =
        resolventScaledLogMoment z scale cutoff +
          (Real.log cutoff - resolventLogMean z cutoff) *
            resolventMass z (scale * cutoff) := by
    rw [resolventScaledCenteredLogMoment, resolventScaledLogMoment,
      resolventMass]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - resolventLogMean z cutoff) * resolventWeight z n =
          (Real.log (n + 1) - Real.log cutoff) * resolventWeight z n +
            (Real.log cutoff - resolventLogMean z cutoff) *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hdecomp]
  field_simp [hmass]

end

end NativeCarrySpectralWeyl.Limits
