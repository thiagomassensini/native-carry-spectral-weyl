import NativeCarrySpectralWeyl.Limits.ResolventWeight
import Mathlib.Tactic

/-!
# Second-order asymptotics of the resolvent logarithmic mean

For the logarithmic resolvent weight `w_z(n)`, this file studies the weighted
logarithmic mean

`μ_M(z) = (sum_{n < M} log(n+1) w_z(n)) / A_M(z)`.

The centered numerator has a discrete telescoping increment.  The already
proved equivalence `A_M(z) ~ M w_z(M)` and the elementary limit
`M log(1 + 1/M) -> 1` make that increment little-o of `w_z(M)`.  Summing the
little-o estimate yields the second-order correction

`μ_M(z) - log M + 1 -> 0`.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- Resolvent-weighted logarithmic first moment. -/
def resolventLogMoment (z : ℂ) (cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    Real.log (n + 1) * resolventWeight z n

/-- Finite resolvent-weighted logarithmic mean `μ_M(z)`. -/
def resolventLogMean (z : ℂ) (cutoff : ℕ) : ℝ :=
  (resolventMass z cutoff)⁻¹ * resolventLogMoment z cutoff

/-- Increment in the centered logarithmic numerator. -/
def resolventLogCenteringIncrement (z : ℂ) (cutoff : ℕ) : ℝ :=
  resolventWeight z cutoff - resolventMass z cutoff *
    (Real.log (cutoff + 1) - Real.log cutoff)

/-- Sum of the centered logarithmic increments. -/
def resolventLogCenteringError (z : ℂ) (cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff, resolventLogCenteringIncrement z n

/-- Exact discrete telescoping identity behind the logarithmic centering. -/
theorem resolventLogCenteringError_eq (z : ℂ) (cutoff : ℕ) :
    resolventLogCenteringError z cutoff =
      resolventLogMoment z cutoff -
        (Real.log cutoff - 1) * resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventLogCenteringError, resolventLogMoment, resolventMass]
  | succ cutoff ih =>
      rw [resolventLogCenteringError, Finset.sum_range_succ]
      change resolventLogCenteringError z cutoff +
        resolventLogCenteringIncrement z cutoff = _
      rw [ih, resolventLogCenteringIncrement]
      simp only [resolventLogMoment, resolventMass, Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The elementary logarithmic step satisfies
`M * (log(M+1) - log M) -> 1`. -/
theorem tendsto_nat_mul_log_succ_sub_log_one :
    Tendsto (fun cutoff : ℕ =>
      (cutoff : ℝ) * (Real.log (cutoff + 1) - Real.log cutoff))
      atTop (nhds 1) := by
  have h := (Real.tendsto_mul_log_one_add_div_atTop 1).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
  have hcutoffNat : cutoff ≠ 0 :=
    Nat.ne_of_gt (Nat.zero_lt_of_lt hcutoff)
  have hcutoffReal : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat
  calc
    ((fun x : ℝ => x * Real.log (1 + 1 / x)) ∘ Nat.cast) cutoff =
        (cutoff : ℝ) * Real.log (1 + 1 / (cutoff : ℝ)) := rfl
    _ = (cutoff : ℝ) *
        Real.log (((cutoff : ℝ) + 1) / (cutoff : ℝ)) := by
          congr 2
          field_simp [hcutoffReal]
    _ = (cutoff : ℝ) *
        (Real.log ((cutoff : ℝ) + 1) - Real.log (cutoff : ℝ)) := by
          rw [Real.log_div (by positivity : (cutoff : ℝ) + 1 ≠ 0)
            hcutoffReal]
    _ = (cutoff : ℝ) *
        (Real.log (cutoff + 1) - Real.log cutoff) := by
          norm_num [Nat.cast_add]

/-- The weighted logarithmic mean has the second-order asymptotic from the
functional-limit notes: `μ_M(z) = log M - 1 + o(1)`. -/
theorem tendsto_resolventLogMean_sub_log_add_one {z : ℂ}
    (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff - Real.log cutoff + 1)
      atTop (nhds 0) := by
  have hmain := (tendsto_resolventMass_div_scale_one hz).mul
    tendsto_nat_mul_log_succ_sub_log_one
  have hscaled : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff / resolventWeight z cutoff) *
        (Real.log (cutoff + 1) - Real.log cutoff))
      atTop (nhds 1) := by
    have heq : (fun cutoff : ℕ =>
        (resolventMass z cutoff / resolventScale z cutoff) *
          ((cutoff : ℝ) *
            (Real.log (cutoff + 1) - Real.log cutoff))) =ᶠ[atTop]
        (fun cutoff : ℕ =>
          (resolventMass z cutoff / resolventWeight z cutoff) *
            (Real.log (cutoff + 1) - Real.log cutoff)) := by
      filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : cutoff ≠ 0 :=
        Nat.ne_of_gt (Nat.zero_lt_of_lt hcutoff)
      have hcutoffReal : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat
      have hweight : resolventWeight z cutoff ≠ 0 :=
        ne_of_gt (resolventWeight_pos hz cutoff)
      rw [resolventScale]
      field_simp [hcutoffReal, hweight]
    simpa only [one_mul] using hmain.congr' heq
  have hincrementRatio : Tendsto (fun cutoff : ℕ =>
      resolventLogCenteringIncrement z cutoff / resolventWeight z cutoff)
      atTop (nhds 0) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have h := hone.sub hscaled
    have heq : (fun cutoff : ℕ =>
        1 - (resolventMass z cutoff / resolventWeight z cutoff) *
          (Real.log (cutoff + 1) - Real.log cutoff)) =ᶠ[atTop]
        (fun cutoff : ℕ => resolventLogCenteringIncrement z cutoff /
          resolventWeight z cutoff) := by
      filter_upwards with cutoff
      have hweight : resolventWeight z cutoff ≠ 0 :=
        ne_of_gt (resolventWeight_pos hz cutoff)
      rw [resolventLogCenteringIncrement]
      field_simp [hweight]
    simpa only [sub_self] using h.congr' heq
  have hincrementSmall :
      resolventLogCenteringIncrement z =o[atTop] resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      resolventLogCenteringError z =o[atTop] resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff, resolventLogCenteringIncrement z n) =o[atTop]
        (fun cutoff =>
          ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventLogCenteringError z cutoff / resolventMass z cutoff)
      atTop (nhds 0) := herrorSmall.tendsto_div_nhds_zero
  apply herrorRatio.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventLogCenteringError_eq, resolventLogMean]
  field_simp [hmass]
  ring

/-- Equivalent form of the second-order correction:
`μ_M(z) - log M -> -1`. -/
theorem tendsto_resolventLogMean_sub_log {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff - Real.log cutoff)
      atTop (nhds (-1)) := by
  have h := (tendsto_resolventLogMean_sub_log_add_one hz).sub_const 1
  simpa only [add_sub_cancel_right, zero_sub] using h

end

end NativeCarrySpectralWeyl.Limits
