import NativeCarrySpectralWeyl.Limits.ScalarThirdFunctionalMoment
import Mathlib.Tactic

/-!
# Fourth scalar moment of the resolvent functional limit

For a fixed positive natural scale `ℓ`, this file proves

`A_M(z)⁻¹ ∑_{n < ℓ M} (log(n+1) - μ_M(z))⁴ w_z(n)
  → ℓ (log(ℓ)⁴ + 6 log(ℓ)² - 8 log(ℓ) + 9)`.

The proof continues the exact discrete recurrence used for moments one
through three.  The quartic increment has a fixed-width boundary block and
the binomial change-of-center terms with coefficients `-4, 6, -4, 1`.
Only the logarithmic step times the already proved cubic raw moment survives
at endpoint-weight scale.  Little-o summation gives the raw fourth moment,
and `log M - μ_M(z) → 1` converts it to the weighted-mean-centered form.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- The fixed-width quartic boundary block created when the cutoff changes
from `M` to `M+1`. -/
def resolventScaledLogFourthBoundary (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ r ∈ Finset.range scale,
    (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 4 *
      resolventWeight z (scale * cutoff + r)

/-- Fourth logarithmic moment below `ℓ M`, centered at `log M`. -/
def resolventScaledLogFourthMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - Real.log cutoff) ^ 4 * resolventWeight z n

/-- The normalized quartic boundary block converges to `ℓ log(ℓ)⁴`. -/
theorem tendsto_resolventScaledLogFourthBoundary_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFourthBoundary z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 4)) := by
  have hterm : ∀ r ∈ Finset.range scale,
      Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 4 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
        atTop (nhds (Real.log scale ^ 4)) := by
    intro r _
    simpa only [mul_one] using
      (tendsto_log_nat_mul_add_sub_log hscale r).pow 4 |>.mul
        (tendsto_resolventWeight_nat_mul_add_div hz hscale r)
  have hsum := tendsto_finsetSum (Finset.range scale) hterm
  have hsum' : Tendsto (fun cutoff : ℕ =>
      ∑ r ∈ Finset.range scale,
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 4 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 4)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [resolventScaledLogFourthBoundary, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hweight]

/-- The logarithmic step times the third scaled moment, normalized by the
endpoint weight, converges to the raw third-moment coefficient. -/
theorem tendsto_logStep_mul_resolventScaledLogCubeMoment_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogCubeMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 3 - 3 * Real.log scale ^ 2 +
          6 * Real.log scale - 6))) := by
  have hproduct :=
    (tendsto_nat_mul_log_succ_sub_log_one.mul
      (tendsto_resolventScaledLogCubeMoment_div_mass hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) *
        (resolventScaledLogCubeMoment z scale cutoff /
          resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 3 - 3 * Real.log scale ^ 2 +
          6 * Real.log scale - 6))) := by
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

/-- The squared logarithmic step times the second scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_sq_mul_resolventScaledLogSqMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogSqMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_mul_resolventScaledLogSqMoment_div_weight hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogSqMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The cubed logarithmic step times the first scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_cube_mul_resolventScaledLogMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_sq_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fourth-power change-of-center correction is negligible relative to
the endpoint weight. -/
theorem tendsto_logStep_fourth_mul_resolventMass_nat_mul_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventMass z (scale * cutoff) /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_cube_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventMass z (scale * cutoff) /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- Exact increment identity for the scaled fourth logarithmic moment. -/
theorem resolventScaledLogFourthMoment_succ (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogFourthMoment z scale (cutoff + 1) -
        resolventScaledLogFourthMoment z scale cutoff =
      resolventScaledLogFourthBoundary z scale cutoff -
        4 * (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogCubeMoment z scale cutoff +
        6 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogSqMoment z scale cutoff -
        4 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogMoment z scale cutoff +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventMass z (scale * cutoff) := by
  rw [resolventScaledLogFourthMoment, resolventScaledLogFourthMoment,
    resolventScaledLogFourthBoundary, resolventScaledLogCubeMoment,
    resolventScaledLogSqMoment, resolventScaledLogMoment, resolventMass]
  rw [Nat.mul_add, Nat.mul_one, Finset.sum_range_add]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcenter :
      (∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 4 *
            resolventWeight z n) -
        ∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log cutoff) ^ 4 *
            resolventWeight z n =
        -4 * (Real.log (cutoff + 1) - Real.log cutoff) *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n +
          6 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n -
          4 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n +
          (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            ∑ n ∈ Finset.range (scale * cutoff), resolventWeight z n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 4 *
              resolventWeight z n -
            (Real.log (n + 1) - Real.log cutoff) ^ 4 *
              resolventWeight z n =
          (-4 * (Real.log (cutoff + 1) - Real.log cutoff)) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n) +
            (6 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) -
            (4 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3) *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [show
      (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 4 *
            resolventWeight z x) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 4 *
              resolventWeight z (scale * cutoff + x)) -
        (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 4 *
            resolventWeight z x) =
        ((∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 4 *
              resolventWeight z x) -
          (∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 4 *
              resolventWeight z x)) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 4 *
              resolventWeight z (scale * cutoff + x)) by ring]
  rw [hcenter]
  ring

/-- Increment after subtracting the predicted raw fourth-moment main term. -/
def resolventScaledLogFourthMomentIncrementError
    (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  resolventScaledLogFourthBoundary z scale cutoff -
    4 * (Real.log (cutoff + 1) - Real.log cutoff) *
      resolventScaledLogCubeMoment z scale cutoff +
    6 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
      resolventScaledLogSqMoment z scale cutoff -
    4 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
      resolventScaledLogMoment z scale cutoff +
    (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
      resolventMass z (scale * cutoff) -
    ((scale : ℝ) *
      (Real.log scale ^ 4 - 4 * Real.log scale ^ 3 +
        12 * Real.log scale ^ 2 - 24 * Real.log scale + 24)) *
      resolventWeight z cutoff

/-- Sum of the scaled raw fourth-moment increment errors. -/
def resolventScaledLogFourthMomentError (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    resolventScaledLogFourthMomentIncrementError z scale n

/-- The raw fourth-moment increment error is little-o of the endpoint
resolvent weight. -/
theorem tendsto_resolventScaledLogFourthMomentIncrementError_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFourthMomentIncrementError z scale cutoff /
        resolventWeight z cutoff) atTop (nhds 0) := by
  have hboundary :=
    tendsto_resolventScaledLogFourthBoundary_div_weight hz hscale
  have hcubic :=
    tendsto_logStep_mul_resolventScaledLogCubeMoment_div_weight hz hscale
  have hquadratic :=
    tendsto_logStep_sq_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale
  have hlinear :=
    tendsto_logStep_cube_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale
  have hfourth :=
    tendsto_logStep_fourth_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale
  have hconstant : Tendsto (fun _ : ℕ =>
      (scale : ℝ) * (Real.log scale ^ 4 - 4 * Real.log scale ^ 3 +
        12 * Real.log scale ^ 2 - 24 * Real.log scale + 24)) atTop
      (nhds ((scale : ℝ) * (Real.log scale ^ 4 -
        4 * Real.log scale ^ 3 + 12 * Real.log scale ^ 2 -
          24 * Real.log scale + 24))) :=
    tendsto_const_nhds
  have hlimit :=
    (((((hboundary.sub (hcubic.const_mul 4)).add
      (hquadratic.const_mul 6)).sub (hlinear.const_mul 4)).add
        hfourth).sub hconstant)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFourthBoundary z scale cutoff /
          resolventWeight z cutoff -
        4 * ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogCubeMoment z scale cutoff /
              resolventWeight z cutoff) +
        6 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogSqMoment z scale cutoff /
              resolventWeight z cutoff) -
        4 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogMoment z scale cutoff /
              resolventWeight z cutoff) +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventMass z (scale * cutoff) /
              resolventWeight z cutoff -
        (scale : ℝ) * (Real.log scale ^ 4 -
          4 * Real.log scale ^ 3 + 12 * Real.log scale ^ 2 -
            24 * Real.log scale + 24))
      atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  rw [resolventScaledLogFourthMomentIncrementError]
  field_simp [hweight]

/-- Exact telescoping identity for the scaled raw fourth-moment error. -/
theorem resolventScaledLogFourthMomentError_eq
    (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogFourthMomentError z scale cutoff =
      resolventScaledLogFourthMoment z scale cutoff -
        ((scale : ℝ) *
          (Real.log scale ^ 4 - 4 * Real.log scale ^ 3 +
            12 * Real.log scale ^ 2 - 24 * Real.log scale + 24)) *
          resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventScaledLogFourthMomentError,
        resolventScaledLogFourthMoment, resolventMass]
  | succ cutoff ih =>
      rw [resolventScaledLogFourthMomentError, Finset.sum_range_succ]
      change resolventScaledLogFourthMomentError z scale cutoff +
        resolventScaledLogFourthMomentIncrementError z scale cutoff = _
      rw [ih, resolventScaledLogFourthMomentIncrementError]
      have hmoment := resolventScaledLogFourthMoment_succ z scale cutoff
      simp only [resolventMass, Finset.sum_range_succ]
      simp only [resolventMass] at hmoment
      change resolventScaledLogFourthMoment z scale (cutoff + 1) -
          resolventScaledLogFourthMoment z scale cutoff = _ at hmoment
      linarith

/-- The raw scaled fourth logarithmic moment centered at `log M` converges to
`ℓ(log(ℓ)⁴ - 4log(ℓ)³ + 12log(ℓ)² - 24log(ℓ) + 24)`. -/
theorem tendsto_resolventScaledLogFourthMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFourthMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 4 - 4 * Real.log scale ^ 3 +
          12 * Real.log scale ^ 2 - 24 * Real.log scale + 24))) := by
  have hincrementRatio :=
    tendsto_resolventScaledLogFourthMomentIncrementError_div_weight_zero
      hz hscale
  have hincrementSmall :
      (resolventScaledLogFourthMomentIncrementError z scale) =o[atTop]
        resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      (resolventScaledLogFourthMomentError z scale) =o[atTop]
        resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff,
        resolventScaledLogFourthMomentIncrementError z scale n) =o[atTop]
      (fun cutoff => ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFourthMomentError z scale cutoff /
        resolventMass z cutoff) atTop (nhds 0) :=
    herrorSmall.tendsto_div_nhds_zero
  have hshifted := herrorRatio.add_const
    ((scale : ℝ) * (Real.log scale ^ 4 - 4 * Real.log scale ^ 3 +
      12 * Real.log scale ^ 2 - 24 * Real.log scale + 24))
  have hshifted' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFourthMomentError z scale cutoff /
          resolventMass z cutoff +
        (scale : ℝ) * (Real.log scale ^ 4 - 4 * Real.log scale ^ 3 +
          12 * Real.log scale ^ 2 - 24 * Real.log scale + 24))
      atTop (nhds ((scale : ℝ) * (Real.log scale ^ 4 -
        4 * Real.log scale ^ 3 + 12 * Real.log scale ^ 2 -
          24 * Real.log scale + 24))) := by
    convert hshifted using 1
    ring
  apply hshifted'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventScaledLogFourthMomentError_eq]
  field_simp [hmass]
  ring

/-- Fourth logarithmic moment below `ℓ M`, centered at the weighted
logarithmic mean `μ_M(z)`. -/
def resolventScaledCenteredLogFourthMoment (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 *
      resolventWeight z n

/-- The fourth centered scalar moment from the functional-limit recurrence:
its limit is `ℓ(log(ℓ)⁴ + 6log(ℓ)² - 8log(ℓ) + 9)`. -/
theorem tendsto_resolventScaledCenteredLogFourthMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledCenteredLogFourthMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 4 + 6 * Real.log scale ^ 2 -
          8 * Real.log scale + 9))) := by
  have hraw := tendsto_resolventScaledLogFourthMoment_div_mass hz hscale
  have hthird := tendsto_resolventScaledLogCubeMoment_div_mass hz hscale
  have hsecond := tendsto_resolventScaledLogSqMoment_div_mass hz hscale
  have hfirst := tendsto_resolventScaledLogMoment_div_mass hz hscale
  have hmean : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff - resolventLogMean z cutoff) atTop (nhds 1) := by
    have h := (tendsto_resolventLogMean_sub_log hz).neg
    simpa only [neg_sub, neg_neg] using h
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hlimit :=
    ((((hraw.add ((hmean.mul hthird).const_mul 4)).add
      (((hmean.pow 2).mul hsecond).const_mul 6)).add
        (((hmean.pow 3).mul hfirst).const_mul 4)).add
          ((hmean.pow 4).mul hmassRatio))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFourthMoment z scale cutoff /
          resolventMass z cutoff +
        4 * ((Real.log cutoff - resolventLogMean z cutoff) *
          (resolventScaledLogCubeMoment z scale cutoff /
            resolventMass z cutoff)) +
        6 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
          (resolventScaledLogSqMoment z scale cutoff /
            resolventMass z cutoff)) +
        4 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
          (resolventScaledLogMoment z scale cutoff /
            resolventMass z cutoff)) +
        (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
          (resolventMass z (scale * cutoff) / resolventMass z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 4 + 6 * Real.log scale ^ 2 -
          8 * Real.log scale + 9))) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  have hdecomp :
      resolventScaledCenteredLogFourthMoment z scale cutoff =
        resolventScaledLogFourthMoment z scale cutoff +
          4 * (Real.log cutoff - resolventLogMean z cutoff) *
            resolventScaledLogCubeMoment z scale cutoff +
          6 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
            resolventScaledLogSqMoment z scale cutoff +
          4 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
            resolventScaledLogMoment z scale cutoff +
          (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
            resolventMass z (scale * cutoff) := by
    rw [resolventScaledCenteredLogFourthMoment,
      resolventScaledLogFourthMoment, resolventScaledLogCubeMoment,
      resolventScaledLogSqMoment, resolventScaledLogMoment, resolventMass]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - resolventLogMean z cutoff) ^ 4 *
              resolventWeight z n =
          (Real.log (n + 1) - Real.log cutoff) ^ 4 *
              resolventWeight z n +
            4 * (Real.log cutoff - resolventLogMean z cutoff) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n) +
            6 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) +
            4 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [hdecomp]
  field_simp [hmass]

end

end NativeCarrySpectralWeyl.Limits
