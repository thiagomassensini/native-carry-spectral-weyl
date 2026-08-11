import NativeCarrySpectralWeyl.Limits.QuinticFunctionalCovariance
import Mathlib.Tactic

/-!
# Sixth scalar moment of the resolvent functional limit

For a fixed positive natural scale `ℓ`, this file proves

`A_M(z)⁻¹ ∑_{n < ℓ M} (log(n+1) - μ_M(z))⁶ w_z(n)
  → ℓ (log(ℓ)⁶ + 15 log(ℓ)⁴ - 40 log(ℓ)³ +
    135 log(ℓ)² - 264 log(ℓ) + 265)`.

The proof continues the exact discrete recurrence used for moments one
through five.  The sextic increment has a fixed-width boundary block and
the binomial change-of-center terms with coefficients `-6, 15, -20, 15, -6, 1`.
Only the logarithmic step times the already proved quintic raw moment survives
at endpoint-weight scale.  Little-o summation gives the raw sixth moment,
and `log M - μ_M(z) → 1` converts it to the weighted-mean-centered form.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- The fixed-width sextic boundary block created when the cutoff changes
from `M` to `M+1`. -/
def resolventScaledLogSixthBoundary (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ r ∈ Finset.range scale,
    (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 6 *
      resolventWeight z (scale * cutoff + r)

/-- Sixth logarithmic moment below `ℓ M`, centered at `log M`. -/
def resolventScaledLogSixthMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - Real.log cutoff) ^ 6 * resolventWeight z n

/-- The normalized sextic boundary block converges to `ℓ log(ℓ)⁶`. -/
theorem tendsto_resolventScaledLogSixthBoundary_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSixthBoundary z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 6)) := by
  have hterm : ∀ r ∈ Finset.range scale,
      Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 6 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
        atTop (nhds (Real.log scale ^ 6)) := by
    intro r _
    simpa only [mul_one] using
      (tendsto_log_nat_mul_add_sub_log hscale r).pow 6 |>.mul
        (tendsto_resolventWeight_nat_mul_add_div hz hscale r)
  have hsum := tendsto_finsetSum (Finset.range scale) hterm
  have hsum' : Tendsto (fun cutoff : ℕ =>
      ∑ r ∈ Finset.range scale,
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 6 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 6)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [resolventScaledLogSixthBoundary, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hweight]

/-- The logarithmic step times the fifth scaled moment, normalized by the
endpoint weight, converges to the raw fifth-moment coefficient. -/
theorem tendsto_logStep_mul_resolventScaledLogFifthMoment_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogFifthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
          20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
            120 * Real.log scale - 120))) := by
  have hproduct :=
    (tendsto_nat_mul_log_succ_sub_log_one.mul
      (tendsto_resolventScaledLogFifthMoment_div_mass hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) *
        (resolventScaledLogFifthMoment z scale cutoff /
          resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
          20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
            120 * Real.log scale - 120))) := by
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

/-- The squared logarithmic step times the fourth scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_sq_mul_resolventScaledLogFourthMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogFourthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_mul_resolventScaledLogFourthMoment_div_weight hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogFourthMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The cubed logarithmic step times the third scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_cube_mul_resolventScaledLogCubeMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogCubeMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_sq_mul_resolventScaledLogCubeMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogCubeMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fourth-power logarithmic step times the second scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_fourth_mul_resolventScaledLogSqMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventScaledLogSqMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_cube_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogSqMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fifth-power logarithmic step times the first scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_fifth_mul_resolventScaledLogMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          resolventScaledLogMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_fourth_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventScaledLogMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The sixth-power change-of-center correction is negligible relative to
the endpoint weight. -/
theorem tendsto_logStep_sixth_mul_resolventMass_nat_mul_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
          resolventMass z (scale * cutoff) /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_fifth_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            resolventMass z (scale * cutoff) /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- Exact increment identity for the scaled sixth logarithmic moment. -/
theorem resolventScaledLogSixthMoment_succ (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogSixthMoment z scale (cutoff + 1) -
        resolventScaledLogSixthMoment z scale cutoff =
      resolventScaledLogSixthBoundary z scale cutoff -
        6 * (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogFifthMoment z scale cutoff +
        15 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogFourthMoment z scale cutoff -
        20 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogCubeMoment z scale cutoff +
        15 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventScaledLogSqMoment z scale cutoff -
        6 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          resolventScaledLogMoment z scale cutoff +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
          resolventMass z (scale * cutoff) := by
  rw [resolventScaledLogSixthMoment, resolventScaledLogSixthMoment,
    resolventScaledLogSixthBoundary, resolventScaledLogFifthMoment,
    resolventScaledLogFourthMoment, resolventScaledLogCubeMoment,
    resolventScaledLogSqMoment, resolventScaledLogMoment, resolventMass]
  rw [Nat.mul_add, Nat.mul_one, Finset.sum_range_add]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcenter :
      (∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 6 *
            resolventWeight z n) -
        ∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log cutoff) ^ 6 *
            resolventWeight z n =
        -6 * (Real.log (cutoff + 1) - Real.log cutoff) *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 5 *
                resolventWeight z n +
          15 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n -
          20 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n +
          15 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n -
          6 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n +
          (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
            ∑ n ∈ Finset.range (scale * cutoff), resolventWeight z n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [show
      (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 6 *
            resolventWeight z x) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 6 *
              resolventWeight z (scale * cutoff + x)) -
        (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 6 *
            resolventWeight z x) =
        ((∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 6 *
              resolventWeight z x) -
          (∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 6 *
              resolventWeight z x)) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 6 *
              resolventWeight z (scale * cutoff + x)) by ring]
  rw [hcenter]
  ring

/-- Increment after subtracting the predicted raw sixth-moment main term. -/
def resolventScaledLogSixthMomentIncrementError
    (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  resolventScaledLogSixthBoundary z scale cutoff -
    6 * (Real.log (cutoff + 1) - Real.log cutoff) *
      resolventScaledLogFifthMoment z scale cutoff +
    15 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
      resolventScaledLogFourthMoment z scale cutoff -
    20 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
      resolventScaledLogCubeMoment z scale cutoff +
    15 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
      resolventScaledLogSqMoment z scale cutoff -
    6 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
      resolventScaledLogMoment z scale cutoff +
    (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
      resolventMass z (scale * cutoff) -
    ((scale : ℝ) *
      (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
        30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
          360 * Real.log scale ^ 2 - 720 * Real.log scale + 720)) *
      resolventWeight z cutoff

/-- Sum of the scaled raw sixth-moment increment errors. -/
def resolventScaledLogSixthMomentError (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    resolventScaledLogSixthMomentIncrementError z scale n

/-- The raw sixth-moment increment error is little-o of the endpoint
resolvent weight. -/
theorem tendsto_resolventScaledLogSixthMomentIncrementError_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSixthMomentIncrementError z scale cutoff /
        resolventWeight z cutoff) atTop (nhds 0) := by
  have hboundary :=
    tendsto_resolventScaledLogSixthBoundary_div_weight hz hscale
  have hfifth :=
    tendsto_logStep_mul_resolventScaledLogFifthMoment_div_weight hz hscale
  have hfourth :=
    tendsto_logStep_sq_mul_resolventScaledLogFourthMoment_div_weight_zero
      hz hscale
  have hcubic :=
    tendsto_logStep_cube_mul_resolventScaledLogCubeMoment_div_weight_zero
      hz hscale
  have hquadratic :=
    tendsto_logStep_fourth_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale
  have hlinear :=
    tendsto_logStep_fifth_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale
  have hsixth :=
    tendsto_logStep_sixth_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale
  have hconstant : Tendsto (fun _ : ℕ =>
      (scale : ℝ) * (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
        30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
          360 * Real.log scale ^ 2 - 720 * Real.log scale + 720)) atTop
      (nhds ((scale : ℝ) * (Real.log scale ^ 6 -
        6 * Real.log scale ^ 5 + 30 * Real.log scale ^ 4 -
          120 * Real.log scale ^ 3 + 360 * Real.log scale ^ 2 -
            720 * Real.log scale + 720))) :=
    tendsto_const_nhds
  have hlimit :=
    (((((((hboundary.sub (hfifth.const_mul 6)).add
      (hfourth.const_mul 15)).sub (hcubic.const_mul 20)).add
        (hquadratic.const_mul 15)).sub
          (hlinear.const_mul 6)).add hsixth).sub hconstant)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSixthBoundary z scale cutoff /
          resolventWeight z cutoff -
        6 * ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogFifthMoment z scale cutoff /
              resolventWeight z cutoff) +
        15 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogFourthMoment z scale cutoff /
              resolventWeight z cutoff) -
        20 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogCubeMoment z scale cutoff /
              resolventWeight z cutoff) +
        15 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventScaledLogSqMoment z scale cutoff /
              resolventWeight z cutoff) -
        6 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            resolventScaledLogMoment z scale cutoff /
              resolventWeight z cutoff) +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
            resolventMass z (scale * cutoff) /
              resolventWeight z cutoff -
        (scale : ℝ) * (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
          30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
            360 * Real.log scale ^ 2 - 720 * Real.log scale + 720))
      atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  rw [resolventScaledLogSixthMomentIncrementError]
  field_simp [hweight]

/-- Exact telescoping identity for the scaled raw sixth-moment error. -/
theorem resolventScaledLogSixthMomentError_eq
    (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogSixthMomentError z scale cutoff =
      resolventScaledLogSixthMoment z scale cutoff -
        ((scale : ℝ) *
          (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
            30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
              360 * Real.log scale ^ 2 - 720 * Real.log scale + 720)) *
          resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventScaledLogSixthMomentError,
        resolventScaledLogSixthMoment, resolventMass]
  | succ cutoff ih =>
      rw [resolventScaledLogSixthMomentError, Finset.sum_range_succ]
      change resolventScaledLogSixthMomentError z scale cutoff +
        resolventScaledLogSixthMomentIncrementError z scale cutoff = _
      rw [ih, resolventScaledLogSixthMomentIncrementError]
      have hmoment := resolventScaledLogSixthMoment_succ z scale cutoff
      simp only [resolventMass, Finset.sum_range_succ]
      simp only [resolventMass] at hmoment
      change resolventScaledLogSixthMoment z scale (cutoff + 1) -
          resolventScaledLogSixthMoment z scale cutoff = _ at hmoment
      linarith

/-- The raw scaled sixth logarithmic moment centered at `log M` converges to
`ℓ(log(ℓ)⁶ - 6log(ℓ)⁵ + 30log(ℓ)⁴ - 120log(ℓ)³ +
360log(ℓ)² - 720log(ℓ) + 720)`. -/
theorem tendsto_resolventScaledLogSixthMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSixthMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
          30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
            360 * Real.log scale ^ 2 - 720 * Real.log scale + 720))) := by
  have hincrementRatio :=
    tendsto_resolventScaledLogSixthMomentIncrementError_div_weight_zero
      hz hscale
  have hincrementSmall :
      (resolventScaledLogSixthMomentIncrementError z scale) =o[atTop]
        resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      (resolventScaledLogSixthMomentError z scale) =o[atTop]
        resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff,
        resolventScaledLogSixthMomentIncrementError z scale n) =o[atTop]
      (fun cutoff => ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSixthMomentError z scale cutoff /
        resolventMass z cutoff) atTop (nhds 0) :=
    herrorSmall.tendsto_div_nhds_zero
  have hshifted := herrorRatio.add_const
    ((scale : ℝ) * (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
      30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
        360 * Real.log scale ^ 2 - 720 * Real.log scale + 720))
  have hshifted' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSixthMomentError z scale cutoff /
          resolventMass z cutoff +
        (scale : ℝ) * (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
          30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
            360 * Real.log scale ^ 2 - 720 * Real.log scale + 720))
      atTop (nhds ((scale : ℝ) * (Real.log scale ^ 6 -
        6 * Real.log scale ^ 5 + 30 * Real.log scale ^ 4 -
          120 * Real.log scale ^ 3 + 360 * Real.log scale ^ 2 -
            720 * Real.log scale + 720))) := by
    convert hshifted using 1
    ring
  apply hshifted'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventScaledLogSixthMomentError_eq]
  field_simp [hmass]
  ring

/-- Sixth logarithmic moment below `ℓ M`, centered at the weighted
logarithmic mean `μ_M(z)`. -/
def resolventScaledCenteredLogSixthMoment (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 *
      resolventWeight z n

/-- The sixth centered scalar moment from the functional-limit recurrence:
its limit is `ℓ(log(ℓ)⁶ + 15log(ℓ)⁴ - 40log(ℓ)³ +
135log(ℓ)² - 264log(ℓ) + 265)`. -/
theorem tendsto_resolventScaledCenteredLogSixthMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledCenteredLogSixthMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 6 + 15 * Real.log scale ^ 4 -
          40 * Real.log scale ^ 3 + 135 * Real.log scale ^ 2 -
            264 * Real.log scale + 265))) := by
  have hraw := tendsto_resolventScaledLogSixthMoment_div_mass hz hscale
  have hfifth := tendsto_resolventScaledLogFifthMoment_div_mass hz hscale
  have hfourth := tendsto_resolventScaledLogFourthMoment_div_mass hz hscale
  have hthird := tendsto_resolventScaledLogCubeMoment_div_mass hz hscale
  have hsecond := tendsto_resolventScaledLogSqMoment_div_mass hz hscale
  have hfirst := tendsto_resolventScaledLogMoment_div_mass hz hscale
  have hmean : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff - resolventLogMean z cutoff) atTop (nhds 1) := by
    have h := (tendsto_resolventLogMean_sub_log hz).neg
    simpa only [neg_sub, neg_neg] using h
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hlimit :=
    ((((((hraw.add ((hmean.mul hfifth).const_mul 6)).add
      (((hmean.pow 2).mul hfourth).const_mul 15)).add
        (((hmean.pow 3).mul hthird).const_mul 20)).add
          (((hmean.pow 4).mul hsecond).const_mul 15)).add
            (((hmean.pow 5).mul hfirst).const_mul 6)).add
              ((hmean.pow 6).mul hmassRatio))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSixthMoment z scale cutoff /
          resolventMass z cutoff +
        6 * ((Real.log cutoff - resolventLogMean z cutoff) *
          (resolventScaledLogFifthMoment z scale cutoff /
            resolventMass z cutoff)) +
        15 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
          (resolventScaledLogFourthMoment z scale cutoff /
            resolventMass z cutoff)) +
        20 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
          (resolventScaledLogCubeMoment z scale cutoff /
            resolventMass z cutoff)) +
        15 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
          (resolventScaledLogSqMoment z scale cutoff /
            resolventMass z cutoff)) +
        6 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
          (resolventScaledLogMoment z scale cutoff /
            resolventMass z cutoff)) +
        (Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
          (resolventMass z (scale * cutoff) / resolventMass z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 6 + 15 * Real.log scale ^ 4 -
          40 * Real.log scale ^ 3 + 135 * Real.log scale ^ 2 -
            264 * Real.log scale + 265))) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  have hdecomp :
      resolventScaledCenteredLogSixthMoment z scale cutoff =
        resolventScaledLogSixthMoment z scale cutoff +
          6 * (Real.log cutoff - resolventLogMean z cutoff) *
            resolventScaledLogFifthMoment z scale cutoff +
          15 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
            resolventScaledLogFourthMoment z scale cutoff +
          20 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
            resolventScaledLogCubeMoment z scale cutoff +
          15 * (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
            resolventScaledLogSqMoment z scale cutoff +
          6 * (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
            resolventScaledLogMoment z scale cutoff +
          (Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
            resolventMass z (scale * cutoff) := by
    rw [resolventScaledCenteredLogSixthMoment,
      resolventScaledLogSixthMoment, resolventScaledLogFifthMoment,
      resolventScaledLogFourthMoment, resolventScaledLogCubeMoment,
      resolventScaledLogSqMoment, resolventScaledLogMoment, resolventMass]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - resolventLogMean z cutoff) ^ 6 *
              resolventWeight z n =
          (Real.log (n + 1) - Real.log cutoff) ^ 6 *
              resolventWeight z n +
            6 * (Real.log cutoff - resolventLogMean z cutoff) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 5 *
                resolventWeight z n) +
            15 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n) +
            20 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n) +
            15 * (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) +
            6 * (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hdecomp]
  field_simp [hmass]

end

end NativeCarrySpectralWeyl.Limits
