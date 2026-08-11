import NativeCarrySpectralWeyl.Limits.SexticFunctionalCovariance
import Mathlib.Tactic

/-!
# Seventh scalar moment of the resolvent functional limit

For a fixed positive natural scale `ℓ`, this file proves

`A_M(z)⁻¹ ∑_{n < ℓ M} (log(n+1) - μ_M(z))⁷ w_z(n)
  → ℓ (log(ℓ)⁷ + 21 log(ℓ)⁵ - 70 log(ℓ)⁴ +
    315 log(ℓ)³ - 924 log(ℓ)² + 1855 log(ℓ) - 1854)`.

The proof continues the exact discrete recurrence used for moments one
through six.  The seventh-power increment has a fixed-width boundary block and
the binomial change-of-center terms with coefficients
`-7, 21, -35, 35, -21, 7, -1`.
Only the logarithmic step times the already proved sixth raw moment survives
at endpoint-weight scale.  Little-o summation gives the raw seventh moment,
and `log M - μ_M(z) → 1` converts it to the weighted-mean-centered form.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- The fixed-width seventh-power boundary block created when the cutoff changes
from `M` to `M+1`. -/
def resolventScaledLogSeventhBoundary (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ r ∈ Finset.range scale,
    (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 7 *
      resolventWeight z (scale * cutoff + r)

/-- Seventh logarithmic moment below `ℓ M`, centered at `log M`. -/
def resolventScaledLogSeventhMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - Real.log cutoff) ^ 7 * resolventWeight z n

/-- The normalized seventh-power boundary block converges to `ℓ log(ℓ)⁷`. -/
theorem tendsto_resolventScaledLogSeventhBoundary_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSeventhBoundary z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 7)) := by
  have hterm : ∀ r ∈ Finset.range scale,
      Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 7 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
        atTop (nhds (Real.log scale ^ 7)) := by
    intro r _
    simpa only [mul_one] using
      (tendsto_log_nat_mul_add_sub_log hscale r).pow 7 |>.mul
        (tendsto_resolventWeight_nat_mul_add_div hz hscale r)
  have hsum := tendsto_finsetSum (Finset.range scale) hterm
  have hsum' : Tendsto (fun cutoff : ℕ =>
      ∑ r ∈ Finset.range scale,
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 7 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 7)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [resolventScaledLogSeventhBoundary, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hweight]

/-- The logarithmic step times the sixth scaled moment, normalized by the
endpoint weight, converges to the raw sixth-moment coefficient. -/
theorem tendsto_logStep_mul_resolventScaledLogSixthMoment_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogSixthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
          30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
            360 * Real.log scale ^ 2 - 720 * Real.log scale + 720))) := by
  have hproduct :=
    (tendsto_nat_mul_log_succ_sub_log_one.mul
      (tendsto_resolventScaledLogSixthMoment_div_mass hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) *
        (resolventScaledLogSixthMoment z scale cutoff /
          resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 6 - 6 * Real.log scale ^ 5 +
          30 * Real.log scale ^ 4 - 120 * Real.log scale ^ 3 +
            360 * Real.log scale ^ 2 - 720 * Real.log scale + 720))) := by
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

/-- The squared logarithmic step times the fifth scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_sq_mul_resolventScaledLogFifthMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogFifthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_mul_resolventScaledLogFifthMoment_div_weight hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogFifthMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The cubed logarithmic step times the fourth scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_cube_mul_resolventScaledLogFourthMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogFourthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_sq_mul_resolventScaledLogFourthMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogFourthMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fourth-power logarithmic step times the third scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_fourth_mul_resolventScaledLogCubeMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventScaledLogCubeMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_cube_mul_resolventScaledLogCubeMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogCubeMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fifth-power logarithmic step times the second scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_fifth_mul_resolventScaledLogSqMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          resolventScaledLogSqMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_fourth_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventScaledLogSqMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The sixth-power logarithmic step times the first scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_sixth_mul_resolventScaledLogMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
          resolventScaledLogMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_fifth_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            resolventScaledLogMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The seventh-power change-of-center correction is negligible relative to
the endpoint weight. -/
theorem tendsto_logStep_seventh_mul_resolventMass_nat_mul_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
          resolventMass z (scale * cutoff) /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_sixth_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
            resolventMass z (scale * cutoff) /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- Exact increment identity for the scaled seventh logarithmic moment. -/
theorem resolventScaledLogSeventhMoment_succ (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogSeventhMoment z scale (cutoff + 1) -
        resolventScaledLogSeventhMoment z scale cutoff =
      resolventScaledLogSeventhBoundary z scale cutoff -
        7 * (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogSixthMoment z scale cutoff +
        21 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogFifthMoment z scale cutoff -
        35 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogFourthMoment z scale cutoff +
        35 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventScaledLogCubeMoment z scale cutoff -
        21 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          resolventScaledLogSqMoment z scale cutoff +
        7 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
          resolventScaledLogMoment z scale cutoff -
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
          resolventMass z (scale * cutoff) := by
  rw [resolventScaledLogSeventhMoment, resolventScaledLogSeventhMoment,
    resolventScaledLogSeventhBoundary, resolventScaledLogSixthMoment,
    resolventScaledLogFifthMoment,
    resolventScaledLogFourthMoment, resolventScaledLogCubeMoment,
    resolventScaledLogSqMoment, resolventScaledLogMoment, resolventMass]
  rw [Nat.mul_add, Nat.mul_one, Finset.sum_range_add]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcenter :
      (∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 7 *
            resolventWeight z n) -
        ∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log cutoff) ^ 7 *
            resolventWeight z n =
        -7 * (Real.log (cutoff + 1) - Real.log cutoff) *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 6 *
                resolventWeight z n +
          21 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 5 *
                resolventWeight z n -
          35 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n +
          35 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n -
          21 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n +
          7 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n -
          (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
            ∑ n ∈ Finset.range (scale * cutoff), resolventWeight z n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [show
      (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 7 *
            resolventWeight z x) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 7 *
              resolventWeight z (scale * cutoff + x)) -
        (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 7 *
            resolventWeight z x) =
        ((∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 7 *
              resolventWeight z x) -
          (∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 7 *
              resolventWeight z x)) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 7 *
              resolventWeight z (scale * cutoff + x)) by ring]
  rw [hcenter]
  ring

/-- Increment after subtracting the predicted raw seventh-moment main term. -/
def resolventScaledLogSeventhMomentIncrementError
    (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  resolventScaledLogSeventhBoundary z scale cutoff -
    7 * (Real.log (cutoff + 1) - Real.log cutoff) *
      resolventScaledLogSixthMoment z scale cutoff +
    21 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
      resolventScaledLogFifthMoment z scale cutoff -
    35 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
      resolventScaledLogFourthMoment z scale cutoff +
    35 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
      resolventScaledLogCubeMoment z scale cutoff -
    21 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
      resolventScaledLogSqMoment z scale cutoff +
    7 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
      resolventScaledLogMoment z scale cutoff -
    (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
      resolventMass z (scale * cutoff) -
    ((scale : ℝ) *
      (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
        42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
          840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
            5040 * Real.log scale - 5040)) *
      resolventWeight z cutoff

/-- Sum of the scaled raw seventh-moment increment errors. -/
def resolventScaledLogSeventhMomentError (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    resolventScaledLogSeventhMomentIncrementError z scale n

/-- The raw seventh-moment increment error is little-o of the endpoint
resolvent weight. -/
theorem tendsto_resolventScaledLogSeventhMomentIncrementError_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSeventhMomentIncrementError z scale cutoff /
        resolventWeight z cutoff) atTop (nhds 0) := by
  have hboundary :=
    tendsto_resolventScaledLogSeventhBoundary_div_weight hz hscale
  have hsixth :=
    tendsto_logStep_mul_resolventScaledLogSixthMoment_div_weight hz hscale
  have hfifth :=
    tendsto_logStep_sq_mul_resolventScaledLogFifthMoment_div_weight_zero
      hz hscale
  have hfourth :=
    tendsto_logStep_cube_mul_resolventScaledLogFourthMoment_div_weight_zero
      hz hscale
  have hcubic :=
    tendsto_logStep_fourth_mul_resolventScaledLogCubeMoment_div_weight_zero
      hz hscale
  have hquadratic :=
    tendsto_logStep_fifth_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale
  have hlinear :=
    tendsto_logStep_sixth_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale
  have hseventh :=
    tendsto_logStep_seventh_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale
  have hconstant : Tendsto (fun _ : ℕ =>
      (scale : ℝ) * (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
        42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
          840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
            5040 * Real.log scale - 5040)) atTop
      (nhds ((scale : ℝ) * (Real.log scale ^ 7 -
        7 * Real.log scale ^ 6 + 42 * Real.log scale ^ 5 -
          210 * Real.log scale ^ 4 + 840 * Real.log scale ^ 3 -
            2520 * Real.log scale ^ 2 + 5040 * Real.log scale - 5040))) :=
    tendsto_const_nhds
  have hlimit :=
    ((((((((hboundary.sub (hsixth.const_mul 7)).add
      (hfifth.const_mul 21)).sub (hfourth.const_mul 35)).add
        (hcubic.const_mul 35)).sub (hquadratic.const_mul 21)).add
          (hlinear.const_mul 7)).sub hseventh).sub hconstant)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSeventhBoundary z scale cutoff /
          resolventWeight z cutoff -
        7 * ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogSixthMoment z scale cutoff /
              resolventWeight z cutoff) +
        21 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogFifthMoment z scale cutoff /
              resolventWeight z cutoff) -
        35 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogFourthMoment z scale cutoff /
              resolventWeight z cutoff) +
        35 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventScaledLogCubeMoment z scale cutoff /
              resolventWeight z cutoff) -
        21 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            resolventScaledLogSqMoment z scale cutoff /
              resolventWeight z cutoff) +
        7 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
            resolventScaledLogMoment z scale cutoff /
              resolventWeight z cutoff) -
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
            resolventMass z (scale * cutoff) /
              resolventWeight z cutoff -
        (scale : ℝ) * (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
          42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
            840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
              5040 * Real.log scale - 5040))
      atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  rw [resolventScaledLogSeventhMomentIncrementError]
  field_simp [hweight]

/-- Exact telescoping identity for the scaled raw seventh-moment error. -/
theorem resolventScaledLogSeventhMomentError_eq
    (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogSeventhMomentError z scale cutoff =
      resolventScaledLogSeventhMoment z scale cutoff -
        ((scale : ℝ) *
          (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
            42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
              840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
                5040 * Real.log scale - 5040)) *
          resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventScaledLogSeventhMomentError,
        resolventScaledLogSeventhMoment, resolventMass]
  | succ cutoff ih =>
      rw [resolventScaledLogSeventhMomentError, Finset.sum_range_succ]
      change resolventScaledLogSeventhMomentError z scale cutoff +
        resolventScaledLogSeventhMomentIncrementError z scale cutoff = _
      rw [ih, resolventScaledLogSeventhMomentIncrementError]
      have hmoment := resolventScaledLogSeventhMoment_succ z scale cutoff
      simp only [resolventMass, Finset.sum_range_succ]
      simp only [resolventMass] at hmoment
      change resolventScaledLogSeventhMoment z scale (cutoff + 1) -
          resolventScaledLogSeventhMoment z scale cutoff = _ at hmoment
      linarith

/-- The raw scaled seventh logarithmic moment centered at `log M` converges to
`ℓ(log(ℓ)⁷ - 7log(ℓ)⁶ + 42log(ℓ)⁵ - 210log(ℓ)⁴ +
840log(ℓ)³ - 2520log(ℓ)² + 5040log(ℓ) - 5040)`. -/
theorem tendsto_resolventScaledLogSeventhMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSeventhMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
          42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
            840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
              5040 * Real.log scale - 5040))) := by
  have hincrementRatio :=
    tendsto_resolventScaledLogSeventhMomentIncrementError_div_weight_zero
      hz hscale
  have hincrementSmall :
      (resolventScaledLogSeventhMomentIncrementError z scale) =o[atTop]
        resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      (resolventScaledLogSeventhMomentError z scale) =o[atTop]
        resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff,
        resolventScaledLogSeventhMomentIncrementError z scale n) =o[atTop]
      (fun cutoff => ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSeventhMomentError z scale cutoff /
        resolventMass z cutoff) atTop (nhds 0) :=
    herrorSmall.tendsto_div_nhds_zero
  have hshifted := herrorRatio.add_const
    ((scale : ℝ) * (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
      42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
        840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
          5040 * Real.log scale - 5040))
  have hshifted' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSeventhMomentError z scale cutoff /
          resolventMass z cutoff +
        (scale : ℝ) * (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
          42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
            840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
              5040 * Real.log scale - 5040))
      atTop (nhds ((scale : ℝ) * (Real.log scale ^ 7 -
        7 * Real.log scale ^ 6 + 42 * Real.log scale ^ 5 -
          210 * Real.log scale ^ 4 + 840 * Real.log scale ^ 3 -
            2520 * Real.log scale ^ 2 + 5040 * Real.log scale - 5040))) := by
    convert hshifted using 1
    ring
  apply hshifted'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventScaledLogSeventhMomentError_eq]
  field_simp [hmass]
  ring

/-- Seventh logarithmic moment below `ℓ M`, centered at the weighted
logarithmic mean `μ_M(z)`. -/
def resolventScaledCenteredLogSeventhMoment (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 *
      resolventWeight z n

/-- The seventh centered scalar moment from the functional-limit recurrence:
its limit is `ℓ(log(ℓ)⁷ + 21log(ℓ)⁵ - 70log(ℓ)⁴ +
315log(ℓ)³ - 924log(ℓ)² + 1855log(ℓ) - 1854)`. -/
theorem tendsto_resolventScaledCenteredLogSeventhMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledCenteredLogSeventhMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 7 + 21 * Real.log scale ^ 5 -
          70 * Real.log scale ^ 4 + 315 * Real.log scale ^ 3 -
            924 * Real.log scale ^ 2 + 1855 * Real.log scale - 1854))) := by
  have hraw := tendsto_resolventScaledLogSeventhMoment_div_mass hz hscale
  have hsixth := tendsto_resolventScaledLogSixthMoment_div_mass hz hscale
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
    (((((((hraw.add ((hmean.mul hsixth).const_mul 7)).add
      (((hmean.pow 2).mul hfifth).const_mul 21)).add
        (((hmean.pow 3).mul hfourth).const_mul 35)).add
          (((hmean.pow 4).mul hthird).const_mul 35)).add
            (((hmean.pow 5).mul hsecond).const_mul 21)).add
              (((hmean.pow 6).mul hfirst).const_mul 7)).add
                ((hmean.pow 7).mul hmassRatio))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSeventhMoment z scale cutoff /
          resolventMass z cutoff +
        7 * ((Real.log cutoff - resolventLogMean z cutoff) *
          (resolventScaledLogSixthMoment z scale cutoff /
            resolventMass z cutoff)) +
        21 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
          (resolventScaledLogFifthMoment z scale cutoff /
            resolventMass z cutoff)) +
        35 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
          (resolventScaledLogFourthMoment z scale cutoff /
            resolventMass z cutoff)) +
        35 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
          (resolventScaledLogCubeMoment z scale cutoff /
            resolventMass z cutoff)) +
        21 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
          (resolventScaledLogSqMoment z scale cutoff /
            resolventMass z cutoff)) +
        7 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
          (resolventScaledLogMoment z scale cutoff /
            resolventMass z cutoff)) +
        (Real.log cutoff - resolventLogMean z cutoff) ^ 7 *
          (resolventMass z (scale * cutoff) / resolventMass z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 7 + 21 * Real.log scale ^ 5 -
          70 * Real.log scale ^ 4 + 315 * Real.log scale ^ 3 -
            924 * Real.log scale ^ 2 + 1855 * Real.log scale - 1854))) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  have hdecomp :
      resolventScaledCenteredLogSeventhMoment z scale cutoff =
        resolventScaledLogSeventhMoment z scale cutoff +
          7 * (Real.log cutoff - resolventLogMean z cutoff) *
            resolventScaledLogSixthMoment z scale cutoff +
          21 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
            resolventScaledLogFifthMoment z scale cutoff +
          35 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
            resolventScaledLogFourthMoment z scale cutoff +
          35 * (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
            resolventScaledLogCubeMoment z scale cutoff +
          21 * (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
            resolventScaledLogSqMoment z scale cutoff +
          7 * (Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
            resolventScaledLogMoment z scale cutoff +
          (Real.log cutoff - resolventLogMean z cutoff) ^ 7 *
            resolventMass z (scale * cutoff) := by
    rw [resolventScaledCenteredLogSeventhMoment,
      resolventScaledLogSeventhMoment, resolventScaledLogSixthMoment,
      resolventScaledLogFifthMoment,
      resolventScaledLogFourthMoment, resolventScaledLogCubeMoment,
      resolventScaledLogSqMoment, resolventScaledLogMoment, resolventMass]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - resolventLogMean z cutoff) ^ 7 *
              resolventWeight z n =
          (Real.log (n + 1) - Real.log cutoff) ^ 7 *
              resolventWeight z n +
            7 * (Real.log cutoff - resolventLogMean z cutoff) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 6 *
                resolventWeight z n) +
            21 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 5 *
                resolventWeight z n) +
            35 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n) +
            35 * (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n) +
            21 * (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) +
            7 * (Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log cutoff - resolventLogMean z cutoff) ^ 7 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [hdecomp]
  field_simp [hmass]

end

end NativeCarrySpectralWeyl.Limits
