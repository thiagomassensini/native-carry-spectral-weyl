import NativeCarrySpectralWeyl.Limits.SeventhFunctionalCovariance
import Mathlib.Tactic

/-!
# Eighth scalar moment of the resolvent functional limit

For a fixed positive natural scale `ℓ`, this file proves

`A_M(z)⁻¹ ∑_{n < ℓ M} (log(n+1) - μ_M(z))⁸ w_z(n)
  → ℓ (log(ℓ)⁸ + 28 log(ℓ)⁶ - 112 log(ℓ)⁵ +
    630 log(ℓ)⁴ - 2464 log(ℓ)³ + 7420 log(ℓ)² -
    14832 log(ℓ) + 14833)`.

The proof continues the exact discrete recurrence used for moments one
through seven.  The eighth-power increment has a fixed-width boundary block and
the binomial change-of-center terms with coefficients
`-8, 28, -56, 70, -56, 28, -8, 1`.
Only the logarithmic step times the already proved seventh raw moment survives
at endpoint-weight scale.  Little-o summation gives the raw eighth moment,
and `log M - μ_M(z) → 1` converts it to the weighted-mean-centered form.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- The fixed-width eighth-power boundary block created when the cutoff changes
from `M` to `M+1`. -/
def resolventScaledLogEighthBoundary (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ r ∈ Finset.range scale,
    (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 8 *
      resolventWeight z (scale * cutoff + r)

/-- Eighth logarithmic moment below `ℓ M`, centered at `log M`. -/
def resolventScaledLogEighthMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - Real.log cutoff) ^ 8 * resolventWeight z n

/-- The normalized eighth-power boundary block converges to `ℓ log(ℓ)⁸`. -/
theorem tendsto_resolventScaledLogEighthBoundary_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogEighthBoundary z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 8)) := by
  have hterm : ∀ r ∈ Finset.range scale,
      Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 8 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
        atTop (nhds (Real.log scale ^ 8)) := by
    intro r _
    simpa only [mul_one] using
      (tendsto_log_nat_mul_add_sub_log hscale r).pow 8 |>.mul
        (tendsto_resolventWeight_nat_mul_add_div hz hscale r)
  have hsum := tendsto_finsetSum (Finset.range scale) hterm
  have hsum' : Tendsto (fun cutoff : ℕ =>
      ∑ r ∈ Finset.range scale,
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 8 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 8)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [resolventScaledLogEighthBoundary, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hweight]

/-- The logarithmic step times the seventh scaled moment, normalized by the
endpoint weight, converges to the raw seventh-moment coefficient. -/
theorem tendsto_logStep_mul_resolventScaledLogSeventhMoment_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogSeventhMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
          42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
            840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
              5040 * Real.log scale - 5040))) := by
  have hproduct :=
    (tendsto_nat_mul_log_succ_sub_log_one.mul
      (tendsto_resolventScaledLogSeventhMoment_div_mass hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) *
        (resolventScaledLogSeventhMoment z scale cutoff /
          resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 7 - 7 * Real.log scale ^ 6 +
          42 * Real.log scale ^ 5 - 210 * Real.log scale ^ 4 +
            840 * Real.log scale ^ 3 - 2520 * Real.log scale ^ 2 +
              5040 * Real.log scale - 5040))) := by
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

/-- The squared logarithmic step times the sixth scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_sq_mul_resolventScaledLogSixthMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogSixthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_mul_resolventScaledLogSixthMoment_div_weight hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogSixthMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The cubed logarithmic step times the fifth scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_cube_mul_resolventScaledLogFifthMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogFifthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_sq_mul_resolventScaledLogFifthMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogFifthMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fourth-power logarithmic step times the fourth scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_fourth_mul_resolventScaledLogFourthMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventScaledLogFourthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_cube_mul_resolventScaledLogFourthMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogFourthMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fifth-power logarithmic step times the third scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_fifth_mul_resolventScaledLogCubeMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          resolventScaledLogCubeMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_fourth_mul_resolventScaledLogCubeMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventScaledLogCubeMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The sixth-power logarithmic step times the second scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_sixth_mul_resolventScaledLogSqMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
          resolventScaledLogSqMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_fifth_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            resolventScaledLogSqMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The seventh-power logarithmic step times the first scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_seventh_mul_resolventScaledLogMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
          resolventScaledLogMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_sixth_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
            resolventScaledLogMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The eighth-power change-of-center correction is negligible relative to
the endpoint weight. -/
theorem tendsto_logStep_eighth_mul_resolventMass_nat_mul_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 8 *
          resolventMass z (scale * cutoff) /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_seventh_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
            resolventMass z (scale * cutoff) /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- Exact increment identity for the scaled eighth logarithmic moment. -/
theorem resolventScaledLogEighthMoment_succ (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogEighthMoment z scale (cutoff + 1) -
        resolventScaledLogEighthMoment z scale cutoff =
      resolventScaledLogEighthBoundary z scale cutoff -
        8 * (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogSeventhMoment z scale cutoff +
        28 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogSixthMoment z scale cutoff -
        56 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogFifthMoment z scale cutoff +
        70 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventScaledLogFourthMoment z scale cutoff -
        56 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          resolventScaledLogCubeMoment z scale cutoff +
        28 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
          resolventScaledLogSqMoment z scale cutoff -
        8 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
          resolventScaledLogMoment z scale cutoff +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 8 *
          resolventMass z (scale * cutoff) := by
  rw [resolventScaledLogEighthMoment, resolventScaledLogEighthMoment,
    resolventScaledLogEighthBoundary, resolventScaledLogSeventhMoment,
    resolventScaledLogSixthMoment,
    resolventScaledLogFifthMoment, resolventScaledLogFourthMoment,
    resolventScaledLogCubeMoment, resolventScaledLogSqMoment,
    resolventScaledLogMoment, resolventMass]
  rw [Nat.mul_add, Nat.mul_one, Finset.sum_range_add]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcenter :
      (∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 8 *
            resolventWeight z n) -
        ∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log cutoff) ^ 8 *
            resolventWeight z n =
        -8 * (Real.log (cutoff + 1) - Real.log cutoff) *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 7 *
                resolventWeight z n +
          28 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 6 *
                resolventWeight z n -
          56 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 5 *
                resolventWeight z n +
          70 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n -
          56 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n +
          28 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n -
          8 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n +
          (Real.log (cutoff + 1) - Real.log cutoff) ^ 8 *
            ∑ n ∈ Finset.range (scale * cutoff), resolventWeight z n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [show
      (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 8 *
            resolventWeight z x) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 8 *
              resolventWeight z (scale * cutoff + x)) -
        (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 8 *
            resolventWeight z x) =
        ((∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 8 *
              resolventWeight z x) -
          (∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 8 *
              resolventWeight z x)) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 8 *
              resolventWeight z (scale * cutoff + x)) by ring]
  rw [hcenter]
  ring

/-- Increment after subtracting the predicted raw eighth-moment main term. -/
def resolventScaledLogEighthMomentIncrementError
    (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  resolventScaledLogEighthBoundary z scale cutoff -
    8 * (Real.log (cutoff + 1) - Real.log cutoff) *
      resolventScaledLogSeventhMoment z scale cutoff +
    28 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
      resolventScaledLogSixthMoment z scale cutoff -
    56 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
      resolventScaledLogFifthMoment z scale cutoff +
    70 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
      resolventScaledLogFourthMoment z scale cutoff -
    56 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
      resolventScaledLogCubeMoment z scale cutoff +
    28 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
      resolventScaledLogSqMoment z scale cutoff -
    8 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
      resolventScaledLogMoment z scale cutoff +
    (Real.log (cutoff + 1) - Real.log cutoff) ^ 8 *
      resolventMass z (scale * cutoff) -
    ((scale : ℝ) *
      (Real.log scale ^ 8 - 8 * Real.log scale ^ 7 +
        56 * Real.log scale ^ 6 - 336 * Real.log scale ^ 5 +
          1680 * Real.log scale ^ 4 - 6720 * Real.log scale ^ 3 +
            20160 * Real.log scale ^ 2 - 40320 * Real.log scale + 40320)) *
      resolventWeight z cutoff

/-- Sum of the scaled raw eighth-moment increment errors. -/
def resolventScaledLogEighthMomentError (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    resolventScaledLogEighthMomentIncrementError z scale n

/-- The raw eighth-moment increment error is little-o of the endpoint
resolvent weight. -/
theorem tendsto_resolventScaledLogEighthMomentIncrementError_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogEighthMomentIncrementError z scale cutoff /
        resolventWeight z cutoff) atTop (nhds 0) := by
  have hboundary :=
    tendsto_resolventScaledLogEighthBoundary_div_weight hz hscale
  have hseventh :=
    tendsto_logStep_mul_resolventScaledLogSeventhMoment_div_weight hz hscale
  have hsixth :=
    tendsto_logStep_sq_mul_resolventScaledLogSixthMoment_div_weight_zero
      hz hscale
  have hfifth :=
    tendsto_logStep_cube_mul_resolventScaledLogFifthMoment_div_weight_zero
      hz hscale
  have hfourth :=
    tendsto_logStep_fourth_mul_resolventScaledLogFourthMoment_div_weight_zero
      hz hscale
  have hthird :=
    tendsto_logStep_fifth_mul_resolventScaledLogCubeMoment_div_weight_zero
      hz hscale
  have hsecond :=
    tendsto_logStep_sixth_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale
  have hfirst :=
    tendsto_logStep_seventh_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale
  have heighth :=
    tendsto_logStep_eighth_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale
  have hconstant : Tendsto (fun _ : ℕ =>
      (scale : ℝ) * (Real.log scale ^ 8 - 8 * Real.log scale ^ 7 +
        56 * Real.log scale ^ 6 - 336 * Real.log scale ^ 5 +
          1680 * Real.log scale ^ 4 - 6720 * Real.log scale ^ 3 +
            20160 * Real.log scale ^ 2 - 40320 * Real.log scale + 40320))
      atTop
      (nhds ((scale : ℝ) * (Real.log scale ^ 8 -
        8 * Real.log scale ^ 7 + 56 * Real.log scale ^ 6 -
          336 * Real.log scale ^ 5 + 1680 * Real.log scale ^ 4 -
            6720 * Real.log scale ^ 3 + 20160 * Real.log scale ^ 2 -
              40320 * Real.log scale + 40320))) :=
    tendsto_const_nhds
  have h1 := hboundary.sub (hseventh.const_mul 8)
  have h2 := h1.add (hsixth.const_mul 28)
  have h3 := h2.sub (hfifth.const_mul 56)
  have h4 := h3.add (hfourth.const_mul 70)
  have h5 := h4.sub (hthird.const_mul 56)
  have h6 := h5.add (hsecond.const_mul 28)
  have h7 := h6.sub (hfirst.const_mul 8)
  have h8 := h7.add heighth
  have hlimit := h8.sub hconstant
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogEighthBoundary z scale cutoff /
          resolventWeight z cutoff -
        8 * ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogSeventhMoment z scale cutoff /
              resolventWeight z cutoff) +
        28 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogSixthMoment z scale cutoff /
              resolventWeight z cutoff) -
        56 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogFifthMoment z scale cutoff /
              resolventWeight z cutoff) +
        70 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventScaledLogFourthMoment z scale cutoff /
              resolventWeight z cutoff) -
        56 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            resolventScaledLogCubeMoment z scale cutoff /
              resolventWeight z cutoff) +
        28 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 6 *
            resolventScaledLogSqMoment z scale cutoff /
              resolventWeight z cutoff) -
        8 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 7 *
            resolventScaledLogMoment z scale cutoff /
              resolventWeight z cutoff) +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 8 *
            resolventMass z (scale * cutoff) /
              resolventWeight z cutoff -
        (scale : ℝ) * (Real.log scale ^ 8 - 8 * Real.log scale ^ 7 +
          56 * Real.log scale ^ 6 - 336 * Real.log scale ^ 5 +
            1680 * Real.log scale ^ 4 - 6720 * Real.log scale ^ 3 +
              20160 * Real.log scale ^ 2 - 40320 * Real.log scale + 40320))
      atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  rw [resolventScaledLogEighthMomentIncrementError]
  field_simp [hweight]

/-- Exact telescoping identity for the scaled raw eighth-moment error. -/
theorem resolventScaledLogEighthMomentError_eq
    (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogEighthMomentError z scale cutoff =
      resolventScaledLogEighthMoment z scale cutoff -
        ((scale : ℝ) *
          (Real.log scale ^ 8 - 8 * Real.log scale ^ 7 +
            56 * Real.log scale ^ 6 - 336 * Real.log scale ^ 5 +
              1680 * Real.log scale ^ 4 - 6720 * Real.log scale ^ 3 +
                20160 * Real.log scale ^ 2 - 40320 * Real.log scale +
                  40320)) *
          resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventScaledLogEighthMomentError,
        resolventScaledLogEighthMoment, resolventMass]
  | succ cutoff ih =>
      rw [resolventScaledLogEighthMomentError, Finset.sum_range_succ]
      change resolventScaledLogEighthMomentError z scale cutoff +
        resolventScaledLogEighthMomentIncrementError z scale cutoff = _
      rw [ih, resolventScaledLogEighthMomentIncrementError]
      have hmoment := resolventScaledLogEighthMoment_succ z scale cutoff
      simp only [resolventMass, Finset.sum_range_succ]
      simp only [resolventMass] at hmoment
      change resolventScaledLogEighthMoment z scale (cutoff + 1) -
          resolventScaledLogEighthMoment z scale cutoff = _ at hmoment
      linarith

/-- The raw scaled eighth logarithmic moment centered at `log M` converges to
`ℓ(log(ℓ)⁸ - 8log(ℓ)⁷ + 56log(ℓ)⁶ - 336log(ℓ)⁵ +
1680log(ℓ)⁴ - 6720log(ℓ)³ + 20160log(ℓ)² - 40320log(ℓ) + 40320)`. -/
theorem tendsto_resolventScaledLogEighthMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogEighthMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 8 - 8 * Real.log scale ^ 7 +
          56 * Real.log scale ^ 6 - 336 * Real.log scale ^ 5 +
            1680 * Real.log scale ^ 4 - 6720 * Real.log scale ^ 3 +
              20160 * Real.log scale ^ 2 - 40320 * Real.log scale +
                40320))) := by
  have hincrementRatio :=
    tendsto_resolventScaledLogEighthMomentIncrementError_div_weight_zero
      hz hscale
  have hincrementSmall :
      (resolventScaledLogEighthMomentIncrementError z scale) =o[atTop]
        resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      (resolventScaledLogEighthMomentError z scale) =o[atTop]
        resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff,
        resolventScaledLogEighthMomentIncrementError z scale n) =o[atTop]
      (fun cutoff => ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogEighthMomentError z scale cutoff /
        resolventMass z cutoff) atTop (nhds 0) :=
    herrorSmall.tendsto_div_nhds_zero
  have hshifted := herrorRatio.add_const
    ((scale : ℝ) * (Real.log scale ^ 8 - 8 * Real.log scale ^ 7 +
      56 * Real.log scale ^ 6 - 336 * Real.log scale ^ 5 +
        1680 * Real.log scale ^ 4 - 6720 * Real.log scale ^ 3 +
          20160 * Real.log scale ^ 2 - 40320 * Real.log scale + 40320))
  have hshifted' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogEighthMomentError z scale cutoff /
          resolventMass z cutoff +
        (scale : ℝ) * (Real.log scale ^ 8 - 8 * Real.log scale ^ 7 +
          56 * Real.log scale ^ 6 - 336 * Real.log scale ^ 5 +
            1680 * Real.log scale ^ 4 - 6720 * Real.log scale ^ 3 +
              20160 * Real.log scale ^ 2 - 40320 * Real.log scale + 40320))
      atTop (nhds ((scale : ℝ) * (Real.log scale ^ 8 -
        8 * Real.log scale ^ 7 + 56 * Real.log scale ^ 6 -
          336 * Real.log scale ^ 5 + 1680 * Real.log scale ^ 4 -
            6720 * Real.log scale ^ 3 + 20160 * Real.log scale ^ 2 -
              40320 * Real.log scale + 40320))) := by
    convert hshifted using 1
    ring
  apply hshifted'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventScaledLogEighthMomentError_eq]
  field_simp [hmass]
  ring

/-- Eighth logarithmic moment below `ℓ M`, centered at the weighted
logarithmic mean `μ_M(z)`. -/
def resolventScaledCenteredLogEighthMoment (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - resolventLogMean z cutoff) ^ 8 *
      resolventWeight z n

/-- The eighth centered scalar moment from the functional-limit recurrence:
its limit is `ℓ(log(ℓ)⁸ + 28log(ℓ)⁶ - 112log(ℓ)⁵ + 630log(ℓ)⁴ -
2464log(ℓ)³ + 7420log(ℓ)² - 14832log(ℓ) + 14833)`. -/
theorem tendsto_resolventScaledCenteredLogEighthMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledCenteredLogEighthMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 8 + 28 * Real.log scale ^ 6 -
          112 * Real.log scale ^ 5 + 630 * Real.log scale ^ 4 -
            2464 * Real.log scale ^ 3 + 7420 * Real.log scale ^ 2 -
              14832 * Real.log scale + 14833))) := by
  have hraw := tendsto_resolventScaledLogEighthMoment_div_mass hz hscale
  have hseventh := tendsto_resolventScaledLogSeventhMoment_div_mass hz hscale
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
  have h1 := hraw.add ((hmean.mul hseventh).const_mul 8)
  have h2 := h1.add (((hmean.pow 2).mul hsixth).const_mul 28)
  have h3 := h2.add (((hmean.pow 3).mul hfifth).const_mul 56)
  have h4 := h3.add (((hmean.pow 4).mul hfourth).const_mul 70)
  have h5 := h4.add (((hmean.pow 5).mul hthird).const_mul 56)
  have h6 := h5.add (((hmean.pow 6).mul hsecond).const_mul 28)
  have h7 := h6.add (((hmean.pow 7).mul hfirst).const_mul 8)
  have hlimit := h7.add ((hmean.pow 8).mul hmassRatio)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogEighthMoment z scale cutoff /
          resolventMass z cutoff +
        8 * ((Real.log cutoff - resolventLogMean z cutoff) *
          (resolventScaledLogSeventhMoment z scale cutoff /
            resolventMass z cutoff)) +
        28 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
          (resolventScaledLogSixthMoment z scale cutoff /
            resolventMass z cutoff)) +
        56 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
          (resolventScaledLogFifthMoment z scale cutoff /
            resolventMass z cutoff)) +
        70 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
          (resolventScaledLogFourthMoment z scale cutoff /
            resolventMass z cutoff)) +
        56 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
          (resolventScaledLogCubeMoment z scale cutoff /
            resolventMass z cutoff)) +
        28 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
          (resolventScaledLogSqMoment z scale cutoff /
            resolventMass z cutoff)) +
        8 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 7 *
          (resolventScaledLogMoment z scale cutoff /
            resolventMass z cutoff)) +
        (Real.log cutoff - resolventLogMean z cutoff) ^ 8 *
          (resolventMass z (scale * cutoff) / resolventMass z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 8 + 28 * Real.log scale ^ 6 -
          112 * Real.log scale ^ 5 + 630 * Real.log scale ^ 4 -
            2464 * Real.log scale ^ 3 + 7420 * Real.log scale ^ 2 -
              14832 * Real.log scale + 14833))) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  have hdecomp :
      resolventScaledCenteredLogEighthMoment z scale cutoff =
        resolventScaledLogEighthMoment z scale cutoff +
          8 * (Real.log cutoff - resolventLogMean z cutoff) *
            resolventScaledLogSeventhMoment z scale cutoff +
          28 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
            resolventScaledLogSixthMoment z scale cutoff +
          56 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
            resolventScaledLogFifthMoment z scale cutoff +
          70 * (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
            resolventScaledLogFourthMoment z scale cutoff +
          56 * (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
            resolventScaledLogCubeMoment z scale cutoff +
          28 * (Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
            resolventScaledLogSqMoment z scale cutoff +
          8 * (Real.log cutoff - resolventLogMean z cutoff) ^ 7 *
            resolventScaledLogMoment z scale cutoff +
          (Real.log cutoff - resolventLogMean z cutoff) ^ 8 *
            resolventMass z (scale * cutoff) := by
    rw [resolventScaledCenteredLogEighthMoment,
      resolventScaledLogEighthMoment, resolventScaledLogSeventhMoment,
      resolventScaledLogSixthMoment, resolventScaledLogFifthMoment,
      resolventScaledLogFourthMoment, resolventScaledLogCubeMoment,
      resolventScaledLogSqMoment, resolventScaledLogMoment, resolventMass]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - resolventLogMean z cutoff) ^ 8 *
              resolventWeight z n =
          (Real.log (n + 1) - Real.log cutoff) ^ 8 *
              resolventWeight z n +
            8 * (Real.log cutoff - resolventLogMean z cutoff) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 7 *
                resolventWeight z n) +
            28 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 6 *
                resolventWeight z n) +
            56 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 5 *
                resolventWeight z n) +
            70 * (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n) +
            56 * (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n) +
            28 * (Real.log cutoff - resolventLogMean z cutoff) ^ 6 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) +
            8 * (Real.log cutoff - resolventLogMean z cutoff) ^ 7 *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log cutoff - resolventLogMean z cutoff) ^ 8 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hdecomp]
  field_simp [hmass]

end

end NativeCarrySpectralWeyl.Limits
