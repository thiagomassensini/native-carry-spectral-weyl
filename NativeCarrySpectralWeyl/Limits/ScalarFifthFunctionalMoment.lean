import NativeCarrySpectralWeyl.Limits.QuarticFunctionalCovariance
import Mathlib.Tactic

/-!
# Fifth scalar moment of the resolvent functional limit

For a fixed positive natural scale `ℓ`, this file proves

`A_M(z)⁻¹ ∑_{n < ℓ M} (log(n+1) - μ_M(z))⁵ w_z(n)
  → ℓ (log(ℓ)⁵ + 10 log(ℓ)³ - 20 log(ℓ)² +
    45 log(ℓ) - 44)`.

The proof continues the exact discrete recurrence used for moments one
through four.  The quintic increment has a fixed-width boundary block and
the binomial change-of-center terms with coefficients `-5, 10, -10, 5, -1`.
Only the logarithmic step times the already proved quartic raw moment survives
at endpoint-weight scale.  Little-o summation gives the raw fifth moment,
and `log M - μ_M(z) → 1` converts it to the weighted-mean-centered form.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- The fixed-width quintic boundary block created when the cutoff changes
from `M` to `M+1`. -/
def resolventScaledLogFifthBoundary (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ r ∈ Finset.range scale,
    (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 5 *
      resolventWeight z (scale * cutoff + r)

/-- Fifth logarithmic moment below `ℓ M`, centered at `log M`. -/
def resolventScaledLogFifthMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - Real.log cutoff) ^ 5 * resolventWeight z n

/-- The normalized quintic boundary block converges to `ℓ log(ℓ)⁵`. -/
theorem tendsto_resolventScaledLogFifthBoundary_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFifthBoundary z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 5)) := by
  have hterm : ∀ r ∈ Finset.range scale,
      Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 5 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
        atTop (nhds (Real.log scale ^ 5)) := by
    intro r _
    simpa only [mul_one] using
      (tendsto_log_nat_mul_add_sub_log hscale r).pow 5 |>.mul
        (tendsto_resolventWeight_nat_mul_add_div hz hscale r)
  have hsum := tendsto_finsetSum (Finset.range scale) hterm
  have hsum' : Tendsto (fun cutoff : ℕ =>
      ∑ r ∈ Finset.range scale,
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 5 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 5)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [resolventScaledLogFifthBoundary, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hweight]

/-- The logarithmic step times the fourth scaled moment, normalized by the
endpoint weight, converges to the raw fourth-moment coefficient. -/
theorem tendsto_logStep_mul_resolventScaledLogFourthMoment_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogFourthMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 4 - 4 * Real.log scale ^ 3 +
          12 * Real.log scale ^ 2 - 24 * Real.log scale + 24))) := by
  have hproduct :=
    (tendsto_nat_mul_log_succ_sub_log_one.mul
      (tendsto_resolventScaledLogFourthMoment_div_mass hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) *
        (resolventScaledLogFourthMoment z scale cutoff /
          resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 4 - 4 * Real.log scale ^ 3 +
          12 * Real.log scale ^ 2 - 24 * Real.log scale + 24))) := by
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

/-- The squared logarithmic step times the third scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_sq_mul_resolventScaledLogCubeMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogCubeMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_mul_resolventScaledLogCubeMoment_div_weight hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogCubeMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The cubed logarithmic step times the second scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_cube_mul_resolventScaledLogSqMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogSqMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_sq_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogSqMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fourth-power logarithmic step times the first scaled moment is
negligible relative to the endpoint weight. -/
theorem tendsto_logStep_fourth_mul_resolventScaledLogMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventScaledLogMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_cube_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogMoment z scale cutoff /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- The fifth-power change-of-center correction is negligible relative to
the endpoint weight. -/
theorem tendsto_logStep_fifth_mul_resolventMass_nat_mul_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          resolventMass z (scale * cutoff) /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hproduct := Real.tendsto_log_nat_add_one_sub_log.mul
    (tendsto_logStep_fourth_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
        ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventMass z (scale * cutoff) /
          resolventWeight z cutoff)) atTop (nhds 0) := by
    simpa using hproduct
  convert hlimit using 1
  ring

/-- Exact increment identity for the scaled fifth logarithmic moment. -/
theorem resolventScaledLogFifthMoment_succ (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogFifthMoment z scale (cutoff + 1) -
        resolventScaledLogFifthMoment z scale cutoff =
      resolventScaledLogFifthBoundary z scale cutoff -
        5 * (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogFourthMoment z scale cutoff +
        10 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogCubeMoment z scale cutoff -
        10 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventScaledLogSqMoment z scale cutoff +
        5 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
          resolventScaledLogMoment z scale cutoff -
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
          resolventMass z (scale * cutoff) := by
  rw [resolventScaledLogFifthMoment, resolventScaledLogFifthMoment,
    resolventScaledLogFifthBoundary, resolventScaledLogFourthMoment,
    resolventScaledLogCubeMoment, resolventScaledLogSqMoment,
    resolventScaledLogMoment, resolventMass]
  rw [Nat.mul_add, Nat.mul_one, Finset.sum_range_add]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcenter :
      (∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 5 *
            resolventWeight z n) -
        ∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log cutoff) ^ 5 *
            resolventWeight z n =
        -5 * (Real.log (cutoff + 1) - Real.log cutoff) *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n +
          10 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n -
          10 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n +
          5 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n +
          -(Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            ∑ n ∈ Finset.range (scale * cutoff), resolventWeight z n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 5 *
              resolventWeight z n -
            (Real.log (n + 1) - Real.log cutoff) ^ 5 *
              resolventWeight z n =
          (-5 * (Real.log (cutoff + 1) - Real.log cutoff)) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n) +
            (10 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n) -
            (10 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) +
            (5 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4) *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (-(Real.log (cutoff + 1) - Real.log cutoff) ^ 5) *
              resolventWeight z n by
        intro n
        ring]
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [show
      (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 5 *
            resolventWeight z x) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 5 *
              resolventWeight z (scale * cutoff + x)) -
        (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 5 *
            resolventWeight z x) =
        ((∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 5 *
              resolventWeight z x) -
          (∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 5 *
              resolventWeight z x)) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 5 *
              resolventWeight z (scale * cutoff + x)) by ring]
  rw [hcenter]
  ring

/-- Increment after subtracting the predicted raw fifth-moment main term. -/
def resolventScaledLogFifthMomentIncrementError
    (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  resolventScaledLogFifthBoundary z scale cutoff -
    5 * (Real.log (cutoff + 1) - Real.log cutoff) *
      resolventScaledLogFourthMoment z scale cutoff +
    10 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
      resolventScaledLogCubeMoment z scale cutoff -
    10 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
      resolventScaledLogSqMoment z scale cutoff +
    5 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
      resolventScaledLogMoment z scale cutoff -
    (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
      resolventMass z (scale * cutoff) -
    ((scale : ℝ) *
      (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
        20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
          120 * Real.log scale - 120)) *
      resolventWeight z cutoff

/-- Sum of the scaled raw fifth-moment increment errors. -/
def resolventScaledLogFifthMomentError (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    resolventScaledLogFifthMomentIncrementError z scale n

/-- The raw fifth-moment increment error is little-o of the endpoint
resolvent weight. -/
theorem tendsto_resolventScaledLogFifthMomentIncrementError_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFifthMomentIncrementError z scale cutoff /
        resolventWeight z cutoff) atTop (nhds 0) := by
  have hboundary :=
    tendsto_resolventScaledLogFifthBoundary_div_weight hz hscale
  have hfourth :=
    tendsto_logStep_mul_resolventScaledLogFourthMoment_div_weight hz hscale
  have hcubic :=
    tendsto_logStep_sq_mul_resolventScaledLogCubeMoment_div_weight_zero
      hz hscale
  have hquadratic :=
    tendsto_logStep_cube_mul_resolventScaledLogSqMoment_div_weight_zero
      hz hscale
  have hlinear :=
    tendsto_logStep_fourth_mul_resolventScaledLogMoment_div_weight_zero
      hz hscale
  have hfifth :=
    tendsto_logStep_fifth_mul_resolventMass_nat_mul_div_weight_zero
      hz hscale
  have hconstant : Tendsto (fun _ : ℕ =>
      (scale : ℝ) * (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
        20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
          120 * Real.log scale - 120)) atTop
      (nhds ((scale : ℝ) * (Real.log scale ^ 5 -
        5 * Real.log scale ^ 4 + 20 * Real.log scale ^ 3 -
          60 * Real.log scale ^ 2 + 120 * Real.log scale - 120))) :=
    tendsto_const_nhds
  have hlimit :=
    ((((((hboundary.sub (hfourth.const_mul 5)).add
      (hcubic.const_mul 10)).sub (hquadratic.const_mul 10)).add
        (hlinear.const_mul 5)).sub hfifth).sub hconstant)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFifthBoundary z scale cutoff /
          resolventWeight z cutoff -
        5 * ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogFourthMoment z scale cutoff /
              resolventWeight z cutoff) +
        10 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogCubeMoment z scale cutoff /
              resolventWeight z cutoff) -
        10 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventScaledLogSqMoment z scale cutoff /
              resolventWeight z cutoff) +
        5 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 4 *
            resolventScaledLogMoment z scale cutoff /
              resolventWeight z cutoff) -
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 5 *
            resolventMass z (scale * cutoff) /
              resolventWeight z cutoff -
        (scale : ℝ) * (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
          20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
            120 * Real.log scale - 120))
      atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  rw [resolventScaledLogFifthMomentIncrementError]
  field_simp [hweight]

/-- Exact telescoping identity for the scaled raw fifth-moment error. -/
theorem resolventScaledLogFifthMomentError_eq
    (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogFifthMomentError z scale cutoff =
      resolventScaledLogFifthMoment z scale cutoff -
        ((scale : ℝ) *
          (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
            20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
              120 * Real.log scale - 120)) *
          resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventScaledLogFifthMomentError,
        resolventScaledLogFifthMoment, resolventMass]
  | succ cutoff ih =>
      rw [resolventScaledLogFifthMomentError, Finset.sum_range_succ]
      change resolventScaledLogFifthMomentError z scale cutoff +
        resolventScaledLogFifthMomentIncrementError z scale cutoff = _
      rw [ih, resolventScaledLogFifthMomentIncrementError]
      have hmoment := resolventScaledLogFifthMoment_succ z scale cutoff
      simp only [resolventMass, Finset.sum_range_succ]
      simp only [resolventMass] at hmoment
      change resolventScaledLogFifthMoment z scale (cutoff + 1) -
          resolventScaledLogFifthMoment z scale cutoff = _ at hmoment
      linarith

/-- The raw scaled fifth logarithmic moment centered at `log M` converges to
`ℓ(log(ℓ)⁵ - 5log(ℓ)⁴ + 20log(ℓ)³ - 60log(ℓ)² +
120log(ℓ) - 120)`. -/
theorem tendsto_resolventScaledLogFifthMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFifthMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
          20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
            120 * Real.log scale - 120))) := by
  have hincrementRatio :=
    tendsto_resolventScaledLogFifthMomentIncrementError_div_weight_zero
      hz hscale
  have hincrementSmall :
      (resolventScaledLogFifthMomentIncrementError z scale) =o[atTop]
        resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      (resolventScaledLogFifthMomentError z scale) =o[atTop]
        resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff,
        resolventScaledLogFifthMomentIncrementError z scale n) =o[atTop]
      (fun cutoff => ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFifthMomentError z scale cutoff /
        resolventMass z cutoff) atTop (nhds 0) :=
    herrorSmall.tendsto_div_nhds_zero
  have hshifted := herrorRatio.add_const
    ((scale : ℝ) * (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
      20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
        120 * Real.log scale - 120))
  have hshifted' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFifthMomentError z scale cutoff /
          resolventMass z cutoff +
        (scale : ℝ) * (Real.log scale ^ 5 - 5 * Real.log scale ^ 4 +
          20 * Real.log scale ^ 3 - 60 * Real.log scale ^ 2 +
            120 * Real.log scale - 120))
      atTop (nhds ((scale : ℝ) * (Real.log scale ^ 5 -
        5 * Real.log scale ^ 4 + 20 * Real.log scale ^ 3 -
          60 * Real.log scale ^ 2 + 120 * Real.log scale - 120))) := by
    convert hshifted using 1
    ring
  apply hshifted'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventScaledLogFifthMomentError_eq]
  field_simp [hmass]
  ring

/-- Fifth logarithmic moment below `ℓ M`, centered at the weighted
logarithmic mean `μ_M(z)`. -/
def resolventScaledCenteredLogFifthMoment (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - resolventLogMean z cutoff) ^ 5 *
      resolventWeight z n

/-- The fifth centered scalar moment from the functional-limit recurrence:
its limit is `ℓ(log(ℓ)⁵ + 10log(ℓ)³ - 20log(ℓ)² +
45log(ℓ) - 44)`. -/
theorem tendsto_resolventScaledCenteredLogFifthMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledCenteredLogFifthMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 5 + 10 * Real.log scale ^ 3 -
          20 * Real.log scale ^ 2 + 45 * Real.log scale - 44))) := by
  have hraw := tendsto_resolventScaledLogFifthMoment_div_mass hz hscale
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
    (((((hraw.add ((hmean.mul hfourth).const_mul 5)).add
      (((hmean.pow 2).mul hthird).const_mul 10)).add
        (((hmean.pow 3).mul hsecond).const_mul 10)).add
          (((hmean.pow 4).mul hfirst).const_mul 5)).add
            ((hmean.pow 5).mul hmassRatio))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogFifthMoment z scale cutoff /
          resolventMass z cutoff +
        5 * ((Real.log cutoff - resolventLogMean z cutoff) *
          (resolventScaledLogFourthMoment z scale cutoff /
            resolventMass z cutoff)) +
        10 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
          (resolventScaledLogCubeMoment z scale cutoff /
            resolventMass z cutoff)) +
        10 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
          (resolventScaledLogSqMoment z scale cutoff /
            resolventMass z cutoff)) +
        5 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
          (resolventScaledLogMoment z scale cutoff /
            resolventMass z cutoff)) +
        (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
          (resolventMass z (scale * cutoff) / resolventMass z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 5 + 10 * Real.log scale ^ 3 -
          20 * Real.log scale ^ 2 + 45 * Real.log scale - 44))) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  have hdecomp :
      resolventScaledCenteredLogFifthMoment z scale cutoff =
        resolventScaledLogFifthMoment z scale cutoff +
          5 * (Real.log cutoff - resolventLogMean z cutoff) *
            resolventScaledLogFourthMoment z scale cutoff +
          10 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
            resolventScaledLogCubeMoment z scale cutoff +
          10 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
            resolventScaledLogSqMoment z scale cutoff +
          5 * (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
            resolventScaledLogMoment z scale cutoff +
          (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
            resolventMass z (scale * cutoff) := by
    rw [resolventScaledCenteredLogFifthMoment,
      resolventScaledLogFifthMoment, resolventScaledLogFourthMoment,
      resolventScaledLogCubeMoment, resolventScaledLogSqMoment,
      resolventScaledLogMoment, resolventMass]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - resolventLogMean z cutoff) ^ 5 *
              resolventWeight z n =
          (Real.log (n + 1) - Real.log cutoff) ^ 5 *
              resolventWeight z n +
            5 * (Real.log cutoff - resolventLogMean z cutoff) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 4 *
                resolventWeight z n) +
            10 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 3 *
                resolventWeight z n) +
            10 * (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) +
            5 * (Real.log cutoff - resolventLogMean z cutoff) ^ 4 *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log cutoff - resolventLogMean z cutoff) ^ 5 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hdecomp]
  field_simp [hmass]

end

end NativeCarrySpectralWeyl.Limits
