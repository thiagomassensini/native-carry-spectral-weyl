import NativeCarrySpectralWeyl.Limits.ScalarFunctionalMoment
import Mathlib.Tactic

/-!
# Second scalar moment of the resolvent functional limit

For a fixed positive natural scale `ℓ`, this file proves

`A_M(z)⁻¹ ∑_{n < ℓ M} (log(n+1) - μ_M(z))² w_z(n)
  → ℓ (1 + log(ℓ)²)`.

The proof remains discrete.  The increment of the quadratic moment centered
at `log M` consists of a fixed-width squared boundary block, a term involving
the already formalized first logarithmic moment, and a quadratic change of
center which is negligible.  Summing the resulting little-o increment gives
the raw second moment; the asymptotic `log M - μ_M(z) → 1` then supplies the
documented weighted-mean-centered moment.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- The fixed-width quadratic boundary block created when the cutoff changes
from `M` to `M+1`. -/
def resolventScaledLogSqBoundary (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ r ∈ Finset.range scale,
    (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 2 *
      resolventWeight z (scale * cutoff + r)

/-- Second logarithmic moment below `ℓ M`, centered at `log M`. -/
def resolventScaledLogSqMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - Real.log cutoff) ^ 2 * resolventWeight z n

/-- The normalized quadratic boundary block converges to
`ℓ log(ℓ)²`. -/
theorem tendsto_resolventScaledLogSqBoundary_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSqBoundary z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 2)) := by
  have hterm : ∀ r ∈ Finset.range scale,
      Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 2 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
        atTop (nhds (Real.log scale ^ 2)) := by
    intro r _
    simpa only [mul_one] using
      (tendsto_log_nat_mul_add_sub_log hscale r).pow 2 |>.mul
        (tendsto_resolventWeight_nat_mul_add_div hz hscale r)
  have hsum := tendsto_finsetSum (Finset.range scale) hterm
  have hsum' : Tendsto (fun cutoff : ℕ =>
      ∑ r ∈ Finset.range scale,
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 2 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 2)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [resolventScaledLogSqBoundary, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hweight]

/-- The logarithmic change of center times the first scaled moment, normalized
by the endpoint weight, converges to `ℓ(log ℓ - 1)`. -/
theorem tendsto_logStep_mul_resolventScaledLogMoment_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * (Real.log scale - 1))) := by
  have hproduct :=
    (tendsto_nat_mul_log_succ_sub_log_one.mul
      (tendsto_resolventScaledLogMoment_div_mass hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) *
        (resolventScaledLogMoment z scale cutoff /
          resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff))
      atTop (nhds ((scale : ℝ) * (Real.log scale - 1))) := by
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

/-- The quadratic change-of-center correction is negligible relative to the
endpoint weight. -/
theorem tendsto_logStep_sq_mul_resolventMass_nat_mul_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventMass z (scale * cutoff) /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hinvNat : Tendsto (fun cutoff : ℕ => ((cutoff : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hproduct :=
    (((tendsto_nat_mul_log_succ_sub_log_one.pow 2).mul
      (tendsto_resolventMass_nat_mul_div hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)).mul hinvNat
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) ^ 2 *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff)) *
          ((cutoff : ℝ))⁻¹) atTop (nhds 0) := by
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

/-- Exact increment identity for the scaled second logarithmic moment. -/
theorem resolventScaledLogSqMoment_succ (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogSqMoment z scale (cutoff + 1) -
        resolventScaledLogSqMoment z scale cutoff =
      resolventScaledLogSqBoundary z scale cutoff -
        2 * (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogMoment z scale cutoff +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventMass z (scale * cutoff) := by
  rw [resolventScaledLogSqMoment, resolventScaledLogSqMoment,
    resolventScaledLogSqBoundary, resolventScaledLogMoment, resolventMass]
  rw [Nat.mul_add, Nat.mul_one, Finset.sum_range_add]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcenter :
      (∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 2 *
            resolventWeight z n) -
        ∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log cutoff) ^ 2 *
            resolventWeight z n =
        -2 * (Real.log (cutoff + 1) - Real.log cutoff) *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n +
          (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff), resolventWeight z n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 2 *
              resolventWeight z n -
            (Real.log (n + 1) - Real.log cutoff) ^ 2 *
              resolventWeight z n =
          (-2 * (Real.log (cutoff + 1) - Real.log cutoff)) *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [show
      (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 2 *
            resolventWeight z x) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 2 *
              resolventWeight z (scale * cutoff + x)) -
        (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 2 *
            resolventWeight z x) =
        ((∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 2 *
              resolventWeight z x) -
          (∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 2 *
              resolventWeight z x)) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 2 *
              resolventWeight z (scale * cutoff + x)) by ring]
  rw [hcenter]
  ring

/-- Increment after subtracting the predicted raw second-moment main term. -/
def resolventScaledLogSqMomentIncrementError
    (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  resolventScaledLogSqBoundary z scale cutoff -
    2 * (Real.log (cutoff + 1) - Real.log cutoff) *
      resolventScaledLogMoment z scale cutoff +
    (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
      resolventMass z (scale * cutoff) -
    ((scale : ℝ) *
      (Real.log scale ^ 2 - 2 * Real.log scale + 2)) *
        resolventWeight z cutoff

/-- Sum of the scaled raw second-moment increment errors. -/
def resolventScaledLogSqMomentError (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    resolventScaledLogSqMomentIncrementError z scale n

/-- The raw second-moment increment error is little-o of the endpoint
resolvent weight. -/
theorem tendsto_resolventScaledLogSqMomentIncrementError_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSqMomentIncrementError z scale cutoff /
        resolventWeight z cutoff) atTop (nhds 0) := by
  have hboundary := tendsto_resolventScaledLogSqBoundary_div_weight hz hscale
  have hlinear :=
    tendsto_logStep_mul_resolventScaledLogMoment_div_weight hz hscale
  have hquadratic :=
    tendsto_logStep_sq_mul_resolventMass_nat_mul_div_weight_zero hz hscale
  have hconstant : Tendsto (fun _ : ℕ =>
      (scale : ℝ) * (Real.log scale ^ 2 - 2 * Real.log scale + 2))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 2 - 2 * Real.log scale + 2))) :=
    tendsto_const_nhds
  have hlimit := ((hboundary.sub (hlinear.const_mul 2)).add hquadratic).sub
    hconstant
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSqBoundary z scale cutoff /
          resolventWeight z cutoff -
        2 * ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogMoment z scale cutoff /
              resolventWeight z cutoff) +
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventMass z (scale * cutoff) /
              resolventWeight z cutoff -
        (scale : ℝ) *
          (Real.log scale ^ 2 - 2 * Real.log scale + 2))
      atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  rw [resolventScaledLogSqMomentIncrementError]
  field_simp [hweight]

/-- Exact telescoping identity for the scaled raw second-moment error. -/
theorem resolventScaledLogSqMomentError_eq
    (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogSqMomentError z scale cutoff =
      resolventScaledLogSqMoment z scale cutoff -
        ((scale : ℝ) *
          (Real.log scale ^ 2 - 2 * Real.log scale + 2)) *
            resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventScaledLogSqMomentError, resolventScaledLogSqMoment,
        resolventMass]
  | succ cutoff ih =>
      rw [resolventScaledLogSqMomentError, Finset.sum_range_succ]
      change resolventScaledLogSqMomentError z scale cutoff +
        resolventScaledLogSqMomentIncrementError z scale cutoff = _
      rw [ih, resolventScaledLogSqMomentIncrementError]
      have hmoment := resolventScaledLogSqMoment_succ z scale cutoff
      simp only [resolventMass, Finset.sum_range_succ]
      simp only [resolventMass] at hmoment
      change resolventScaledLogSqMoment z scale (cutoff + 1) -
          resolventScaledLogSqMoment z scale cutoff = _ at hmoment
      linarith

/-- The raw scaled second logarithmic moment centered at `log M` converges to
`ℓ(log(ℓ)² - 2 log(ℓ) + 2)`. -/
theorem tendsto_resolventScaledLogSqMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSqMoment z scale cutoff / resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 2 - 2 * Real.log scale + 2))) := by
  have hincrementRatio :=
    tendsto_resolventScaledLogSqMomentIncrementError_div_weight_zero hz hscale
  have hincrementSmall :
      (resolventScaledLogSqMomentIncrementError z scale) =o[atTop]
        resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      (resolventScaledLogSqMomentError z scale) =o[atTop]
        resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff,
        resolventScaledLogSqMomentIncrementError z scale n) =o[atTop]
      (fun cutoff => ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSqMomentError z scale cutoff /
        resolventMass z cutoff) atTop (nhds 0) :=
    herrorSmall.tendsto_div_nhds_zero
  have hshifted := herrorRatio.add_const
    ((scale : ℝ) * (Real.log scale ^ 2 - 2 * Real.log scale + 2))
  have hshifted' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSqMomentError z scale cutoff /
          resolventMass z cutoff +
        (scale : ℝ) * (Real.log scale ^ 2 - 2 * Real.log scale + 2))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 2 - 2 * Real.log scale + 2))) := by
    convert hshifted using 1
    ring
  apply hshifted'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventScaledLogSqMomentError_eq]
  field_simp [hmass]
  ring

/-- Second logarithmic moment below `ℓ M`, centered at the weighted
logarithmic mean `μ_M(z)`. -/
def resolventScaledCenteredLogSqMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 *
      resolventWeight z n

/-- The second centered scalar moment from the functional-limit notes:
its limit is `ℓ(1 + log(ℓ)²)`. -/
theorem tendsto_resolventScaledCenteredLogSqMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledCenteredLogSqMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) * (1 + Real.log scale ^ 2))) := by
  have hraw := tendsto_resolventScaledLogSqMoment_div_mass hz hscale
  have hfirst := tendsto_resolventScaledLogMoment_div_mass hz hscale
  have hmean : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff - resolventLogMean z cutoff) atTop (nhds 1) := by
    have h := (tendsto_resolventLogMean_sub_log hz).neg
    simpa only [neg_sub, neg_neg] using h
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hlimit := (hraw.add ((hmean.mul hfirst).const_mul 2)).add
    ((hmean.pow 2).mul hmassRatio)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogSqMoment z scale cutoff / resolventMass z cutoff +
        2 * ((Real.log cutoff - resolventLogMean z cutoff) *
          (resolventScaledLogMoment z scale cutoff /
            resolventMass z cutoff)) +
        (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
          (resolventMass z (scale * cutoff) / resolventMass z cutoff))
      atTop (nhds ((scale : ℝ) * (1 + Real.log scale ^ 2))) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  have hdecomp :
      resolventScaledCenteredLogSqMoment z scale cutoff =
        resolventScaledLogSqMoment z scale cutoff +
          2 * (Real.log cutoff - resolventLogMean z cutoff) *
            resolventScaledLogMoment z scale cutoff +
          (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
            resolventMass z (scale * cutoff) := by
    rw [resolventScaledCenteredLogSqMoment, resolventScaledLogSqMoment,
      resolventScaledLogMoment, resolventMass]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - resolventLogMean z cutoff) ^ 2 *
              resolventWeight z n =
          (Real.log (n + 1) - Real.log cutoff) ^ 2 *
              resolventWeight z n +
            2 * (Real.log cutoff - resolventLogMean z cutoff) *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hdecomp]
  field_simp [hmass]

end

end NativeCarrySpectralWeyl.Limits
