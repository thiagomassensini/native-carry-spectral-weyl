import NativeCarrySpectralWeyl.Limits.ScalarSecondFunctionalMoment
import Mathlib.Tactic

/-!
# Third scalar moment of the resolvent functional limit

For a fixed positive natural scale `ℓ`, this file proves

`A_M(z)⁻¹ ∑_{n < ℓ M} (log(n+1) - μ_M(z))³ w_z(n)
  → ℓ (log(ℓ)³ + 3 log(ℓ) - 2)`.

The proof is discrete.  The increment of the cubic moment centered at
`log M` consists of a fixed-width cubic boundary block, the already proved
second and first logarithmic moments multiplied by the appropriate powers of
the logarithmic step, and a cubic change-of-center term.  The final two terms
are negligible.  Summing the resulting little-o increment gives the raw
third moment; the asymptotic `log M - μ_M(z) → 1` then supplies the
weighted-mean-centered moment.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

noncomputable section

/-- The fixed-width cubic boundary block created when the cutoff changes
from `M` to `M+1`. -/
def resolventScaledLogCubeBoundary (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ r ∈ Finset.range scale,
    (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 3 *
      resolventWeight z (scale * cutoff + r)

/-- Third logarithmic moment below `ℓ M`, centered at `log M`. -/
def resolventScaledLogCubeMoment (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - Real.log cutoff) ^ 3 * resolventWeight z n

/-- The normalized cubic boundary block converges to `ℓ log(ℓ)³`. -/
theorem tendsto_resolventScaledLogCubeBoundary_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogCubeBoundary z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 3)) := by
  have hterm : ∀ r ∈ Finset.range scale,
      Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 3 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
        atTop (nhds (Real.log scale ^ 3)) := by
    intro r _
    simpa only [mul_one] using
      (tendsto_log_nat_mul_add_sub_log hscale r).pow 3 |>.mul
        (tendsto_resolventWeight_nat_mul_add_div hz hscale r)
  have hsum := tendsto_finsetSum (Finset.range scale) hterm
  have hsum' : Tendsto (fun cutoff : ℕ =>
      ∑ r ∈ Finset.range scale,
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) ^ 3 *
          (resolventWeight z (scale * cutoff + r) /
            resolventWeight z cutoff))
      atTop (nhds ((scale : ℝ) * Real.log scale ^ 3)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum
  apply hsum'.congr'
  filter_upwards with cutoff
  rw [resolventScaledLogCubeBoundary, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hweight]

/-- The logarithmic change of center times the second scaled moment,
normalized by the endpoint weight, converges to the raw second-moment
coefficient. -/
theorem tendsto_logStep_mul_resolventScaledLogSqMoment_div_weight {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogSqMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 2 - 2 * Real.log scale + 2))) := by
  have hproduct :=
    (tendsto_nat_mul_log_succ_sub_log_one.mul
      (tendsto_resolventScaledLogSqMoment_div_mass hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) *
        (resolventScaledLogSqMoment z scale cutoff /
          resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 2 - 2 * Real.log scale + 2))) := by
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

/-- The squared logarithmic step times the first scaled moment is negligible
relative to the endpoint weight. -/
theorem tendsto_logStep_sq_mul_resolventScaledLogMoment_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogMoment z scale cutoff /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hinvNat : Tendsto (fun cutoff : ℕ => ((cutoff : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hproduct :=
    (((tendsto_nat_mul_log_succ_sub_log_one.pow 2).mul
      (tendsto_resolventScaledLogMoment_div_mass hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)).mul hinvNat
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) ^ 2 *
        (resolventScaledLogMoment z scale cutoff / resolventMass z cutoff) *
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

/-- The cubic change-of-center correction is negligible relative to the
endpoint weight. -/
theorem tendsto_logStep_cube_mul_resolventMass_nat_mul_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventMass z (scale * cutoff) /
        resolventWeight z cutoff)
      atTop (nhds 0) := by
  have hinvNat : Tendsto (fun cutoff : ℕ => ((cutoff : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hproduct :=
    (((tendsto_nat_mul_log_succ_sub_log_one.pow 3).mul
      (tendsto_resolventMass_nat_mul_div hz hscale)).mul
        (tendsto_resolventMass_div_scale_one hz)).mul (hinvNat.pow 2)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (((cutoff : ℝ) *
          (Real.log (cutoff + 1) - Real.log cutoff)) ^ 3 *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff) *
        (resolventMass z cutoff / resolventScale z cutoff)) *
          ((cutoff : ℝ))⁻¹ ^ 2) atTop (nhds 0) := by
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

/-- Exact increment identity for the scaled third logarithmic moment. -/
theorem resolventScaledLogCubeMoment_succ (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogCubeMoment z scale (cutoff + 1) -
        resolventScaledLogCubeMoment z scale cutoff =
      resolventScaledLogCubeBoundary z scale cutoff -
        3 * (Real.log (cutoff + 1) - Real.log cutoff) *
          resolventScaledLogSqMoment z scale cutoff +
        3 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
          resolventScaledLogMoment z scale cutoff -
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
          resolventMass z (scale * cutoff) := by
  rw [resolventScaledLogCubeMoment, resolventScaledLogCubeMoment,
    resolventScaledLogCubeBoundary, resolventScaledLogSqMoment,
    resolventScaledLogMoment, resolventMass]
  rw [Nat.mul_add, Nat.mul_one, Finset.sum_range_add]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcenter :
      (∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 3 *
            resolventWeight z n) -
        ∑ n ∈ Finset.range (scale * cutoff),
          (Real.log (n + 1) - Real.log cutoff) ^ 3 *
            resolventWeight z n =
        -3 * (Real.log (cutoff + 1) - Real.log cutoff) *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n +
          3 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              (Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n -
          (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff), resolventWeight z n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - Real.log (cutoff + 1)) ^ 3 *
              resolventWeight z n -
            (Real.log (n + 1) - Real.log cutoff) ^ 3 *
              resolventWeight z n =
          (-3 * (Real.log (cutoff + 1) - Real.log cutoff)) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) +
            (3 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2) *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) -
            (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [show
      (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 3 *
            resolventWeight z x) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 3 *
              resolventWeight z (scale * cutoff + x)) -
        (∑ x ∈ Finset.range (scale * cutoff),
          (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 3 *
            resolventWeight z x) =
        ((∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log ((cutoff : ℝ) + 1)) ^ 3 *
              resolventWeight z x) -
          (∑ x ∈ Finset.range (scale * cutoff),
            (Real.log ((x : ℝ) + 1) - Real.log cutoff) ^ 3 *
              resolventWeight z x)) +
          (∑ x ∈ Finset.range scale,
            (Real.log ((scale : ℝ) * cutoff + x + 1) -
                Real.log ((cutoff : ℝ) + 1)) ^ 3 *
              resolventWeight z (scale * cutoff + x)) by ring]
  rw [hcenter]
  ring

/-- Increment after subtracting the predicted raw third-moment main term. -/
def resolventScaledLogCubeMomentIncrementError
    (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  resolventScaledLogCubeBoundary z scale cutoff -
    3 * (Real.log (cutoff + 1) - Real.log cutoff) *
      resolventScaledLogSqMoment z scale cutoff +
    3 * (Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
      resolventScaledLogMoment z scale cutoff -
    (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
      resolventMass z (scale * cutoff) -
    ((scale : ℝ) *
      (Real.log scale ^ 3 - 3 * Real.log scale ^ 2 +
        6 * Real.log scale - 6)) * resolventWeight z cutoff

/-- Sum of the scaled raw third-moment increment errors. -/
def resolventScaledLogCubeMomentError (z : ℂ) (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff,
    resolventScaledLogCubeMomentIncrementError z scale n

/-- The raw third-moment increment error is little-o of the endpoint
resolvent weight. -/
theorem tendsto_resolventScaledLogCubeMomentIncrementError_div_weight_zero
    {z : ℂ} (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogCubeMomentIncrementError z scale cutoff /
        resolventWeight z cutoff) atTop (nhds 0) := by
  have hboundary := tendsto_resolventScaledLogCubeBoundary_div_weight hz hscale
  have hquadratic :=
    tendsto_logStep_mul_resolventScaledLogSqMoment_div_weight hz hscale
  have hlinear :=
    tendsto_logStep_sq_mul_resolventScaledLogMoment_div_weight_zero hz hscale
  have hcubic :=
    tendsto_logStep_cube_mul_resolventMass_nat_mul_div_weight_zero hz hscale
  have hconstant : Tendsto (fun _ : ℕ =>
      (scale : ℝ) * (Real.log scale ^ 3 - 3 * Real.log scale ^ 2 +
        6 * Real.log scale - 6)) atTop
      (nhds ((scale : ℝ) * (Real.log scale ^ 3 -
        3 * Real.log scale ^ 2 + 6 * Real.log scale - 6))) :=
    tendsto_const_nhds
  have hlimit :=
    ((((hboundary.sub (hquadratic.const_mul 3)).add
      (hlinear.const_mul 3)).sub hcubic).sub hconstant)
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogCubeBoundary z scale cutoff /
          resolventWeight z cutoff -
        3 * ((Real.log (cutoff + 1) - Real.log cutoff) *
            resolventScaledLogSqMoment z scale cutoff /
              resolventWeight z cutoff) +
        3 * ((Real.log (cutoff + 1) - Real.log cutoff) ^ 2 *
            resolventScaledLogMoment z scale cutoff /
              resolventWeight z cutoff) -
        (Real.log (cutoff + 1) - Real.log cutoff) ^ 3 *
            resolventMass z (scale * cutoff) /
              resolventWeight z cutoff -
        (scale : ℝ) * (Real.log scale ^ 3 -
          3 * Real.log scale ^ 2 + 6 * Real.log scale - 6))
      atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hweight : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  rw [resolventScaledLogCubeMomentIncrementError]
  field_simp [hweight]

/-- Exact telescoping identity for the scaled raw third-moment error. -/
theorem resolventScaledLogCubeMomentError_eq
    (z : ℂ) (scale cutoff : ℕ) :
    resolventScaledLogCubeMomentError z scale cutoff =
      resolventScaledLogCubeMoment z scale cutoff -
        ((scale : ℝ) *
          (Real.log scale ^ 3 - 3 * Real.log scale ^ 2 +
            6 * Real.log scale - 6)) * resolventMass z cutoff := by
  induction cutoff with
  | zero =>
      simp [resolventScaledLogCubeMomentError, resolventScaledLogCubeMoment,
        resolventMass]
  | succ cutoff ih =>
      rw [resolventScaledLogCubeMomentError, Finset.sum_range_succ]
      change resolventScaledLogCubeMomentError z scale cutoff +
        resolventScaledLogCubeMomentIncrementError z scale cutoff = _
      rw [ih, resolventScaledLogCubeMomentIncrementError]
      have hmoment := resolventScaledLogCubeMoment_succ z scale cutoff
      simp only [resolventMass, Finset.sum_range_succ]
      simp only [resolventMass] at hmoment
      change resolventScaledLogCubeMoment z scale (cutoff + 1) -
          resolventScaledLogCubeMoment z scale cutoff = _ at hmoment
      linarith

/-- The raw scaled third logarithmic moment centered at `log M` converges to
`ℓ(log(ℓ)³ - 3log(ℓ)² + 6log(ℓ) - 6)`. -/
theorem tendsto_resolventScaledLogCubeMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledLogCubeMoment z scale cutoff / resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 3 - 3 * Real.log scale ^ 2 +
          6 * Real.log scale - 6))) := by
  have hincrementRatio :=
    tendsto_resolventScaledLogCubeMomentIncrementError_div_weight_zero
      hz hscale
  have hincrementSmall :
      (resolventScaledLogCubeMomentIncrementError z scale) =o[atTop]
        resolventWeight z :=
    (Asymptotics.isLittleO_iff_tendsto' <| by
      filter_upwards with cutoff
      exact fun hzero =>
        (ne_of_gt (resolventWeight_pos hz cutoff) hzero).elim).2
      hincrementRatio
  have herrorSmall :
      (resolventScaledLogCubeMomentError z scale) =o[atTop]
        resolventMass z := by
    have hsum := hincrementSmall.sum_range
      (fun cutoff => (resolventWeight_pos hz cutoff).le)
      (tendsto_resolventMass_atTop hz)
    change (fun cutoff =>
      ∑ n ∈ Finset.range cutoff,
        resolventScaledLogCubeMomentIncrementError z scale n) =o[atTop]
      (fun cutoff => ∑ n ∈ Finset.range cutoff, resolventWeight z n)
    simpa only using hsum
  have herrorRatio : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogCubeMomentError z scale cutoff /
        resolventMass z cutoff) atTop (nhds 0) :=
    herrorSmall.tendsto_div_nhds_zero
  have hshifted := herrorRatio.add_const
    ((scale : ℝ) * (Real.log scale ^ 3 - 3 * Real.log scale ^ 2 +
      6 * Real.log scale - 6))
  have hshifted' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogCubeMomentError z scale cutoff /
          resolventMass z cutoff +
        (scale : ℝ) * (Real.log scale ^ 3 - 3 * Real.log scale ^ 2 +
          6 * Real.log scale - 6))
      atTop (nhds ((scale : ℝ) * (Real.log scale ^ 3 -
        3 * Real.log scale ^ 2 + 6 * Real.log scale - 6))) := by
    convert hshifted using 1
    ring
  apply hshifted'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  rw [resolventScaledLogCubeMomentError_eq]
  field_simp [hmass]
  ring

/-- Third logarithmic moment below `ℓ M`, centered at the weighted logarithmic
mean `μ_M(z)`. -/
def resolventScaledCenteredLogCubeMoment (z : ℂ)
    (scale cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (scale * cutoff),
    (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 *
      resolventWeight z n

/-- The third centered scalar moment from the functional-limit notes:
its limit is `ℓ(log(ℓ)³ + 3log(ℓ) - 2)`. -/
theorem tendsto_resolventScaledCenteredLogCubeMoment_div_mass {z : ℂ}
    (hz : z.im ≠ 0) {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScaledCenteredLogCubeMoment z scale cutoff /
        resolventMass z cutoff)
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 3 + 3 * Real.log scale - 2))) := by
  have hraw := tendsto_resolventScaledLogCubeMoment_div_mass hz hscale
  have hsecond := tendsto_resolventScaledLogSqMoment_div_mass hz hscale
  have hfirst := tendsto_resolventScaledLogMoment_div_mass hz hscale
  have hmean : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff - resolventLogMean z cutoff) atTop (nhds 1) := by
    have h := (tendsto_resolventLogMean_sub_log hz).neg
    simpa only [neg_sub, neg_neg] using h
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hlimit :=
    (((hraw.add ((hmean.mul hsecond).const_mul 3)).add
      (((hmean.pow 2).mul hfirst).const_mul 3)).add
        ((hmean.pow 3).mul hmassRatio))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      resolventScaledLogCubeMoment z scale cutoff / resolventMass z cutoff +
        3 * ((Real.log cutoff - resolventLogMean z cutoff) *
          (resolventScaledLogSqMoment z scale cutoff /
            resolventMass z cutoff)) +
        3 * ((Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
          (resolventScaledLogMoment z scale cutoff /
            resolventMass z cutoff)) +
        (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
          (resolventMass z (scale * cutoff) / resolventMass z cutoff))
      atTop (nhds ((scale : ℝ) *
        (Real.log scale ^ 3 + 3 * Real.log scale - 2))) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards [(tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hmass
  have hdecomp :
      resolventScaledCenteredLogCubeMoment z scale cutoff =
        resolventScaledLogCubeMoment z scale cutoff +
          3 * (Real.log cutoff - resolventLogMean z cutoff) *
            resolventScaledLogSqMoment z scale cutoff +
          3 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
            resolventScaledLogMoment z scale cutoff +
          (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
            resolventMass z (scale * cutoff) := by
    rw [resolventScaledCenteredLogCubeMoment,
      resolventScaledLogCubeMoment, resolventScaledLogSqMoment,
      resolventScaledLogMoment, resolventMass]
    simp_rw [show ∀ n : ℕ,
        (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 *
              resolventWeight z n =
          (Real.log (n + 1) - Real.log cutoff) ^ 3 *
              resolventWeight z n +
            3 * (Real.log cutoff - resolventLogMean z cutoff) *
              ((Real.log (n + 1) - Real.log cutoff) ^ 2 *
                resolventWeight z n) +
            3 * (Real.log cutoff - resolventLogMean z cutoff) ^ 2 *
              ((Real.log (n + 1) - Real.log cutoff) *
                resolventWeight z n) +
            (Real.log cutoff - resolventLogMean z cutoff) ^ 3 *
              resolventWeight z n by
        intro n
        ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [hdecomp]
  field_simp [hmass]

end

end NativeCarrySpectralWeyl.Limits
