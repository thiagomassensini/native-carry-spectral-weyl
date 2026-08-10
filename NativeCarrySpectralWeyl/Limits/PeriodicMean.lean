import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Cesàro limits of periodic sequences

This file supplies the arithmetic core of the cutoff-to-limit passage for the
native carry cameras.  A periodic vector-valued sequence has Cesàro mean equal
to the average over one period.  The proof keeps the finite-cutoff error
explicit: after subtracting the period mean, every complete block cancels and
only a prefix shorter than one period remains.
-/

open scoped BigOperators
open Filter

namespace NativeCarrySpectralWeyl.Limits

variable {E : Type*} [NormedAddCommGroup E]

/-- The average of a sequence over the half-open period `0, ..., period - 1`. -/
noncomputable def periodMean [NormedSpace ℝ E] (q : ℕ → E) (period : ℕ) : E :=
  (period : ℝ)⁻¹ • ∑ r ∈ Finset.range period, q r

/-- A periodic sum over an integral number of periods is the corresponding
natural multiple of the sum over one period. -/
theorem sum_range_mul_period {q : ℕ → E} {period : ℕ}
    (hq : Function.Periodic q period) (blocks : ℕ) :
    ∑ n ∈ Finset.range (blocks * period), q n =
      blocks • ∑ r ∈ Finset.range period, q r := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hshift : ∑ r ∈ Finset.range period, q (blocks * period + r) =
          ∑ r ∈ Finset.range period, q r := by
        apply Finset.sum_congr rfl
        intro r hr
        simpa [nsmul_eq_mul, Nat.add_comm, Nat.mul_comm] using (hq.nsmul blocks r)
      rw [hshift, add_nsmul]
      simp

/-- Split a periodic prefix into complete periods and its final incomplete
period. -/
theorem sum_range_eq_blocks_add_remainder {q : ℕ → E} {period : ℕ}
    (hq : Function.Periodic q period) (cutoff : ℕ) :
    ∑ n ∈ Finset.range cutoff, q n =
      (cutoff / period) • ∑ r ∈ Finset.range period, q r +
        ∑ r ∈ Finset.range (cutoff % period), q r := by
  have hcutoff : cutoff = (cutoff / period) * period + cutoff % period := by
    calc
      cutoff = period * (cutoff / period) + cutoff % period :=
        (Nat.div_add_mod cutoff period).symm
      _ = (cutoff / period) * period + cutoff % period := by rw [Nat.mul_comm]
  calc
    ∑ n ∈ Finset.range cutoff, q n =
        ∑ n ∈ Finset.range ((cutoff / period) * period + cutoff % period), q n := by
          exact congrArg (fun bound => ∑ n ∈ Finset.range bound, q n) hcutoff
    _ = ∑ n ∈ Finset.range ((cutoff / period) * period), q n +
        ∑ r ∈ Finset.range (cutoff % period), q ((cutoff / period) * period + r) :=
          Finset.sum_range_add _ _ _
    _ = (cutoff / period) • ∑ r ∈ Finset.range period, q r +
        ∑ r ∈ Finset.range (cutoff % period), q r := by
          rw [sum_range_mul_period hq]
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          simpa [nsmul_eq_mul, Nat.add_comm, Nat.mul_comm] using
            (hq.nsmul (cutoff / period) r)

/-- If the sum over one period vanishes, every prefix sum is exactly the sum
over the final incomplete period. -/
theorem sum_range_eq_remainder_of_periodic_of_sum_eq_zero {q : ℕ → E} {period : ℕ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) (cutoff : ℕ) :
    ∑ n ∈ Finset.range cutoff, q n =
      ∑ r ∈ Finset.range (cutoff % period), q r := by
  rw [sum_range_eq_blocks_add_remainder hq, hsum, nsmul_zero, zero_add]

/-- The prefix sums of a zero-mean periodic sequence are uniformly bounded by
the sum of the norms over one period. -/
theorem norm_sum_range_le_period_norm_sum {q : ℕ → E} {period : ℕ}
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) (cutoff : ℕ) :
    ‖∑ n ∈ Finset.range cutoff, q n‖ ≤
      ∑ r ∈ Finset.range period, ‖q r‖ := by
  rw [sum_range_eq_remainder_of_periodic_of_sum_eq_zero hq hsum]
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.mod_lt cutoff hperiod).le)
    (fun _ _ _ => norm_nonneg _)

/-- Normalized prefix sums of a zero-mean periodic sequence converge to zero. -/
theorem tendsto_inv_smul_sum_range_zero_of_periodic {q : ℕ → E} {period : ℕ}
    [NormedSpace ℝ E]
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (cutoff : ℝ)⁻¹ • ∑ n ∈ Finset.range cutoff, q n) atTop (nhds 0) := by
  apply (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).zero_smul_isBoundedUnder_le
  change ∃ bound : ℝ, ∀ᶠ cutoff : ℕ in atTop,
    ‖∑ n ∈ Finset.range cutoff, q n‖ ≤ bound
  refine ⟨∑ r ∈ Finset.range period, ‖q r‖, Filter.Eventually.of_forall ?_⟩
  exact norm_sum_range_le_period_norm_sum hperiod hq hsum

/-- The sum of the centered sequence over one period is zero. -/
theorem sum_period_sub_periodMean {q : ℕ → E} {period : ℕ}
    [NormedSpace ℝ E]
    (hperiod : 0 < period) :
    ∑ r ∈ Finset.range period, (q r - periodMean q period) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  simp only [periodMean, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hperiod.ne'), one_smul, sub_self]

/-- A periodic sequence converges in Cesàro mean to its average over one
period.  The target may be any real normed vector space. -/
theorem tendsto_periodic_cesaro {q : ℕ → E} {period : ℕ}
    [NormedSpace ℝ E]
    (hperiod : 0 < period) (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (cutoff : ℝ)⁻¹ • ∑ n ∈ Finset.range cutoff, q n)
      atTop (nhds (periodMean q period)) := by
  let centered : ℕ → E := fun n => q n - periodMean q period
  have hcentered : Function.Periodic centered period := by
    intro n
    simp only [centered]
    rw [hq n]
  have hcenteredSum : ∑ r ∈ Finset.range period, centered r = 0 := by
    simpa only [centered] using sum_period_sub_periodMean (q := q) hperiod
  have hzero := tendsto_inv_smul_sum_range_zero_of_periodic
    hperiod hcentered hcenteredSum
  have hadd : Tendsto (fun cutoff : ℕ =>
      (cutoff : ℝ)⁻¹ • ∑ n ∈ Finset.range cutoff, centered n + periodMean q period)
      atTop (nhds (periodMean q period)) := by
    simpa using hzero.add_const (periodMean q period)
  apply hadd.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with cutoff hcutoff
  have hcutoff0 : (cutoff : ℝ) ≠ 0 := by positivity
  simp only [centered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul,
    inv_mul_cancel₀ hcutoff0, one_smul, sub_add_cancel]

/-- A Dirichlet--Abel form of the periodic weighted-mean lemma.

If the weights decrease to zero while their partial sums diverge to `+∞`,
then the normalized weighted mean of a periodic vector-valued sequence has the
same limit as its ordinary period mean.  This is the form used for the
resolvent weights in the cutoff covariance. -/
theorem tendsto_periodic_weightedMean {q : ℕ → E} {period : ℕ} {weight : ℕ → ℝ}
    [NormedSpace ℝ E]
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hweightAnti : Antitone weight) (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop) :
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff, weight n)⁻¹ •
        ∑ n ∈ Finset.range cutoff, weight n • q n)
      atTop (nhds (periodMean q period)) := by
  let centered : ℕ → E := fun n => q n - periodMean q period
  let mass : ℕ → ℝ := fun cutoff => ∑ n ∈ Finset.range cutoff, weight n
  let centeredNumerator : ℕ → E := fun cutoff =>
    ∑ n ∈ Finset.range cutoff, weight n • centered n
  have hcentered : Function.Periodic centered period := by
    intro n
    simp only [centered]
    rw [hq n]
  have hcenteredSum : ∑ r ∈ Finset.range period, centered r = 0 := by
    simpa only [centered] using sum_period_sub_periodMean (q := q) hperiod
  let bound : ℝ := ∑ r ∈ Finset.range period, ‖centered r‖
  have hprefixBound (cutoff : ℕ) :
      ‖∑ n ∈ Finset.range cutoff, centered n‖ ≤ bound := by
    exact norm_sum_range_le_period_norm_sum hperiod hcentered hcenteredSum cutoff
  have hcenteredCauchy : CauchySeq centeredNumerator := by
    exact hweightAnti.cauchySeq_series_mul_of_tendsto_zero_of_bounded
      hweightZero hprefixBound
  have hcenteredBounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ centeredNumerator) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hcenteredCauchy.isBounded_range
    change ∃ C : ℝ, ∀ᶠ cutoff : ℕ in atTop, ‖centeredNumerator cutoff‖ ≤ C
    exact ⟨C, Filter.Eventually.of_forall fun cutoff =>
      hC (centeredNumerator cutoff) ⟨cutoff, rfl⟩⟩
  have hinvMass : Tendsto (fun cutoff => (mass cutoff)⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp hmass
  have hcenteredZero : Tendsto (fun cutoff =>
      (mass cutoff)⁻¹ • centeredNumerator cutoff) atTop (nhds 0) :=
    hinvMass.zero_smul_isBoundedUnder_le hcenteredBounded
  have hadd : Tendsto (fun cutoff =>
      (mass cutoff)⁻¹ • centeredNumerator cutoff + periodMean q period)
      atTop (nhds (periodMean q period)) := by
    simpa using hcenteredZero.add_const (periodMean q period)
  apply hadd.congr'
  filter_upwards [hmass.eventually_gt_atTop 0] with cutoff hmassPos
  have hmass0 : mass cutoff ≠ 0 := ne_of_gt hmassPos
  have hmass0' : (∑ n ∈ Finset.range cutoff, weight n) ≠ 0 := by
    simpa only [mass] using hmass0
  simp only [mass, centeredNumerator, centered, smul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [smul_smul, inv_mul_cancel₀ hmass0', one_smul, sub_add_cancel]

/-- Translating a periodic sequence does not change its sum over one complete
period. -/
theorem sum_period_natAdd {q : ℕ → E} {period : ℕ}
    (hq : Function.Periodic q period) (offset : ℕ) :
    ∑ r ∈ Finset.range period, q (offset + r) =
      ∑ r ∈ Finset.range period, q r := by
  apply add_left_cancel (a := ∑ r ∈ Finset.range offset, q r)
  calc
    (∑ r ∈ Finset.range offset, q r) +
        ∑ r ∈ Finset.range period, q (offset + r) =
      ∑ r ∈ Finset.range (offset + period), q r :=
        (Finset.sum_range_add q offset period).symm
    _ = ∑ r ∈ Finset.range (period + offset), q r := by rw [Nat.add_comm]
    _ = (∑ r ∈ Finset.range period, q r) +
        ∑ r ∈ Finset.range offset, q (period + r) :=
          Finset.sum_range_add q period offset
    _ = (∑ r ∈ Finset.range period, q r) +
        ∑ r ∈ Finset.range offset, q r := by
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          simpa only [Nat.add_comm] using hq r
    _ = (∑ r ∈ Finset.range offset, q r) +
        ∑ r ∈ Finset.range period, q r := add_comm _ _

/-- Translating a periodic sequence does not change its period mean. -/
theorem periodMean_natAdd {q : ℕ → E} {period : ℕ} [NormedSpace ℝ E]
    (hq : Function.Periodic q period) (offset : ℕ) :
    periodMean (fun n => q (offset + n)) period = periodMean q period := by
  simp only [periodMean]
  rw [sum_period_natAdd hq offset]

/-- Dirichlet--Abel periodic averaging when the weight is antitone only after
a finite prefix.  Both the finite mass and numerator prefix disappear after
normalization by the divergent total mass. -/
theorem tendsto_periodic_weightedMean_of_eventually_antitone
    {q : ℕ → E} {period : ℕ} {weight : ℕ → ℝ}
    [NormedSpace ℝ E]
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hweightAnti : ∃ offset : ℕ, Antitone (fun n => weight (n + offset)))
    (hweightZero : Tendsto weight atTop (nhds 0))
    (hmass : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, weight n) atTop atTop) :
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff, weight n)⁻¹ •
        ∑ n ∈ Finset.range cutoff, weight n • q n)
      atTop (nhds (periodMean q period)) := by
  obtain ⟨offset, hanti⟩ := hweightAnti
  let shiftedWeight : ℕ → ℝ := fun n => weight (n + offset)
  let shiftedQ : ℕ → E := fun n => q (offset + n)
  let mass : ℕ → ℝ := fun cutoff => ∑ n ∈ Finset.range cutoff, weight n
  let shiftedMass : ℕ → ℝ := fun cutoff =>
    ∑ n ∈ Finset.range cutoff, shiftedWeight n
  let numerator : ℕ → E := fun cutoff =>
    ∑ n ∈ Finset.range cutoff, weight n • q n
  let shiftedNumerator : ℕ → E := fun cutoff =>
    ∑ n ∈ Finset.range cutoff, shiftedWeight n • shiftedQ n
  let prefixMass : ℝ := mass offset
  let prefixNumerator : E := numerator offset
  have hshiftedQ : Function.Periodic shiftedQ period := by
    intro n
    simpa only [shiftedQ, Nat.add_assoc] using hq (offset + n)
  have hshiftedZero : Tendsto shiftedWeight atTop (nhds 0) :=
    hweightZero.comp (tendsto_add_atTop_nat offset)
  have hmassShift : Tendsto (fun cutoff => mass (cutoff + offset)) atTop atTop :=
    hmass.comp (tendsto_add_atTop_nat offset)
  have hshiftedMassEq (cutoff : ℕ) :
      shiftedMass cutoff = mass (cutoff + offset) - prefixMass := by
    simp only [shiftedMass, shiftedWeight, mass, prefixMass]
    rw [Nat.add_comm cutoff offset, Finset.sum_range_add]
    simp only [Nat.add_comm offset]
    abel
  have hshiftedMass : Tendsto shiftedMass atTop atTop := by
    have h := Filter.tendsto_atTop_add_const_right atTop (-prefixMass) hmassShift
    apply h.congr'
    filter_upwards with cutoff
    rw [hshiftedMassEq]
    simp only [sub_eq_add_neg]
  have hshiftedMean : Tendsto (fun cutoff =>
      (shiftedMass cutoff)⁻¹ • shiftedNumerator cutoff)
      atTop (nhds (periodMean q period)) := by
    have h := tendsto_periodic_weightedMean hperiod hshiftedQ hanti
      hshiftedZero hshiftedMass
    rw [periodMean_natAdd hq offset] at h
    exact h
  have hprefixMassEq (cutoff : ℕ) :
      mass (cutoff + offset) = prefixMass + shiftedMass cutoff := by
    rw [hshiftedMassEq]
    ring
  have hprefixNumeratorEq (cutoff : ℕ) :
      numerator (cutoff + offset) = prefixNumerator + shiftedNumerator cutoff := by
    simp only [numerator, prefixNumerator, shiftedNumerator, shiftedWeight, shiftedQ]
    rw [Nat.add_comm cutoff offset, Finset.sum_range_add]
    simp only [Nat.add_comm offset]
  have hinvMassShift : Tendsto (fun cutoff => (mass (cutoff + offset))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hmassShift
  have hprefixZero : Tendsto (fun cutoff =>
      (mass (cutoff + offset))⁻¹ • prefixNumerator) atTop (nhds 0) := by
    simpa using hinvMassShift.smul_const prefixNumerator
  have hratio : Tendsto (fun cutoff =>
      shiftedMass cutoff / mass (cutoff + offset)) atTop (nhds 1) := by
    have hcorrection : Tendsto (fun cutoff =>
        prefixMass * (mass (cutoff + offset))⁻¹) atTop (nhds 0) := by
      simpa using hinvMassShift.const_mul prefixMass
    have h : Tendsto (fun cutoff : ℕ =>
        (1 : ℝ) - prefixMass * (mass (cutoff + offset))⁻¹)
        atTop (nhds 1) := by simpa using tendsto_const_nhds.sub hcorrection
    apply h.congr'
    filter_upwards [hmassShift.eventually_ne_atTop 0] with cutoff hmass0
    rw [hprefixMassEq]
    have hsum0 : prefixMass + shiftedMass cutoff ≠ 0 := by
      rw [← hprefixMassEq]
      exact hmass0
    field_simp [hsum0]
    ring
  have hmain := hratio.smul hshiftedMean
  have htotal := hmain.add hprefixZero
  have hshiftedFull : Tendsto (fun cutoff =>
      (mass (cutoff + offset))⁻¹ • numerator (cutoff + offset))
      atTop (nhds (periodMean q period)) := by
    have htotal' : Tendsto (fun x =>
        (shiftedMass x / mass (x + offset)) •
            ((shiftedMass x)⁻¹ • shiftedNumerator x) +
          (mass (x + offset))⁻¹ • prefixNumerator)
        atTop (nhds (periodMean q period)) := by simpa using htotal
    apply htotal'.congr'
    filter_upwards [hshiftedMass.eventually_ne_atTop 0,
      hmassShift.eventually_ne_atTop 0] with cutoff htail0 hmass0
    rw [hprefixNumeratorEq]
    simp only [div_eq_mul_inv, smul_add]
    rw [smul_smul]
    have hcoef : shiftedMass cutoff * (mass (cutoff + offset))⁻¹ *
        (shiftedMass cutoff)⁻¹ = (mass (cutoff + offset))⁻¹ := by
      field_simp [htail0, hmass0]
    rw [hcoef]
    ac_rfl
  exact (tendsto_add_atTop_iff_nat
    (f := fun cutoff : ℕ => (mass cutoff)⁻¹ • numerator cutoff)
    offset).1 hshiftedFull

end NativeCarrySpectralWeyl.Limits
