import NativeCarrySpectralWeyl.Limits.CameraCovariance
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
# Scalar asymptotics of the logarithmic resolvent weight

For a fixed nonreal spectral parameter `z`, this file formalizes the scalar
weight from the Weyl defect-probe notes,

`w_z(n) = |z - log(n + 1)|⁻²`.

It proves positivity, decay, eventual monotonicity, divergence of the mass,
the asymptotic `A_M(z) ~ M / log(M + 1)^2`, and regular variation
`A_(L M)(z) / A_M(z) → L` for every fixed positive natural `L`.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

/-- The note's weight `|z - log n|⁻²`, indexed from zero as `n + 1`. -/
noncomputable def resolventWeight (z : ℂ) (n : ℕ) : ℝ :=
  (Complex.normSq (z - (Real.log (n + 1) : ℂ)))⁻¹

theorem resolventWeight_eq (z : ℂ) (n : ℕ) :
    resolventWeight z n =
      (((Real.log (n + 1) - z.re) ^ 2 + z.im ^ 2))⁻¹ := by
  simp only [resolventWeight, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  congr 1
  ring

theorem resolventWeight_pos {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    0 < resolventWeight z n := by
  rw [resolventWeight_eq]
  exact inv_pos.mpr (by positivity)

/-- The real resolvent denominator is negligible compared with its argument. -/
theorem tendsto_resolventDenominator_div_atTop (z : ℂ) :
    Tendsto (fun x : ℝ =>
      ((Real.log x - z.re) ^ 2 + z.im ^ 2) / x) atTop (nhds 0) := by
  have hlog2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)
  have hlog1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 (by norm_num)
  have hlinear : Tendsto (fun x : ℝ =>
      (2 * z.re) * (Real.log x / x)) atTop (nhds 0) := by
    simpa using hlog1.const_mul (2 * z.re)
  have hconstant : Tendsto (fun x : ℝ =>
      (z.re ^ 2 + z.im ^ 2) * (1 / x)) atTop (nhds 0) := by
    simpa using hinv.const_mul (z.re ^ 2 + z.im ^ 2)
  have hexpanded : Tendsto (fun x : ℝ =>
      Real.log x ^ 2 / x - (2 * z.re) * (Real.log x / x) +
        (z.re ^ 2 + z.im ^ 2) * (1 / x)) atTop (nhds 0) := by
    simpa using (hlog2.sub hlinear).add hconstant
  apply hexpanded.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  field_simp [hx]
  ring

/-- The relative one-step change of the logarithmic resolvent denominator is
`o(1/x)`.  This is the discrete slow-variation estimate needed by Stolz. -/
theorem tendsto_resolventDenominator_step (z : ℂ) :
    Tendsto (fun x : ℝ =>
      x * ((((Real.log (x + 1) - z.re) ^ 2 + z.im ^ 2) -
        ((Real.log x - z.re) ^ 2 + z.im ^ 2)) /
          ((Real.log (x + 1) - z.re) ^ 2 + z.im ^ 2)))
      atTop (nhds 0) := by
  let y : ℝ → ℝ := fun x => Real.log (x + 1) - z.re
  let delta : ℝ → ℝ := fun x => Real.log (x + 1) - Real.log x
  have hxp1 : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hy : Tendsto y atTop atTop := by
    exact Filter.tendsto_atTop_add_const_right atTop (-z.re)
      (Real.tendsto_log_atTop.comp hxp1)
  have hyInv : Tendsto (fun x => (y x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hy
  have hySq : Tendsto (fun x => (y x) ^ 2) atTop atTop := by
    simpa only [pow_two] using hy.atTop_mul_atTop₀ hy
  have hySqInv : Tendsto (fun x => ((y x) ^ 2)⁻¹) atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hySq
    convert h using 1
    rfl
  have hconstDivSq : Tendsto (fun x => z.im ^ 2 / (y x) ^ 2)
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hySqInv : Tendsto (fun x => z.im ^ 2 * ((y x) ^ 2)⁻¹)
        atTop (nhds (z.im ^ 2 * 0)))
  have hnormalizedDen : Tendsto (fun x => 1 + z.im ^ 2 / (y x) ^ 2)
      atTop (nhds 1) := by simpa using tendsto_const_nhds.add hconstDivSq
  have hyOverDen : Tendsto (fun x => y x / ((y x) ^ 2 + z.im ^ 2))
      atTop (nhds 0) := by
    have hquot := hyInv.div hnormalizedDen (by norm_num)
    have hquot' : Tendsto (fun x => (y x)⁻¹ /
        (1 + z.im ^ 2 / (y x) ^ 2)) atTop (nhds 0) := by
      convert hquot using 1
      · ext x
        rfl
      · norm_num
    apply hquot'.congr'
    filter_upwards [hy.eventually_ne_atTop 0] with x hy0
    field_simp [hy0]
  have hden : Tendsto (fun x => (y x) ^ 2 + z.im ^ 2) atTop atTop :=
    hySq.atTop_add tendsto_const_nhds
  have hdenInv : Tendsto (fun x => (((y x) ^ 2 + z.im ^ 2))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hden
  have hdelta : Tendsto delta atTop (nhds 0) :=
    Real.tendsto_log_comp_add_sub_log 1
  have hdeltaOverDen : Tendsto (fun x => delta x / ((y x) ^ 2 + z.im ^ 2))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using hdelta.mul hdenInv
  have hsecond : Tendsto (fun x =>
      (2 * y x - delta x) / ((y x) ^ 2 + z.im ^ 2)) atTop (nhds 0) := by
    have h := (hyOverDen.const_mul 2).sub hdeltaOverDen
    have h' : Tendsto (fun x =>
        2 * (y x / ((y x) ^ 2 + z.im ^ 2)) -
          delta x / ((y x) ^ 2 + z.im ^ 2)) atTop (nhds 0) := by simpa using h
    apply h'.congr'
    filter_upwards with x
    ring
  have hfirst : Tendsto (fun x : ℝ => x * delta x) atTop (nhds 1) := by
    have h := Real.tendsto_mul_log_one_add_div_atTop 1
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [delta]
    rw [← Real.log_div (by linarith : x + 1 ≠ 0) hx.ne']
    congr 2
    field_simp [hx.ne']
  have hproduct := hfirst.mul hsecond
  have hproduct' : Tendsto (fun x =>
      (x * delta x) * ((2 * y x - delta x) / ((y x) ^ 2 + z.im ^ 2)))
      atTop (nhds 0) := by simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hy.eventually_ne_atTop 0] with x hx hy0
  simp only [y, delta]
  field_simp [show (Real.log (x + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 by
    exact ne_of_gt (by positivity)]
  ring

/-- Eventually the resolvent weight dominates the shifted harmonic weight.
This coarse comparison is enough to force infinite total mass. -/
theorem eventually_one_div_nat_succ_le_resolventWeight {z : ℂ}
    (hz : z.im ≠ 0) :
    ∀ᶠ n : ℕ in atTop, (1 / ((n : ℝ) + 1)) ≤ resolventWeight z n := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ =>
      ((Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2) /
        ((n : ℝ) + 1)) atTop (nhds 0) := by
    have hcomp := (tendsto_resolventDenominator_div_atTop z).comp hcast
    convert hcomp using 1
    rfl
  filter_upwards [hratio.eventually (Iio_mem_nhds zero_lt_one)] with n hn
  rw [resolventWeight_eq]
  have hx : 0 < (n : ℝ) + 1 := by positivity
  have hdenPos : 0 <
      (Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2 := by
    positivity
  have hdenLe :
      (Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2 ≤ (n : ℝ) + 1 :=
    (div_le_one hx).mp hn.le
  simpa only [one_div, Nat.cast_add, Nat.cast_one] using inv_anti₀ hdenPos hdenLe

theorem tendsto_resolventWeight_zero (z : ℂ) :
    Tendsto (resolventWeight z) atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hshift : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) - z.re)
      atTop atTop := by
    simpa only [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right atTop (-z.re) hlog
  have hsq : Tendsto (fun n : ℕ =>
      (Real.log ((n : ℝ) + 1) - z.re) ^ 2) atTop atTop :=
    by simpa only [pow_two] using hshift.atTop_mul_atTop₀ hshift
  have hden : Tendsto (fun n : ℕ =>
      (Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2) atTop atTop :=
    hsq.atTop_add tendsto_const_nhds
  have hinv := tendsto_inv_atTop_zero.comp hden
  rw [show resolventWeight z = fun n : ℕ =>
      (((Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2))⁻¹ by
    funext n
    simpa only [Nat.cast_add, Nat.cast_one] using resolventWeight_eq z n]
  convert hinv using 1
  rfl

theorem exists_resolventWeight_antitone_natAdd {z : ℂ} (hz : z.im ≠ 0) :
    ∃ offset : ℕ, Antitone (fun n : ℕ => resolventWeight z (offset + n)) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  obtain ⟨offset, hoffset⟩ := eventually_atTop.1 (hlog.eventually_ge_atTop z.re)
  refine ⟨offset, ?_⟩
  intro m n hmn
  change resolventWeight z (offset + n) ≤ resolventWeight z (offset + m)
  rw [resolventWeight_eq, resolventWeight_eq]
  have hindexNat : offset + m + 1 ≤ offset + n + 1 :=
    Nat.add_le_add_right (Nat.add_le_add_left hmn offset) 1
  have hindex : ((offset + m + 1 : ℕ) : ℝ) ≤
      ((offset + n + 1 : ℕ) : ℝ) := by exact_mod_cast hindexNat
  have hlogMono : Real.log (((offset + m + 1 : ℕ) : ℝ)) ≤
      Real.log (((offset + n + 1 : ℕ) : ℝ)) := by
    exact Real.strictMonoOn_log.monotoneOn (by exact Set.mem_Ioi.mpr (by positivity))
      (by exact Set.mem_Ioi.mpr (by positivity)) hindex
  have hleft : z.re ≤ Real.log (((offset + m + 1 : ℕ) : ℝ)) := by
    have h := hoffset (offset + m) (Nat.le_add_right offset m)
    rw [show ((offset + m : ℕ) : ℝ) + 1 =
        ((offset + m + 1 : ℕ) : ℝ) by norm_num [Nat.cast_add]] at h
    exact h
  have hsquare :
      (Real.log (((offset + m + 1 : ℕ) : ℝ)) - z.re) ^ 2 ≤
        (Real.log (((offset + n + 1 : ℕ) : ℝ)) - z.re) ^ 2 := by
    nlinarith
  have hden :
      (Real.log (((offset + m + 1 : ℕ) : ℝ)) - z.re) ^ 2 + z.im ^ 2 ≤
        (Real.log (((offset + n + 1 : ℕ) : ℝ)) - z.re) ^ 2 + z.im ^ 2 := by
    linarith
  apply inv_anti₀ (by positivity)
  simpa only [Nat.cast_add, Nat.cast_one] using hden

/-- Resolvent mass through the positive integers `1, ..., cutoff`. -/
noncomputable def resolventMass (z : ℂ) (cutoff : ℕ) : ℝ :=
  ∑ n ∈ Finset.range cutoff, resolventWeight z n

/-- For nonreal spectral parameter, the resolvent weight is not summable. -/
theorem not_summable_resolventWeight {z : ℂ} (hz : z.im ≠ 0) :
    ¬ Summable (resolventWeight z) := by
  obtain ⟨offset, hoffset⟩ :=
    eventually_atTop.1 (eventually_one_div_nat_succ_le_resolventWeight hz)
  have hharmonicNot : ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ => by positivity)).2
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  intro hweight
  have hweightShift : Summable (fun n : ℕ => resolventWeight z (n + offset)) :=
    (summable_nat_add_iff offset).2 hweight
  have hharmonicShift : Summable (fun n : ℕ =>
      1 / (((n + offset : ℕ) : ℝ) + 1)) := by
    apply hweightShift.of_nonneg_of_le (fun _ => by positivity)
    intro n
    exact hoffset (n + offset) (by omega)
  apply hharmonicNot
  exact (summable_nat_add_iff offset).1 hharmonicShift

/-- The concrete resolvent mass diverges to `+∞`. -/
theorem tendsto_resolventMass_atTop {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (resolventMass z) atTop atTop := by
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => (resolventWeight_pos hz n).le)).1 (not_summable_resolventWeight hz)

/-- The endpoint scale `M w_z(M + 1)` associated with the resolvent mass. -/
noncomputable def resolventScale (z : ℂ) (cutoff : ℕ) : ℝ :=
  (cutoff : ℝ) * resolventWeight z cutoff

/-- The endpoint scale diverges; equivalently, the logarithmic denominator is
`o(M)`. -/
theorem tendsto_resolventScale_atTop {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (resolventScale z) atTop atTop := by
  let ratio : ℕ → ℝ := fun n =>
    ((Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2) / ((n : ℝ) + 1)
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hratio : Tendsto ratio atTop (nhds 0) := by
    have h := (tendsto_resolventDenominator_div_atTop z).comp hcast
    convert h using 1
    rfl
  have hratioPos : ∀ᶠ n in atTop, ratio n ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards with n
    simp only [Set.mem_Ioi, ratio]
    exact div_pos (by positivity) (by positivity)
  have hratioGT : Tendsto ratio atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hratio, hratioPos⟩
  have hinv : Tendsto ratio⁻¹ atTop atTop := hratioGT.inv_tendsto_nhdsGT_zero
  have hfactor : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1))
      atTop (nhds 1) := tendsto_natCast_div_add_atTop 1
  have hproduct := hinv.atTop_mul_pos zero_lt_one hfactor
  apply hproduct.congr'
  filter_upwards with n
  rw [resolventScale, resolventWeight_eq]
  simp only [ratio, Pi.inv_apply]
  have hx : (n : ℝ) + 1 ≠ 0 := by positivity
  have hden : (Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  field_simp [hx, hden]

/-- The increment of `M w_z(M + 1)` is asymptotic to the resolvent weight.
This is the discrete slow-variation statement behind the mass asymptotic. -/
theorem tendsto_resolventScale_increment_div_weight {z : ℂ}
    (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ =>
      (resolventScale z (n + 1) - resolventScale z n) /
        resolventWeight z n) atTop (nhds 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hstep := (tendsto_resolventDenominator_step z).comp hcast
  have hlimit : Tendsto (fun n : ℕ => 1 -
      ((n : ℝ) + 1) *
        ((((Real.log (((n : ℝ) + 1) + 1) - z.re) ^ 2 + z.im ^ 2) -
          ((Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2)) /
            ((Real.log (((n : ℝ) + 1) + 1) - z.re) ^ 2 + z.im ^ 2))
      ) atTop (nhds 1) := by
    have hstep' : Tendsto (fun n : ℕ =>
        ((n : ℝ) + 1) *
          ((((Real.log (((n : ℝ) + 1) + 1) - z.re) ^ 2 + z.im ^ 2) -
            ((Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2)) /
              ((Real.log (((n : ℝ) + 1) + 1) - z.re) ^ 2 + z.im ^ 2))
        ) atTop (nhds 0) := by
      change Tendsto (fun n : ℕ =>
        ((n : ℝ) + 1) *
          ((((Real.log (((n : ℝ) + 1) + 1) - z.re) ^ 2 + z.im ^ 2) -
            ((Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2)) /
              ((Real.log (((n : ℝ) + 1) + 1) - z.re) ^ 2 + z.im ^ 2))
        ) atTop (nhds 0) at hstep
      exact hstep
    simpa using tendsto_const_nhds.sub hstep'
  apply hlimit.congr'
  filter_upwards with n
  simp only [resolventScale, resolventWeight_eq, Nat.cast_add, Nat.cast_one]
  have hden0 : (Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  have hden1 : (Real.log (((n : ℝ) + 1) + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  field_simp [hden0, hden1]
  ring

/-- The resolvent mass is asymptotic to its endpoint scale:
`A_M(z) ~ M w_z(M + 1)`. -/
theorem tendsto_resolventMass_div_scale_one {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventMass z cutoff / resolventScale z cutoff) atTop (nhds 1) := by
  let increment : ℕ → ℝ := fun n =>
    resolventScale z (n + 1) - resolventScale z n
  have hratio : Tendsto (fun n => increment n / resolventWeight z n)
      atTop (nhds 1) := tendsto_resolventScale_increment_div_weight hz
  have hweightNe : ∀ᶠ n : ℕ in atTop, resolventWeight z n ≠ 0 :=
    Filter.Eventually.of_forall fun n => ne_of_gt (resolventWeight_pos hz n)
  have hincrementEquivWeight :
      Asymptotics.IsEquivalent atTop increment (resolventWeight z) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hweightNe).2 hratio
  have herror : (fun n => resolventWeight z n - increment n) =o[atTop] increment :=
    hincrementEquivWeight.symm.isLittleO
  have hincrementPosEv : ∀ᶠ n : ℕ in atTop, 0 < increment n := by
    filter_upwards [hratio.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    have hw := resolventWeight_pos hz n
    rcases (div_pos_iff.mp hn) with h | h
    · exact h.1
    · linarith
  obtain ⟨offset, hincrementPos⟩ := eventually_atTop.1 hincrementPosEv
  let shiftedIncrement : ℕ → ℝ := fun n => increment (n + offset)
  let shiftedWeight : ℕ → ℝ := fun n => resolventWeight z (n + offset)
  have herrorShift : (fun n => shiftedWeight n - shiftedIncrement n) =o[atTop]
      shiftedIncrement := by
    have h := herror.comp_tendsto (tendsto_add_atTop_nat offset)
    convert h using 1 <;> ext n <;> rfl
  have hshiftedIncrementNonneg : 0 ≤ shiftedIncrement := by
    intro n
    exact (hincrementPos (n + offset) (by omega)).le
  have hscaleShift : Tendsto (fun n : ℕ => resolventScale z (n + offset))
      atTop atTop :=
    (tendsto_resolventScale_atTop hz).comp (tendsto_add_atTop_nat offset)
  have hsumIncrement : Tendsto (fun cutoff : ℕ =>
      ∑ n ∈ Finset.range cutoff, shiftedIncrement n) atTop atTop := by
    have hsub := Filter.tendsto_atTop_add_const_right atTop
      (-resolventScale z offset) hscaleShift
    apply hsub.congr'
    filter_upwards with cutoff
    simp only [shiftedIncrement, increment]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.zero_add,
      Nat.add_zero, sub_eq_add_neg] using
      (Finset.sum_range_sub (fun n => resolventScale z (n + offset)) cutoff).symm
  have hsumError := herrorShift.sum_range hshiftedIncrementNonneg hsumIncrement
  have htailEquivSumIncrement : Asymptotics.IsEquivalent atTop
      (fun cutoff => ∑ n ∈ Finset.range cutoff, shiftedWeight n)
      (fun cutoff => ∑ n ∈ Finset.range cutoff, shiftedIncrement n) := by
    rw [Asymptotics.IsEquivalent]
    change (fun cutoff =>
      (∑ n ∈ Finset.range cutoff, shiftedWeight n) -
        ∑ n ∈ Finset.range cutoff, shiftedIncrement n) =o[atTop]
          (fun cutoff => ∑ n ∈ Finset.range cutoff, shiftedIncrement n)
    simpa only [Finset.sum_sub_distrib] using hsumError
  have htailEquivScaleSub : Asymptotics.IsEquivalent atTop
      (fun cutoff => ∑ n ∈ Finset.range cutoff, shiftedWeight n)
      (fun cutoff => resolventScale z (cutoff + offset) - resolventScale z offset) := by
    apply htailEquivSumIncrement.congr_right
    filter_upwards with cutoff
    simp only [shiftedIncrement, increment]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.zero_add,
      Nat.add_zero] using
      Finset.sum_range_sub (fun n => resolventScale z (n + offset)) cutoff
  have hscaleNorm : Tendsto (norm ∘ fun n : ℕ => resolventScale z (n + offset))
      atTop atTop := tendsto_norm_atTop_atTop.comp hscaleShift
  have hscaleSubEquiv : Asymptotics.IsEquivalent atTop
      (fun cutoff => resolventScale z (cutoff + offset) - resolventScale z offset)
      (fun cutoff => resolventScale z (cutoff + offset)) := by
    simpa only [sub_eq_add_neg] using
      (Asymptotics.IsEquivalent.refl.add_const_of_norm_tendsto_atTop
        (c := -resolventScale z offset) hscaleNorm)
  have htailEquivScale := htailEquivScaleSub.trans hscaleSubEquiv
  have hfullShiftEquiv : Asymptotics.IsEquivalent atTop
      (fun cutoff => resolventMass z (cutoff + offset))
      (fun cutoff => resolventScale z (cutoff + offset)) := by
    have hadd := htailEquivScale.const_add_of_norm_tendsto_atTop hscaleNorm
      (c := resolventMass z offset)
    apply hadd.congr_left
    filter_upwards with cutoff
    simp only [resolventMass, shiftedWeight]
    rw [Nat.add_comm cutoff offset, Finset.sum_range_add]
    simp only [Nat.add_comm]
  have hscaleNe : ∀ᶠ cutoff : ℕ in atTop,
      resolventScale z (cutoff + offset) ≠ 0 :=
    hscaleShift.eventually_ne_atTop 0
  have hshiftRatio : Tendsto (fun cutoff : ℕ =>
      resolventMass z (cutoff + offset) / resolventScale z (cutoff + offset))
      atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hscaleNe).1 hfullShiftEquiv
  exact (tendsto_add_atTop_iff_nat
    (f := fun cutoff : ℕ => resolventMass z cutoff / resolventScale z cutoff)
    offset).1 hshiftRatio

/-- The resolvent denominator is asymptotic to `log(x)^2`. -/
theorem tendsto_resolventDenominator_div_log_sq (z : ℂ) :
    Tendsto (fun x : ℝ =>
      ((Real.log x - z.re) ^ 2 + z.im ^ 2) / Real.log x ^ 2)
      atTop (nhds 1) := by
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hlogInv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hlogSq : Tendsto (fun x : ℝ => Real.log x ^ 2) atTop atTop := by
    simpa only [pow_two] using hlog.atTop_mul_atTop₀ hlog
  have hlogSqInv : Tendsto (fun x : ℝ => (Real.log x ^ 2)⁻¹)
      atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hlogSq
    convert h using 1
    rfl
  have hexpanded : Tendsto (fun x : ℝ =>
      1 - (2 * z.re) * (Real.log x)⁻¹ +
        (z.re ^ 2 + z.im ^ 2) * (Real.log x ^ 2)⁻¹)
      atTop (nhds 1) := by
    have hlinear : Tendsto (fun x : ℝ => (2 * z.re) * (Real.log x)⁻¹)
        atTop (nhds 0) := by simpa using hlogInv.const_mul (2 * z.re)
    have hconstant : Tendsto (fun x : ℝ =>
        (z.re ^ 2 + z.im ^ 2) * (Real.log x ^ 2)⁻¹)
        atTop (nhds 0) := by
      simpa using hlogSqInv.const_mul (z.re ^ 2 + z.im ^ 2)
    simpa using (tendsto_const_nhds.sub hlinear).add hconstant
  apply hexpanded.congr'
  filter_upwards [hlog.eventually_ne_atTop 0] with x hlog0
  field_simp [hlog0]
  ring

/-- A fixed positive natural dilation does not change the resolvent weight
asymptotically. -/
theorem tendsto_resolventWeight_nat_mul_div {z : ℂ} (hz : z.im ≠ 0)
    {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventWeight z (scale * cutoff) / resolventWeight z cutoff)
      atTop (nhds 1) := by
  let base : ℕ → ℝ := fun n => (n : ℝ) + 1
  let dilated : ℕ → ℝ := fun n => (scale * n : ℕ) + 1
  have hbase : Tendsto base atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hdilatedNat : Tendsto (fun n : ℕ => scale * n) atTop atTop :=
    tendsto_nat_const_mul_atTop hscale
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
    have h := tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 1 scale
      (d := 1) (by norm_num)
    convert h using 1
    · ext n
      simp only [base, dilated, Nat.cast_mul]
      ring
    · norm_num
  have hlogDifference : Tendsto (fun n : ℕ =>
      Real.log (dilated n) - Real.log (base n)) atTop (nhds (Real.log scale)) := by
    have hlogRatio := (Real.continuousAt_log (Nat.cast_ne_zero.mpr hscale.ne')).tendsto.comp
      hlinearRatio
    apply hlogRatio.congr'
    filter_upwards with n
    change Real.log (dilated n / base n) =
      Real.log (dilated n) - Real.log (base n)
    rw [Real.log_div (by positivity : dilated n ≠ 0) (by positivity : base n ≠ 0)]
  have hbaseLog : Tendsto (fun n => Real.log (base n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hbase
  have hbaseLogInv : Tendsto (fun n => (Real.log (base n))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hbaseLog
  have hlogRatio : Tendsto (fun n : ℕ =>
      Real.log (dilated n) / Real.log (base n)) atTop (nhds 1) := by
    have hcorrection := hlogDifference.mul hbaseLogInv
    have honeAdd : Tendsto (fun n : ℕ => 1 +
        (Real.log (dilated n) - Real.log (base n)) *
          (Real.log (base n))⁻¹) atTop (nhds 1) := by simpa using tendsto_const_nhds.add hcorrection
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
      (Real.tendsto_log_atTop.comp hdilated).eventually_ne_atTop 0] with n hb hd
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
  simp only [resolventWeight_eq, base, dilated, Nat.cast_mul]
  have hbaseDen0 : (Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  have hdilatedDen0 : (Real.log ((scale : ℝ) * n + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  field_simp [hbaseDen0, hdilatedDen0]

/-- Fixed natural dilation multiplies the endpoint scale by that dilation. -/
theorem tendsto_resolventScale_nat_mul_div {z : ℂ} (hz : z.im ≠ 0)
    {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventScale z (scale * cutoff) / resolventScale z cutoff)
      atTop (nhds (scale : ℝ)) := by
  have hweight := tendsto_resolventWeight_nat_mul_div hz hscale
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (scale : ℝ) *
        (resolventWeight z (scale * cutoff) / resolventWeight z cutoff))
      atTop (nhds (scale : ℝ)) := by simpa using hweight.const_mul (scale : ℝ)
  apply hlimit.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with cutoff hcutoff
  simp only [resolventScale, Nat.cast_mul]
  have hcutoff0 : (cutoff : ℝ) ≠ 0 := by positivity
  have hweight0 : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hcutoff0, hweight0]

/-- The concrete resolvent mass is regularly varying with index one. -/
theorem tendsto_resolventMass_nat_mul_div {z : ℂ} (hz : z.im ≠ 0)
    {scale : ℕ} (hscale : 0 < scale) :
    Tendsto (fun cutoff : ℕ =>
      resolventMass z (scale * cutoff) / resolventMass z cutoff)
      atTop (nhds (scale : ℝ)) := by
  have hcutoffScale := tendsto_nat_const_mul_atTop hscale
  have hmassScale := (tendsto_resolventMass_div_scale_one hz).comp hcutoffScale
  have hscaleRatio := tendsto_resolventScale_nat_mul_div hz hscale
  have hmassBaseInv : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff / resolventScale z cutoff)⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_resolventMass_div_scale_one hz).inv₀ (by norm_num)
  have hproduct := (hmassScale.mul hscaleRatio).mul hmassBaseInv
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventMass z (scale * cutoff) / resolventScale z (scale * cutoff)) *
        (resolventScale z (scale * cutoff) / resolventScale z cutoff) *
          (resolventMass z cutoff / resolventScale z cutoff)⁻¹)
      atTop (nhds (scale : ℝ)) := by simpa using hproduct
  apply hlimit.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with cutoff hcutoff
  have hmass0 : resolventMass z cutoff ≠ 0 := by
    rw [resolventMass]
    exact ne_of_gt (Finset.sum_pos' (fun n _ => (resolventWeight_pos hz n).le)
      ⟨0, Finset.mem_range.mpr (by omega), resolventWeight_pos hz 0⟩)
  have hscale0 : resolventScale z cutoff ≠ 0 := by
    rw [resolventScale]
    exact mul_ne_zero (by positivity) (ne_of_gt (resolventWeight_pos hz cutoff))
  have hscaledScale0 : resolventScale z (scale * cutoff) ≠ 0 := by
    rw [resolventScale]
    exact mul_ne_zero (by positivity) (ne_of_gt (resolventWeight_pos hz (scale * cutoff)))
  field_simp [hmass0, hscale0, hscaledScale0]

/-- The note's concrete resolvent weight satisfies the exact scalar
regular-variation hypothesis used by the cutoff covariance theorem. -/
theorem resolventWeight_hasAsymptoticallyLinearMass {z : ℂ} (hz : z.im ≠ 0) :
    HasAsymptoticallyLinearMass (resolventWeight z) := by
  intro scale hscale
  simpa only [resolventMass, div_eq_inv_mul, mul_comm] using
    tendsto_resolventMass_nat_mul_div hz hscale

/-- Pointwise logarithmic asymptotic of the concrete resolvent weight. -/
theorem tendsto_resolventWeight_mul_log_sq_one {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ =>
      resolventWeight z n * Real.log ((n : ℝ) + 1) ^ 2)
      atTop (nhds 1) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hden := (tendsto_resolventDenominator_div_log_sq z).comp hcast
  have hinv := hden.inv₀ (by norm_num)
  have hinv' : Tendsto (fun n : ℕ =>
      ((((Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2) /
        Real.log ((n : ℝ) + 1) ^ 2))⁻¹) atTop (nhds 1) := by
    simpa using hinv
  apply hinv'.congr'
  filter_upwards with n
  rw [resolventWeight_eq]
  have hden0 : (Real.log ((n : ℝ) + 1) - z.re) ^ 2 + z.im ^ 2 ≠ 0 :=
    ne_of_gt (by positivity)
  field_simp [hden0]

/-- The documented scalar asymptotic
`A_M(z) ~ M / log(M + 1)^2`. -/
theorem tendsto_resolventMass_div_nat_div_log_sq_one {z : ℂ}
    (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventMass z cutoff /
        ((cutoff : ℝ) / Real.log ((cutoff : ℝ) + 1) ^ 2))
      atTop (nhds 1) := by
  have hmassScale := tendsto_resolventMass_div_scale_one hz
  have hweightLog := tendsto_resolventWeight_mul_log_sq_one hz
  have hproduct := hmassScale.mul hweightLog
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff / resolventScale z cutoff) *
        (resolventWeight z cutoff * Real.log ((cutoff : ℝ) + 1) ^ 2))
      atTop (nhds 1) := by simpa using hproduct
  apply hlimit.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h => h⟩] with cutoff hcutoff
  rw [resolventScale]
  have hcutoff0 : (cutoff : ℝ) ≠ 0 := by positivity
  have hweight0 : resolventWeight z cutoff ≠ 0 :=
    ne_of_gt (resolventWeight_pos hz cutoff)
  field_simp [hcutoff0, hweight0]

/-- The genuine scaled camera covariance for the concrete resolvent weight
converges to the periodic Gram matrix. -/
theorem tendsto_resolvent_scaledCutoffCameraCovariance
    {ι : Type*} [Fintype ι] {period : ℕ} {camera : ι → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      scaledCutoffCameraCovariance (resolventWeight z) cutoff camera)
      atTop (nhds (periodicGramMatrix period camera)) := by
  obtain ⟨offset, hanti⟩ := exists_resolventWeight_antitone_natAdd hz
  apply tendsto_scaledCutoffCameraCovariance_of_eventually_antitone
    hperiod hcamera hcommon ⟨offset, ?_⟩ (tendsto_resolventWeight_zero z)
      (by
        change Tendsto (resolventMass z) atTop atTop
        exact tendsto_resolventMass_atTop hz)
      (resolventWeight_hasAsymptoticallyLinearMass hz)
  simpa only [Nat.add_comm] using hanti

/-- Uniform finite-matrix norm convergence for the concrete resolvent
covariance. -/
theorem tendsto_norm_resolvent_scaledCutoffCameraCovariance_sub
    {ι : Type*} [Fintype ι] {period : ℕ} {camera : ι → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖scaledCutoffCameraCovariance (resolventWeight z) cutoff camera -
        periodicGramMatrix period camera‖) atTop (nhds 0) := by
  obtain ⟨offset, hanti⟩ := exists_resolventWeight_antitone_natAdd hz
  apply tendsto_norm_scaledCutoffCameraCovariance_sub_of_eventually_antitone
    hperiod hcamera hcommon ⟨offset, ?_⟩ (tendsto_resolventWeight_zero z)
      (by
        change Tendsto (resolventMass z) atTop atTop
        exact tendsto_resolventMass_atTop hz)
      (resolventWeight_hasAsymptoticallyLinearMass hz)
  simpa only [Nat.add_comm] using hanti

/-- The concrete resolvent covariance of cameras `2, ..., 7` converges to the
exact documented six-camera Gram matrix. -/
theorem tendsto_sixCamera_resolvent_scaledCutoffCovariance {z : ℂ}
    (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      scaledCutoffCameraCovariance (resolventWeight z) cutoff sixCamera)
      atTop (nhds sixCameraGram) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [sixCameraGram_eq] using
    (tendsto_resolvent_scaledCutoffCameraCovariance
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Uniform matrix-norm convergence for the exact six-camera resolvent
covariance package. -/
theorem tendsto_norm_sixCamera_resolvent_scaledCutoffCovariance_sub {z : ℂ}
    (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖scaledCutoffCameraCovariance (resolventWeight z) cutoff sixCamera -
        sixCameraGram‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [sixCameraGram_eq] using
    (tendsto_norm_resolvent_scaledCutoffCameraCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

end NativeCarrySpectralWeyl.Limits
