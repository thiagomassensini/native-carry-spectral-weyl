import NativeCarrySpectralWeyl.Camera.CommonZeroSet
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Quantitative native-line cutoff tails

This module turns the centered-second-difference majorant into the explicit
`cutoff⁻³ᐟ²` remainder stated in the source notes.  The cutoff is the literal
number of aligned center blocks used by `finiteBracketCharacteristic`.

The estimates here are scalar and pointwise in the native-line parameter.  A
later derivative module adds the logarithmic losses caused by differentiation.
-/

open scoped BigOperators
open Set
open Filter

namespace NativeCarrySpectralWeyl.Camera

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The universal `m⁻⁵ᐟ²` block weight on the native line. -/
def nativeTailWeight (index : ℕ) : ℝ :=
  (((index + 1 : ℕ) : ℝ) ^ (-(5 : ℝ) / 2))

/-- The sum of the squared radii emitted by one camera center. -/
def cameraRadiusSqSum (camera : ℕ) : ℝ :=
  if camera = 2 then 1
  else ∑ radius ∈ radiusSet camera, (radius : ℝ) ^ 2

/-- Explicit pointwise coefficient in the native-line tail estimate. -/
def nativeTailConstant (camera : ℕ) (t : ℝ) : ℝ :=
  ‖nativeLine t * (nativeLine t + 1)‖ * cameraRadiusSqSum camera

theorem cameraRadiusSqSum_nonneg (camera : ℕ) :
    0 ≤ cameraRadiusSqSum camera := by
  unfold cameraRadiusSqSum
  split_ifs
  · norm_num
  · positivity

theorem nativeTailConstant_nonneg (camera : ℕ) (t : ℝ) :
    0 ≤ nativeTailConstant camera t := by
  exact mul_nonneg (norm_nonneg _) (cameraRadiusSqSum_nonneg camera)

/-- The compact-normal majorant specializes exactly to the native-line
`m⁻⁵ᐟ²` weight. -/
theorem centerBracketMajorant_nativeLine_eq (camera index : ℕ) (t : ℝ) :
    centerBracketMajorant camera (1 / 2 : ℝ)
        ‖nativeLine t * (nativeLine t + 1)‖ index =
      nativeTailConstant camera t * nativeTailWeight index := by
  have hexponent : -(1 / 2 : ℝ) - 2 = -(5 : ℝ) / 2 := by norm_num
  unfold centerBracketMajorant nativeTailConstant cameraRadiusSqSum
    radiusBracketMajorant nativeTailWeight
  by_cases h2 : camera = 2
  · subst camera
    simp only [if_pos]
    rw [hexponent]
    ring
  · simp only [h2, if_false]
    rw [hexponent]
    rw [← Finset.mul_sum]
    ring

/-- Every native-line center block has the explicit `m⁻⁵ᐟ²` bound. -/
theorem centerBracketTerm_norm_le_nativeTail {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) (index : ℕ) :
    ‖centerBracketTerm camera (nativeLine t) index‖ ≤
      nativeTailConstant camera t * nativeTailWeight index := by
  rw [← centerBracketMajorant_nativeLine_eq]
  apply centerBracketTerm_norm_le_majorant hcamera
  · rw [nativeLine_re]
  · exact le_rfl
  · norm_num

theorem nativeTailWeight_summable : Summable nativeTailWeight := by
  have hbase : Summable
      (fun index : ℕ => (((index + 1 : ℕ) : ℝ) ^ (-(5 : ℝ) / 2))) := by
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  change Summable
    (fun index : ℕ => (((index + 1 : ℕ) : ℝ) ^ (-(5 : ℝ) / 2)))
  exact hbase

/-- Integral-test tail bound producing the exact exponent drop
`5/2 ↦ 3/2`. -/
theorem nativeTailWeight_tsum_nat_add_le {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) :
    (∑' index : ℕ, nativeTailWeight (index + cutoff)) ≤
      (2 / 3 : ℝ) * (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  let f : ℝ → ℝ := fun x => x ^ (-(5 : ℝ) / 2)
  have hcutoffPos : (0 : ℝ) < cutoff := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hcutoff)
  have hanti : AntitoneOn f (Ici (cutoff : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
    intro x hx
    exact hcutoffPos.trans_le hx
  have hint : MeasureTheory.IntegrableOn f (Ioi (cutoff : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hcutoffPos
  have hnonneg : ∀ x ∈ Ioi (cutoff : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg (hcutoffPos.trans hx).le _
  have h := hanti.tsum_comp_add_le_integral cutoff hint hnonneg
  rw [integral_Ioi_rpow_of_lt (by norm_num) hcutoffPos] at h
  norm_num at h
  calc
    (∑' index : ℕ, nativeTailWeight (index + cutoff)) =
        ∑' index : ℕ, f ((index : ℝ) + cutoff + 1) := by
      apply tsum_congr
      intro index
      simp only [nativeTailWeight, f, Nat.cast_add, Nat.cast_one]
    _ ≤ (cutoff : ℝ) ^ (-(3 : ℝ) / 2) / (3 / 2 : ℝ) := by
      convert h using 1
      all_goals norm_num
    _ = (2 / 3 : ℝ) * (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by ring

/-- The infinite-minus-finite characteristic is literally the shifted center
block tail. -/
theorem bracketCharacteristic_sub_finite_eq_tsum_nat_add {camera cutoff : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    bracketCharacteristic camera (nativeLine t) -
        finiteBracketCharacteristic camera cutoff (nativeLine t) =
      ∑' index : ℕ,
        centerBracketTerm camera (nativeLine t) (index + cutoff) := by
  have hsum := centerBracketTerm_summable hcamera (s := nativeLine t) (by
    rw [nativeLine_re]
    norm_num)
  have hsplit := hsum.sum_add_tsum_nat_add cutoff
  unfold bracketCharacteristic finiteBracketCharacteristic
  rw [← hsplit]
  ring

/-- Explicit `O(cutoff⁻³ᐟ²)` error bound for one supported camera on the native
line. -/
theorem bracketCharacteristic_nativeLine_tail_le {camera cutoff : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : 1 ≤ cutoff) (t : ℝ) :
    ‖bracketCharacteristic camera (nativeLine t) -
        finiteBracketCharacteristic camera cutoff (nativeLine t)‖ ≤
      ((2 / 3 : ℝ) * nativeTailConstant camera t) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  rw [bracketCharacteristic_sub_finite_eq_tsum_nat_add hcamera]
  have hshiftInjective : Function.Injective (fun index : ℕ => index + cutoff) := by
    intro left right h
    exact Nat.add_right_cancel h
  have hnormSummable : Summable (fun index : ℕ =>
      ‖centerBracketTerm camera (nativeLine t) (index + cutoff)‖) :=
    (centerBracketTerm_norm_summable hcamera (by
      rw [nativeLine_re]
      norm_num)).comp_injective hshiftInjective
  calc
    ‖∑' index : ℕ, centerBracketTerm camera (nativeLine t) (index + cutoff)‖ ≤
        ∑' index : ℕ, ‖centerBracketTerm camera (nativeLine t) (index + cutoff)‖ :=
      norm_tsum_le_tsum_norm hnormSummable
    _ ≤ ∑' index : ℕ,
        nativeTailConstant camera t * nativeTailWeight (index + cutoff) := by
      exact Summable.tsum_le_tsum
        (fun index => centerBracketTerm_norm_le_nativeTail hcamera t (index + cutoff))
        hnormSummable
        ((nativeTailWeight_summable.comp_injective hshiftInjective).mul_left _)
    _ = nativeTailConstant camera t *
        ∑' index : ℕ, nativeTailWeight (index + cutoff) := by
      rw [tsum_mul_left]
    _ ≤ nativeTailConstant camera t *
        ((2 / 3 : ℝ) * (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (nativeTailWeight_tsum_nat_add_le hcutoff)
        (nativeTailConstant_nonneg camera t)
    _ = ((2 / 3 : ℝ) * nativeTailConstant camera t) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by ring

/-- Asymptotic form of the explicit native-line tail theorem. -/
theorem bracketCharacteristic_nativeLine_tail_isBigO {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    (fun cutoff : ℕ => bracketCharacteristic camera (nativeLine t) -
        finiteBracketCharacteristic camera cutoff (nativeLine t)) =O[atTop]
      (fun cutoff : ℕ => (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) := by
  apply Asymptotics.IsBigO.of_bound ((2 / 3 : ℝ) * nativeTailConstant camera t)
  filter_upwards [eventually_ge_atTop 1] with cutoff hcutoff
  have htail := bracketCharacteristic_nativeLine_tail_le hcamera hcutoff t
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg cutoff) _)] using htail

/-- Quantitative finite-cutoff cross-factor residual.  This is the numerically
stable form of the camera factorization because it never divides by the native
scalar near a zero. -/
theorem finiteBracketCharacteristic_cross_tail_le {camera cutoff : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : 1 ≤ cutoff) (t : ℝ) :
    ‖factor 3 (nativeLine t) *
          finiteBracketCharacteristic camera cutoff (nativeLine t) -
        factor camera (nativeLine t) *
          finiteBracketCharacteristic 3 cutoff (nativeLine t)‖ ≤
      ((2 / 3 : ℝ) *
        (‖factor camera (nativeLine t)‖ * nativeTailConstant 3 t +
          ‖factor 3 (nativeLine t)‖ * nativeTailConstant camera t)) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  have hdomain : nativeLine t ∈ bracketDomain := by
    simp [bracketDomain]
    norm_num
  have hcross := bracketCharacteristic_cross_eq hcamera hdomain
  have hrearrange :
      factor 3 (nativeLine t) *
            finiteBracketCharacteristic camera cutoff (nativeLine t) -
          factor camera (nativeLine t) *
            finiteBracketCharacteristic 3 cutoff (nativeLine t) =
        factor camera (nativeLine t) *
            (bracketCharacteristic 3 (nativeLine t) -
              finiteBracketCharacteristic 3 cutoff (nativeLine t)) -
          factor 3 (nativeLine t) *
            (bracketCharacteristic camera (nativeLine t) -
              finiteBracketCharacteristic camera cutoff (nativeLine t)) := by
    linear_combination hcross
  rw [hrearrange]
  calc
    ‖factor camera (nativeLine t) *
          (bracketCharacteristic 3 (nativeLine t) -
            finiteBracketCharacteristic 3 cutoff (nativeLine t)) -
        factor 3 (nativeLine t) *
          (bracketCharacteristic camera (nativeLine t) -
            finiteBracketCharacteristic camera cutoff (nativeLine t))‖ ≤
      ‖factor camera (nativeLine t)‖ *
          ‖bracketCharacteristic 3 (nativeLine t) -
            finiteBracketCharacteristic 3 cutoff (nativeLine t)‖ +
        ‖factor 3 (nativeLine t)‖ *
          ‖bracketCharacteristic camera (nativeLine t) -
            finiteBracketCharacteristic camera cutoff (nativeLine t)‖ := by
      simpa only [norm_mul] using norm_sub_le
        (factor camera (nativeLine t) *
          (bracketCharacteristic 3 (nativeLine t) -
            finiteBracketCharacteristic 3 cutoff (nativeLine t)))
        (factor 3 (nativeLine t) *
          (bracketCharacteristic camera (nativeLine t) -
            finiteBracketCharacteristic camera cutoff (nativeLine t)))
    _ ≤ ‖factor camera (nativeLine t)‖ *
          (((2 / 3 : ℝ) * nativeTailConstant 3 t) *
            (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) +
        ‖factor 3 (nativeLine t)‖ *
          (((2 / 3 : ℝ) * nativeTailConstant camera t) *
            (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) := by
      gcongr
      · exact bracketCharacteristic_nativeLine_tail_le (by omega : 2 ≤ 3) hcutoff t
      · exact bracketCharacteristic_nativeLine_tail_le hcamera hcutoff t
    _ = ((2 / 3 : ℝ) *
        (‖factor camera (nativeLine t)‖ * nativeTailConstant 3 t +
          ‖factor 3 (nativeLine t)‖ * nativeTailConstant camera t)) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by ring

/-- The stable finite-camera cross residual is `O(cutoff⁻³ᐟ²)` for every fixed
supported camera and native-line parameter. -/
theorem finiteBracketCharacteristic_cross_tail_isBigO {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    (fun cutoff : ℕ =>
      factor 3 (nativeLine t) *
          finiteBracketCharacteristic camera cutoff (nativeLine t) -
        factor camera (nativeLine t) *
          finiteBracketCharacteristic 3 cutoff (nativeLine t)) =O[atTop]
      (fun cutoff : ℕ => (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) := by
  let C : ℝ := (2 / 3 : ℝ) *
    (‖factor camera (nativeLine t)‖ * nativeTailConstant 3 t +
      ‖factor 3 (nativeLine t)‖ * nativeTailConstant camera t)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop 1] with cutoff hcutoff
  have htail := finiteBracketCharacteristic_cross_tail_le hcamera hcutoff t
  simpa only [C, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg cutoff) _)] using htail

end

end NativeCarrySpectralWeyl.Camera
