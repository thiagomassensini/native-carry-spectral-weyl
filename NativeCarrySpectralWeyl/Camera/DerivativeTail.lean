import NativeCarrySpectralWeyl.Camera.QuantitativeTail
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Quantitative derivative tails

Differentiating a Dirichlet sample in the complex exponent introduces one
factor of `log n`.  This module preserves the centered-bracket cancellation,
rather than bounding the three legs separately, and obtains the source rate
`cutoff⁻³ᐟ² log cutoff` for the first derivative.
-/

open scoped BigOperators
open Set Filter

namespace NativeCarrySpectralWeyl.Camera

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- The logarithmically weighted native-line block majorant. -/
def nativeLogTailWeight (index : ℕ) : ℝ :=
  Real.log ((index + 1 : ℕ) : ℝ) * nativeTailWeight index

/-- The threshold needed for monotonicity of `log x / x^(5/2)` lies below two. -/
theorem exp_two_fifths_le_two : Real.exp (2 / 5 : ℝ) ≤ 2 := by
  rw [← Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
  have hlog := Real.log_two_gt_d9
  norm_num at hlog ⊢
  linarith

/-- Continuous logarithmic tail integrand. -/
def nativeLogTailIntegrand (x : ℝ) : ℝ :=
  Real.log x * x ^ (-(5 : ℝ) / 2)

/-- An antiderivative chosen to vanish at positive infinity. -/
def nativeLogTailPrimitive (x : ℝ) : ℝ :=
  -(4 / 9 + (2 / 3 : ℝ) * Real.log x) * x ^ (-(3 : ℝ) / 2)

theorem nativeLogTailPrimitive_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt nativeLogTailPrimitive (nativeLogTailIntegrand x) x := by
  have hlog := Real.hasDerivAt_log hx.ne'
  have hpow := Real.hasDerivAt_rpow_const
    (p := -(3 : ℝ) / 2) (Or.inl hx.ne')
  have hcoeffRaw :=
    ((hlog.const_mul (2 / 3 : ℝ)).const_add (4 / 9 : ℝ)).neg
  have hcoeff : HasDerivAt
      (fun y : ℝ => -(4 / 9 + (2 / 3 : ℝ) * Real.log y))
      (-(2 / 3 : ℝ) * x⁻¹) x := by
    convert! hcoeffRaw using 1
    all_goals ring
  have hproduct := hcoeff.mul hpow
  have hfive : x ^ (-(5 : ℝ) / 2) = x⁻¹ * x ^ (-(3 : ℝ) / 2) := by
    rw [show -(5 : ℝ) / 2 = -1 + (-(3 : ℝ) / 2) by ring,
      Real.rpow_add hx, Real.rpow_neg_one]
  have hshift : x ^ (-(3 : ℝ) / 2 - 1) = x⁻¹ * x ^ (-(3 : ℝ) / 2) := by
    rw [show -(3 : ℝ) / 2 - 1 = -1 + (-(3 : ℝ) / 2) by ring,
      Real.rpow_add hx, Real.rpow_neg_one]
  have hderiv :
      (-(2 / 3 : ℝ) * x⁻¹) * x ^ (-(3 : ℝ) / 2) +
          -(4 / 9 + (2 / 3 : ℝ) * Real.log x) *
            (-(3 : ℝ) / 2 * x ^ (-(3 : ℝ) / 2 - 1)) =
        nativeLogTailIntegrand x := by
    unfold nativeLogTailIntegrand
    rw [hfive, hshift]
    ring
  rw [← hderiv]
  change HasDerivAt
    (fun y : ℝ => -(4 / 9 + (2 / 3 : ℝ) * Real.log y) *
      y ^ (-(3 : ℝ) / 2)) _ x
  convert! hproduct using 1

theorem nativeLogTailIntegrand_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ nativeLogTailIntegrand x := by
  exact mul_nonneg (Real.log_nonneg hx) (Real.rpow_nonneg (zero_le_one.trans hx) _)

theorem nativeLogTailPrimitive_tendsto :
    Tendsto nativeLogTailPrimitive atTop (nhds 0) := by
  have hlogzero : Tendsto
      (fun x : ℝ => Real.log x * x ^ (-(3 : ℝ) / 2)) atTop (nhds 0) := by
    have hdiv := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2))
      |>.tendsto_div_nhds_zero
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [show -(3 : ℝ) / 2 = -(3 / 2 : ℝ) by ring,
      Real.rpow_neg hx]
    simp only [div_eq_mul_inv]
  have hpowzero : Tendsto (fun x : ℝ => x ^ (-(3 : ℝ) / 2)) atTop (nhds 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)
  have hfirst := hlogzero.const_mul (-(2 / 3 : ℝ))
  have hsecond := hpowzero.const_mul (-(4 / 9 : ℝ))
  convert hfirst.add hsecond using 1
  · funext x
    unfold nativeLogTailPrimitive
    ring
  · norm_num

theorem nativeLogTailIntegrand_integrableOn_Ioi {c : ℝ} (hc : 1 ≤ c) :
    MeasureTheory.IntegrableOn nativeLogTailIntegrand (Ioi c) := by
  apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (g := nativeLogTailPrimitive) (l := 0)
  · intro x hx
    exact nativeLogTailPrimitive_hasDerivAt (zero_lt_one.trans_le (hc.trans hx))
  · intro x hx
    exact nativeLogTailIntegrand_nonneg (hc.trans hx.le)
  · exact nativeLogTailPrimitive_tendsto

/-- Exact improper integral of the logarithmically weighted native-line
majorant. -/
theorem integral_Ioi_log_mul_rpow_native {c : ℝ} (hc : 1 ≤ c) :
    ∫ x : ℝ in Ioi c, nativeLogTailIntegrand x =
      ((2 / 3 : ℝ) * Real.log c + 4 / 9) * c ^ (-(3 : ℝ) / 2) := by
  have hvalue := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := nativeLogTailPrimitive) (f' := nativeLogTailIntegrand) (m := 0)
    (fun x hx => nativeLogTailPrimitive_hasDerivAt
      (zero_lt_one.trans_le (hc.trans hx)))
    (nativeLogTailIntegrand_integrableOn_Ioi hc)
    nativeLogTailPrimitive_tendsto
  rw [hvalue]
  unfold nativeLogTailPrimitive
  ring

/-- Integral-test bound for the logarithmically weighted discrete tail. -/
theorem nativeLogTailWeight_tsum_nat_add_le {cutoff : ℕ} (hcutoff : 2 ≤ cutoff) :
    (∑' index : ℕ, nativeLogTailWeight (index + cutoff)) ≤
      ((2 / 3 : ℝ) * Real.log cutoff + 4 / 9) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  let f : ℝ → ℝ := fun x => Real.log x / x ^ (5 / 2 : ℝ)
  have hcutoffOne : (1 : ℝ) ≤ cutoff := by exact_mod_cast (hcutoff.trans' (by omega))
  have hcutoffPos : (0 : ℝ) < cutoff := zero_lt_one.trans_le hcutoffOne
  have hthreshold : Real.exp ((5 / 2 : ℝ)⁻¹) ≤ cutoff := by
    have htwo : Real.exp ((5 / 2 : ℝ)⁻¹) ≤ 2 := by
      convert exp_two_fifths_le_two using 1
      all_goals norm_num
    exact htwo.trans (by exact_mod_cast hcutoff)
  have hanti : AntitoneOn f (Ici (cutoff : ℝ)) :=
    (Real.log_div_self_rpow_antitoneOn (a := 5 / 2) (by norm_num)).mono
      (Ici_subset_Ici.mpr hthreshold)
  have hnonneg : ∀ x ∈ Ioi (cutoff : ℝ), 0 ≤ f x := by
    intro x hx
    exact div_nonneg (Real.log_nonneg (hcutoffOne.trans hx.le))
      (Real.rpow_nonneg (hcutoffPos.trans hx).le _)
  have hpointwise : ∀ x ∈ Ioi (cutoff : ℝ),
      nativeLogTailIntegrand x = f x := by
    intro x hx
    dsimp [nativeLogTailIntegrand, f]
    have hxpos : 0 < x := hcutoffPos.trans hx
    rw [show -(5 : ℝ) / 2 = -(5 / 2 : ℝ) by ring,
      Real.rpow_neg hxpos.le]
    simp only [div_eq_mul_inv]
  have hint : MeasureTheory.IntegrableOn f (Ioi (cutoff : ℝ)) :=
    (nativeLogTailIntegrand_integrableOn_Ioi hcutoffOne).congr_fun
      hpointwise measurableSet_Ioi
  have h := hanti.tsum_comp_add_le_integral cutoff hint hnonneg
  have hfi : (∫ x : ℝ in Ioi (cutoff : ℝ), f x) =
      ((2 / 3 : ℝ) * Real.log cutoff + 4 / 9) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [← integral_Ioi_log_mul_rpow_native hcutoffOne]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun x hx => (hpointwise x hx).symm)
  rw [hfi] at h
  calc
    (∑' index : ℕ, nativeLogTailWeight (index + cutoff)) =
        ∑' index : ℕ, f ((index : ℝ) + cutoff + 1) := by
      apply tsum_congr
      intro index
      dsimp [nativeLogTailWeight, nativeTailWeight, f]
      simp only [Nat.cast_add, Nat.cast_one]
      have hxpos : 0 < (index : ℝ) + cutoff + 1 := by positivity
      rw [show -(5 : ℝ) / 2 = -(5 / 2 : ℝ) by ring,
        Real.rpow_neg hxpos.le]
      simp only [div_eq_mul_inv]
    _ ≤ _ := by
      convert h using 1
      all_goals norm_num

/-- The logarithmically weighted native-line majorant is summable. -/
theorem nativeLogTailWeight_summable : Summable nativeLogTailWeight := by
  have hbase : Summable (fun index : ℕ =>
      2 * (((index + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) := by
    apply Summable.mul_left
    exact (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num))
  apply Summable.of_nonneg_of_le
    (fun index => by
      unfold nativeLogTailWeight nativeTailWeight
      have hone : (1 : ℝ) ≤ ((index + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_add_left 1 index)
      exact mul_nonneg (Real.log_nonneg hone)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _ hbase
  intro index
  let x : ℝ := (index + 1 : ℕ)
  have hx : 0 < x := by positivity
  have hlog := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1 / 2)
  change Real.log x * x ^ (-(5 : ℝ) / 2) ≤ 2 * x ^ (-2 : ℝ)
  calc
    Real.log x * x ^ (-(5 : ℝ) / 2) ≤
        (x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) * x ^ (-(5 : ℝ) / 2) := by
      gcongr
    _ = 2 * x ^ (-2 : ℝ) := by
      rw [div_eq_mul_inv]
      rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
      rw [show x ^ (1 / 2 : ℝ) * 2 * x ^ (-(5 : ℝ) / 2) =
        2 * (x ^ (1 / 2 : ℝ) * x ^ (-(5 : ℝ) / 2)) by ring,
        ← Real.rpow_add hx]
      norm_num

/-! ## Differentiated Dirichlet brackets -/

/-- Complex-exponent derivative of a positive Dirichlet sample. -/
def dirichletValueExponentDeriv (s : ℂ) (n : ℕ) : ℂ :=
  -(Real.log n : ℂ) * dirichletValue s n

theorem dirichletValue_hasDerivAt {n : ℕ} (hn : 0 < n) (s : ℂ) :
    HasDerivAt (fun z => dirichletValue z n) (dirichletValueExponentDeriv s n) s := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hpow := (hasDerivAt_neg' s).const_cpow (Or.inl hnC)
  unfold dirichletValue dirichletValueExponentDeriv
  rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ n)]
  convert! hpow using 1
  simp [dirichletValue, mul_comm]

/-- Real-variable kernel representing differentiation in the exponent. -/
def dirichletKernelExponentDeriv (s : ℂ) (x : ℝ) : ℂ :=
  -(Real.log x : ℂ) * dirichletKernel s x

/-- First real derivative of the exponent-derivative kernel. -/
def dirichletKernelExponentDerivX (s : ℂ) (x : ℝ) : ℂ :=
  (s * (Real.log x : ℂ) - 1) * (x : ℂ) ^ (-s - 1)

/-- Second real derivative of the exponent-derivative kernel. -/
def dirichletKernelExponentDerivXX (s : ℂ) (x : ℝ) : ℂ :=
  ((2 * s + 1) - s * (s + 1) * (Real.log x : ℂ)) *
    (x : ℂ) ^ (-s - 2)

theorem ofReal_inv_mul_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ)⁻¹ * (x : ℂ) ^ z = (x : ℂ) ^ (z - 1) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [show z - 1 = (-1 : ℂ) + z by ring,
    Complex.cpow_add _ _ hxC, Complex.cpow_neg_one]

theorem dirichletKernelExponentDeriv_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dirichletKernelExponentDeriv s)
      (dirichletKernelExponentDerivX s x) x := by
  have hlog : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x : ℂ)⁻¹) x := by
    convert! (Real.hasDerivAt_log hx.ne').ofReal_comp using 1
    norm_cast
  have hpow := dirichletKernel_hasDerivAt s hx
  have hproduct := hlog.neg.mul hpow
  have hshift := ofReal_inv_mul_cpow hx (-s)
  unfold dirichletKernelExponentDeriv dirichletKernelExponentDerivX dirichletKernel at *
  convert! hproduct using 1
  simp only [Pi.neg_apply]
  rw [dirichletKernelDeriv, neg_mul, hshift]
  ring

theorem dirichletKernelExponentDerivX_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dirichletKernelExponentDerivX s)
      (dirichletKernelExponentDerivXX s x) x := by
  have hlog : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x : ℂ)⁻¹) x := by
    convert! (Real.hasDerivAt_log hx.ne').ofReal_comp using 1
    norm_cast
  have hcoeff : HasDerivAt
      (fun y : ℝ => s * (Real.log y : ℂ) - 1) (s * (x : ℂ)⁻¹) x := by
    exact (hlog.const_mul s).sub_const 1
  by_cases hs : s = -1
  · subst s
    have hsimple := hlog.neg.sub_const 1
    unfold dirichletKernelExponentDerivX dirichletKernelExponentDerivXX
    convert! hsimple using 1
    · simp [Complex.cpow_zero]
    · norm_num
      rw [Complex.cpow_neg_one]
  · have hexponent : -s - 1 ≠ 0 := by
      intro h
      apply hs
      linear_combination -h
    have hpow := hasDerivAt_ofReal_cpow_const hx.ne' hexponent
    have hproduct := hcoeff.mul hpow
    have hshift := ofReal_inv_mul_cpow hx (-s - 1)
    unfold dirichletKernelExponentDerivX dirichletKernelExponentDerivXX at *
    convert! hproduct using 1
    have hfirst : s * (x : ℂ)⁻¹ * (x : ℂ) ^ (-s - 1) =
        s * (x : ℂ) ^ (-s - 2) := by
      rw [mul_assoc, hshift]
      congr 2
      ring
    rw [hfirst, show -s - 1 - 1 = -s - 2 by ring]
    ring

/-- Norm bound for the second real derivative; this is the source of the one
logarithmic loss in the differentiated cutoff tail. -/
theorem dirichletKernelExponentDerivXX_norm_le (s : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖dirichletKernelExponentDerivXX s x‖ ≤
      (‖2 * s + 1‖ + ‖s * (s + 1)‖ * Real.log x) *
        x ^ (-s.re - 2) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  rw [dirichletKernelExponentDerivXX, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have hcoeff :
      ‖(2 * s + 1) - s * (s + 1) * (Real.log x : ℂ)‖ ≤
        ‖2 * s + 1‖ + ‖s * (s + 1)‖ * Real.log x := by
    calc
      ‖(2 * s + 1) - s * (s + 1) * (Real.log x : ℂ)‖ ≤
          ‖2 * s + 1‖ + ‖s * (s + 1) * (Real.log x : ℂ)‖ :=
        norm_sub_le _ _
      _ = ‖2 * s + 1‖ + ‖s * (s + 1)‖ * Real.log x := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg hx)]
  exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hxpos.le _)

/-- Exponent derivative of one centered natural bracket. -/
def centeredBracketExponentDerivTerm (s : ℂ) (center radius : ℕ) : ℂ :=
  dirichletValueExponentDeriv s (center - radius) -
    2 * dirichletValueExponentDeriv s center +
      dirichletValueExponentDeriv s (center + radius)

/-- The explicit logarithmic expression is the complex derivative of a valid
centered bracket. -/
theorem centeredBracketTerm_hasDerivAt (s : ℂ) {center radius : ℕ}
    (hradius : radius < center) :
    HasDerivAt (fun z => centeredBracketTerm z center radius)
      (centeredBracketExponentDerivTerm s center radius) s := by
  have hleft : 0 < center - radius := Nat.sub_pos_of_lt hradius
  have hcenter : 0 < center := hleft.trans_le (Nat.sub_le center radius)
  have hright : 0 < center + radius :=
    hcenter.trans_le (Nat.le_add_right center radius)
  exact ((dirichletValue_hasDerivAt hleft s).sub
    ((dirichletValue_hasDerivAt hcenter s).const_mul 2)).add
      (dirichletValue_hasDerivAt hright s)

/-- Native-line bound for one differentiated centered bracket.  The
centered-second-difference cancellation is retained before norms are taken. -/
theorem centeredBracketExponentDerivTerm_norm_le_nativeLine
    (t : ℝ) {center radius index : ℕ}
    (hradius : radius < center) (hlower : index + 1 ≤ center - radius) :
    ‖centeredBracketExponentDerivTerm (nativeLine t) center radius‖ ≤
      ((‖2 * nativeLine t + 1‖ +
          ‖nativeLine t * (nativeLine t + 1)‖ *
            Real.log ((center + radius : ℕ) : ℝ)) * nativeTailWeight index) *
        (radius : ℝ) ^ 2 := by
  let s := nativeLine t
  let left : ℝ := (center - radius : ℕ)
  let right : ℝ := center + radius
  let C : ℝ :=
    (‖2 * s + 1‖ + ‖s * (s + 1)‖ * Real.log right) *
      nativeTailWeight index
  have hleftOne : 1 ≤ left := by
    dsimp [left]
    exact_mod_cast hlower.trans' (Nat.le_add_left 1 index)
  have hleftPos : 0 < left := zero_lt_one.trans_le hleftOne
  have hcastSub : ((center - radius : ℕ) : ℝ) = (center : ℝ) - radius := by
    exact Nat.cast_sub hradius.le
  have hcenterRight : (center : ℝ) + radius = right := by
    simp [right]
  have hrightOne : 1 ≤ right := by
    dsimp [right]
    have hcenterOne : 1 ≤ center := by omega
    exact_mod_cast hcenterOne.trans (Nat.le_add_right center radius)
  have hbound : ∀ x ∈ Icc ((center : ℝ) - radius) ((center : ℝ) + radius),
      ‖dirichletKernelExponentDerivXX s x‖ ≤ C := by
    intro x hx
    have hleftx : left ≤ x := by
      change ((center - radius : ℕ) : ℝ) ≤ x
      rw [hcastSub]
      exact hx.1
    have hxOne : 1 ≤ x := by
      exact hleftOne.trans hleftx
    have hxpos : 0 < x := zero_lt_one.trans_le hxOne
    have hlog : Real.log x ≤ Real.log right := by
      apply Real.log_le_log hxpos
      simpa only [hcenterRight] using hx.2
    have hpow : x ^ (-(5 : ℝ) / 2) ≤ nativeTailWeight index := by
      unfold nativeTailWeight
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · have hindex : (((index + 1 : ℕ) : ℝ)) ≤ left := by
          dsimp [left]
          exact_mod_cast hlower
        exact hindex.trans hleftx
      · norm_num
    have hkernel := dirichletKernelExponentDerivXX_norm_le s hxOne
    rw [show -s.re - 2 = -(5 : ℝ) / 2 by
      dsimp [s]
      rw [nativeLine_re]
      norm_num] at hkernel
    calc
      ‖dirichletKernelExponentDerivXX s x‖ ≤
          (‖2 * s + 1‖ + ‖s * (s + 1)‖ * Real.log x) *
            x ^ (-(5 : ℝ) / 2) := hkernel
      _ ≤ (‖2 * s + 1‖ + ‖s * (s + 1)‖ * Real.log right) *
            nativeTailWeight index := by
        gcongr
        exact add_nonneg (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (Real.log_nonneg hrightOne))
  have hcentered := norm_centeredSecondDifference_le
    (f := dirichletKernelExponentDeriv s)
    (f' := dirichletKernelExponentDerivX s)
    (f'' := dirichletKernelExponentDerivXX s)
    (center := (center : ℝ)) (radius := (radius : ℝ))
    (C := C) (by positivity)
    (fun x hx => dirichletKernelExponentDeriv_hasDerivAt s
      (hleftPos.trans_le (by
        change ((center - radius : ℕ) : ℝ) ≤ x
        rw [hcastSub]
        exact hx.1)))
    (fun x hx => dirichletKernelExponentDerivX_hasDerivAt s
      (hleftPos.trans_le (by
        change ((center - radius : ℕ) : ℝ) ≤ x
        rw [hcastSub]
        exact hx.1)))
    hbound
  unfold centeredBracketExponentDerivTerm dirichletValueExponentDeriv
    dirichletValue
  rw [← hcastSub] at hcentered
  simpa only [s, C, left, right, Nat.cast_add, Complex.ofReal_natCast,
    Complex.ofReal_add, dirichletKernelExponentDeriv, dirichletKernel] using hcentered

/-! ## Camera-scale derivative majorants -/

/-- A simple positive scale dominating the right leg of every aligned center
block.  It is `5` for C2 and `2b` for a natural camera `b`. -/
def cameraDerivativeScale (camera : ℕ) : ℕ :=
  if camera = 2 then 5 else 2 * camera

theorem cameraDerivativeScale_pos {camera : ℕ} (hcamera : 2 ≤ camera) :
    0 < cameraDerivativeScale camera := by
  unfold cameraDerivativeScale
  split_ifs <;> omega

theorem c2_alignedCenter_add_one_le_scale (index : ℕ) :
    alignedCenter 2 index + 1 ≤ cameraDerivativeScale 2 * (index + 1) := by
  simp only [alignedCenter_eq_cameraSlope_mul, cameraSlope_two,
    cameraDerivativeScale, if_pos]
  omega

theorem natural_alignedCenter_add_radius_le_scale {camera radius index : ℕ}
    (hcamera : 3 ≤ camera) (hradius : radius ∈ radiusSet camera) :
    alignedCenter camera index + radius ≤
      cameraDerivativeScale camera * (index + 1) := by
  have h2 : camera ≠ 2 := by omega
  have hradiusCamera : radius ≤ camera :=
    (mem_radiusSet_iff.mp hradius).2.trans (Nat.div_le_self camera 2)
  have hcameraMul : camera ≤ camera * (index + 1) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left camera (Nat.one_le_iff_ne_zero.mpr (by omega : index + 1 ≠ 0))
  rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_of_ne_two h2,
    cameraDerivativeScale, if_neg h2, two_mul]
  calc
    camera * (index + 1) + radius ≤
        camera * (index + 1) + camera * (index + 1) :=
      Nat.add_le_add_left (hradiusCamera.trans hcameraMul) _
    _ = (camera + camera) * (index + 1) := (Nat.add_mul _ _ _).symm

/-- The right leg contributes at most a camera-dependent constant plus
`log(index + 1)`. -/
theorem alignedCenter_add_radius_log_le {camera radius index : ℕ}
    (hcamera : 2 ≤ camera)
    (hright : alignedCenter camera index + radius ≤
      cameraDerivativeScale camera * (index + 1)) :
    Real.log (alignedCenter camera index + radius) ≤
      Real.log (cameraDerivativeScale camera) + Real.log (index + 1) := by
  have hrightPos : 0 < alignedCenter camera index + radius := by
    rw [alignedCenter_eq_cameraSlope_mul]
    have hslope : 0 < cameraSlope camera := by
      by_cases h2 : camera = 2
      · subst camera
        simp
      · rw [cameraSlope_of_ne_two h2]
        omega
    positivity
  have hscalePos := cameraDerivativeScale_pos hcamera
  calc
    Real.log (alignedCenter camera index + radius) ≤
        Real.log (cameraDerivativeScale camera * (index + 1)) := by
      apply Real.log_le_log
      · exact_mod_cast hrightPos
      · exact_mod_cast hright
    _ = Real.log (cameraDerivativeScale camera) + Real.log (index + 1) := by
      rw [Real.log_mul (by exact_mod_cast hscalePos.ne') (by positivity)]

/-- One coefficient controls both the plain and logarithmically weighted
native-line tails of a fixed camera. -/
def nativeDerivativeTailConstant (camera : ℕ) (t : ℝ) : ℝ :=
  (‖2 * nativeLine t + 1‖ +
      ‖nativeLine t * (nativeLine t + 1)‖ *
        (Real.log (cameraDerivativeScale camera) + 1)) *
    cameraRadiusSqSum camera

theorem nativeDerivativeTailConstant_nonneg {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    0 ≤ nativeDerivativeTailConstant camera t := by
  have hscaleOne : 1 ≤ cameraDerivativeScale camera :=
    cameraDerivativeScale_pos hcamera
  have hlog : 0 ≤ Real.log (cameraDerivativeScale camera) := by
    exact Real.log_nonneg (by exact_mod_cast hscaleOne)
  unfold nativeDerivativeTailConstant
  exact mul_nonneg
    (add_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (by linarith)))
    (cameraRadiusSqSum_nonneg camera)

/-- Exponent derivative of all centered brackets emitted at one aligned
camera center. -/
def centerBracketExponentDeriv (camera : ℕ) (s : ℂ) (index : ℕ) : ℂ :=
  if camera = 2 then
    centeredBracketExponentDerivTerm s (alignedCenter 2 index) 1
  else
    ∑ radius ∈ radiusSet camera,
      centeredBracketExponentDerivTerm s (alignedCenter camera index) radius

/-- Exact complex-exponent derivative of one aligned center block. -/
theorem centerBracketTerm_hasDerivAt {camera : ℕ} (hcamera : 2 ≤ camera)
    (index : ℕ) (s : ℂ) :
    HasDerivAt (fun z => centerBracketTerm camera z index)
      (centerBracketExponentDeriv camera s index) s := by
  by_cases h2 : camera = 2
  · subst camera
    simp only [centerBracketTerm, centerBracketExponentDeriv, if_pos]
    apply centeredBracketTerm_hasDerivAt
    rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_two]
    omega
  · have hcamera3 : 3 ≤ camera := by omega
    simp only [centerBracketTerm, centerBracketExponentDeriv, h2, if_false]
    exact HasDerivAt.fun_sum fun radius hradius =>
      centeredBracketTerm_hasDerivAt s (by
        have hlower := natural_index_succ_le_alignedCenter_sub hcamera3 hradius
          (index := index)
        omega)

/-- Exponent derivative of the finite exceptional seed block. -/
def seedDirichletExponentDeriv (camera : ℕ) (s : ℂ) : ℂ :=
  if camera = 2 then dirichletValueExponentDeriv s 1
  else ∑ radius ∈ radiusSet camera, dirichletValueExponentDeriv s radius

theorem seedDirichletTerm_hasDerivAt {camera : ℕ} (hcamera : 2 ≤ camera)
    (s : ℂ) : HasDerivAt (fun z => seedDirichletTerm camera z)
      (seedDirichletExponentDeriv camera s) s := by
  by_cases h2 : camera = 2
  · subst camera
    simp only [seedDirichletTerm, seedDirichletExponentDeriv, if_pos]
    exact dirichletValue_hasDerivAt (by norm_num) s
  · simp only [seedDirichletTerm, seedDirichletExponentDeriv, h2, if_false]
    exact HasDerivAt.fun_sum fun radius hradius =>
      dirichletValue_hasDerivAt
        ((mem_radiusSet_iff.mp hradius).1.trans_lt' (by omega)) s

/-- Explicit exponent derivative of a characteristic with exactly `cutoff`
aligned center blocks. -/
def finiteBracketCharacteristicExponentDeriv
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  seedDirichletExponentDeriv camera s +
    ∑ index ∈ Finset.range cutoff, centerBracketExponentDeriv camera s index

theorem finiteBracketCharacteristic_hasDerivAt {camera : ℕ}
    (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    HasDerivAt (finiteBracketCharacteristic camera cutoff)
      (finiteBracketCharacteristicExponentDeriv camera cutoff s) s := by
  exact (seedDirichletTerm_hasDerivAt hcamera s).add
    (HasDerivAt.fun_sum fun index _ => centerBracketTerm_hasDerivAt hcamera index s)

theorem deriv_centerBracketTerm {camera : ℕ} (hcamera : 2 ≤ camera)
    (index : ℕ) (s : ℂ) :
    deriv (fun z => centerBracketTerm camera z index) s =
      centerBracketExponentDeriv camera s index :=
  (centerBracketTerm_hasDerivAt hcamera index s).deriv

theorem deriv_finiteBracketCharacteristic {camera : ℕ}
    (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    deriv (finiteBracketCharacteristic camera cutoff) s =
      finiteBracketCharacteristicExponentDeriv camera cutoff s :=
  (finiteBracketCharacteristic_hasDerivAt hcamera cutoff s).deriv

/-- Every differentiated native-line center block is dominated by the sum of
the plain and logarithmic `m⁻⁵ᐟ²` weights. -/
theorem centerBracketExponentDeriv_norm_le_nativeTail {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) (index : ℕ) :
    ‖centerBracketExponentDeriv camera (nativeLine t) index‖ ≤
      nativeDerivativeTailConstant camera t *
        (nativeTailWeight index + nativeLogTailWeight index) := by
  let a : ℝ := ‖2 * nativeLine t + 1‖
  let b : ℝ := ‖nativeLine t * (nativeLine t + 1)‖
  let L : ℝ := Real.log (cameraDerivativeScale camera)
  have hscaleOne : 1 ≤ cameraDerivativeScale camera :=
    cameraDerivativeScale_pos hcamera
  have hL : 0 ≤ L := by exact Real.log_nonneg (by exact_mod_cast hscaleOne)
  have hlogIndex : 0 ≤ Real.log (index + 1) := by
    have hindexOne : (1 : ℕ) ≤ index + 1 := by omega
    exact Real.log_nonneg (by exact_mod_cast hindexOne)
  have hcoefficient {right : ℕ}
      (hlog : Real.log right ≤ L + Real.log (index + 1)) :
      a + b * Real.log right ≤
        (a + b * (L + 1)) * (1 + Real.log (index + 1)) := by
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    calc
      a + b * Real.log right ≤ a + b * (L + Real.log (index + 1)) := by
        gcongr
      _ ≤ (a + b * (L + 1)) * (1 + Real.log (index + 1)) := by
        have halog : 0 ≤ a * Real.log (index + 1) :=
          mul_nonneg ha hlogIndex
        have hbLlog : 0 ≤ (b * L) * Real.log (index + 1) :=
          mul_nonneg (mul_nonneg hb hL) hlogIndex
        nlinarith
  have hradiusBound {center radius : ℕ}
      (hradius : radius < center) (hlower : index + 1 ≤ center - radius)
      (hright : center + radius ≤ cameraDerivativeScale camera * (index + 1)) :
      ‖centeredBracketExponentDerivTerm (nativeLine t) center radius‖ ≤
        ((a + b * (L + 1)) *
          (nativeTailWeight index + nativeLogTailWeight index)) *
            (radius : ℝ) ^ 2 := by
    have hterm := centeredBracketExponentDerivTerm_norm_le_nativeLine t
      hradius hlower
    have hrightPos : 0 < center + radius := by omega
    have hlog : Real.log ((center + radius : ℕ) : ℝ) ≤
        L + Real.log (index + 1) := by
      dsimp [L]
      calc
        Real.log ((center + radius : ℕ) : ℝ) ≤
            Real.log (cameraDerivativeScale camera * (index + 1)) := by
          apply Real.log_le_log
          · exact_mod_cast hrightPos
          · exact_mod_cast hright
        _ = Real.log (cameraDerivativeScale camera) +
            Real.log (index + 1) := by
          rw [Real.log_mul (by
            exact_mod_cast (cameraDerivativeScale_pos hcamera).ne') (by positivity)]
    have hcoeff := hcoefficient hlog
    have hweight : 0 ≤ nativeTailWeight index := Real.rpow_nonneg (by positivity) _
    calc
      ‖centeredBracketExponentDerivTerm (nativeLine t) center radius‖ ≤
          ((a + b * Real.log ((center + radius : ℕ) : ℝ)) *
            nativeTailWeight index) *
            (radius : ℝ) ^ 2 := by simpa only [a, b] using hterm
      _ ≤ (((a + b * (L + 1)) * (1 + Real.log (index + 1))) *
          nativeTailWeight index) * (radius : ℝ) ^ 2 := by
        gcongr
      _ = ((a + b * (L + 1)) *
          (nativeTailWeight index + nativeLogTailWeight index)) *
            (radius : ℝ) ^ 2 := by
        unfold nativeLogTailWeight
        simp only [Nat.cast_add, Nat.cast_one]
        ring
  by_cases h2 : camera = 2
  · subst camera
    simp only [centerBracketExponentDeriv, if_pos]
    have hcenter : 1 < alignedCenter 2 index := by
      rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_two]
      omega
    have hsingle := hradiusBound hcenter
      (c2_index_succ_le_alignedCenter_sub index)
      (c2_alignedCenter_add_one_le_scale index)
    simpa only [nativeDerivativeTailConstant, cameraRadiusSqSum, if_pos,
      Nat.cast_one, one_pow, mul_one, a, b, L] using hsingle
  · have hcamera3 : 3 ≤ camera := by omega
    simp only [centerBracketExponentDeriv, h2, if_false]
    calc
      ‖∑ radius ∈ radiusSet camera,
          centeredBracketExponentDerivTerm (nativeLine t)
            (alignedCenter camera index) radius‖ ≤
          ∑ radius ∈ radiusSet camera,
            ‖centeredBracketExponentDerivTerm (nativeLine t)
              (alignedCenter camera index) radius‖ := norm_sum_le _ _
      _ ≤ ∑ radius ∈ radiusSet camera,
          ((a + b * (L + 1)) *
            (nativeTailWeight index + nativeLogTailWeight index)) *
              (radius : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro radius hradius
        apply hradiusBound
        · have hlower := natural_index_succ_le_alignedCenter_sub hcamera3 hradius
            (index := index)
          omega
        · exact natural_index_succ_le_alignedCenter_sub hcamera3 hradius
        · exact natural_alignedCenter_add_radius_le_scale hcamera3 hradius
      _ = nativeDerivativeTailConstant camera t *
          (nativeTailWeight index + nativeLogTailWeight index) := by
        unfold nativeDerivativeTailConstant cameraRadiusSqSum
        simp only [h2, if_false]
        rw [← Finset.mul_sum]
        dsimp [a, b, L]
        ring

/-! ## Differentiated series and cutoff tails -/

theorem centerBracketExponentDeriv_summable {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    Summable (centerBracketExponentDeriv camera (nativeLine t)) := by
  have hmajor : Summable (fun index =>
      nativeTailWeight index + nativeLogTailWeight index) :=
    nativeTailWeight_summable.add nativeLogTailWeight_summable
  exact (hmajor.mul_left (nativeDerivativeTailConstant camera t)).of_norm_bounded
    (centerBracketExponentDeriv_norm_le_nativeTail hcamera t)

/-- Termwise exponent derivative of the infinite bracket characteristic on the
native line. -/
def bracketCharacteristicExponentDeriv
    (camera : ℕ) (s : ℂ) : ℂ :=
  seedDirichletExponentDeriv camera s +
    ∑' index, centerBracketExponentDeriv camera s index

/-- Normal convergence identifies the derivative of the infinite
characteristic with the explicitly differentiated centered series. -/
theorem deriv_bracketCharacteristic_nativeLine {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    deriv (bracketCharacteristic camera) (nativeLine t) =
      bracketCharacteristicExponentDeriv camera (nativeLine t) := by
  have hdomain : nativeLine t ∈ bracketDomain := by
    simp [bracketDomain]
    norm_num
  have hderivConvergence :=
    (finiteBracketCharacteristic_tendstoLocallyUniformlyOn hcamera).deriv
      (Filter.Eventually.of_forall fun cutoff =>
        (finiteBracketCharacteristic_differentiable hcamera cutoff).differentiableOn)
      isOpen_bracketDomain
  have hlimit : Tendsto
      (fun cutoff => deriv (finiteBracketCharacteristic camera cutoff)
        (nativeLine t)) atTop
      (nhds (deriv (bracketCharacteristic camera) (nativeLine t))) := by
    simpa only [Function.comp_apply] using hderivConvergence.tendsto_at hdomain
  have hsum := centerBracketExponentDeriv_summable hcamera t
  have hexplicit : Tendsto
      (fun cutoff => finiteBracketCharacteristicExponentDeriv camera cutoff
        (nativeLine t)) atTop
      (nhds (bracketCharacteristicExponentDeriv camera (nativeLine t))) := by
    unfold finiteBracketCharacteristicExponentDeriv
      bracketCharacteristicExponentDeriv
    exact tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique hlimit
  exact hexplicit.congr' (Filter.Eventually.of_forall fun cutoff =>
    (deriv_finiteBracketCharacteristic hcamera cutoff (nativeLine t)).symm)

/-- Infinite-minus-finite derivative is literally the shifted differentiated
center-block tail. -/
theorem bracketCharacteristicExponentDeriv_sub_finite_eq_tsum_nat_add
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (t : ℝ) :
    bracketCharacteristicExponentDeriv camera (nativeLine t) -
        finiteBracketCharacteristicExponentDeriv camera cutoff (nativeLine t) =
      ∑' index : ℕ,
        centerBracketExponentDeriv camera (nativeLine t) (index + cutoff) := by
  have hsum := centerBracketExponentDeriv_summable hcamera t
  have hsplit := hsum.sum_add_tsum_nat_add cutoff
  unfold bracketCharacteristicExponentDeriv
    finiteBracketCharacteristicExponentDeriv
  rw [← hsplit]
  ring

/-- Explicit first-derivative tail bound.  Its dominant term is exactly
`cutoff⁻³ᐟ² log cutoff`. -/
theorem bracketCharacteristicExponentDeriv_tail_le {camera cutoff : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : 2 ≤ cutoff) (t : ℝ) :
    ‖bracketCharacteristicExponentDeriv camera (nativeLine t) -
        finiteBracketCharacteristicExponentDeriv camera cutoff (nativeLine t)‖ ≤
      nativeDerivativeTailConstant camera t *
        ((2 / 3 : ℝ) * Real.log cutoff + 10 / 9) *
          (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  rw [bracketCharacteristicExponentDeriv_sub_finite_eq_tsum_nat_add hcamera]
  have hshiftInjective : Function.Injective (fun index : ℕ => index + cutoff) := by
    intro left right h
    exact Nat.add_right_cancel h
  have hshiftSummable :=
    (centerBracketExponentDeriv_summable hcamera t).comp_injective hshiftInjective
  have hnormSummable : Summable (fun index : ℕ =>
      ‖centerBracketExponentDeriv camera (nativeLine t) (index + cutoff)‖) :=
    summable_norm_iff.mpr hshiftSummable
  have hweightSummable : Summable (fun index : ℕ =>
      nativeTailWeight (index + cutoff)) := by
    exact (summable_nat_add_iff cutoff).mpr nativeTailWeight_summable
  have hlogWeightSummable : Summable (fun index : ℕ =>
      nativeLogTailWeight (index + cutoff)) := by
    exact (summable_nat_add_iff cutoff).mpr nativeLogTailWeight_summable
  have hmajorSummable : Summable (fun index : ℕ =>
      nativeDerivativeTailConstant camera t *
        (nativeTailWeight (index + cutoff) +
          nativeLogTailWeight (index + cutoff))) :=
    (hweightSummable.add hlogWeightSummable).mul_left _
  calc
    ‖∑' index : ℕ,
        centerBracketExponentDeriv camera (nativeLine t) (index + cutoff)‖ ≤
        ∑' index : ℕ,
          ‖centerBracketExponentDeriv camera (nativeLine t) (index + cutoff)‖ :=
      norm_tsum_le_tsum_norm hnormSummable
    _ ≤ ∑' index : ℕ, nativeDerivativeTailConstant camera t *
        (nativeTailWeight (index + cutoff) +
          nativeLogTailWeight (index + cutoff)) := by
      exact Summable.tsum_le_tsum
        (fun index => centerBracketExponentDeriv_norm_le_nativeTail
          hcamera t (index + cutoff)) hnormSummable hmajorSummable
    _ = nativeDerivativeTailConstant camera t *
        ((∑' index : ℕ, nativeTailWeight (index + cutoff)) +
          ∑' index : ℕ, nativeLogTailWeight (index + cutoff)) := by
      rw [tsum_mul_left, hweightSummable.tsum_add hlogWeightSummable]
    _ ≤ nativeDerivativeTailConstant camera t *
        (((2 / 3 : ℝ) * (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) +
          (((2 / 3 : ℝ) * Real.log cutoff + 4 / 9) *
            (cutoff : ℝ) ^ (-(3 : ℝ) / 2))) := by
      apply mul_le_mul_of_nonneg_left _
        (nativeDerivativeTailConstant_nonneg hcamera t)
      exact add_le_add
        (nativeTailWeight_tsum_nat_add_le (hcutoff.trans' (by omega)))
        (nativeLogTailWeight_tsum_nat_add_le hcutoff)
    _ = nativeDerivativeTailConstant camera t *
        ((2 / 3 : ℝ) * Real.log cutoff + 10 / 9) *
          (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by ring

/-- The first complex-exponent derivative of the infinite characteristic is
quantitatively approximated by the derivative of the `cutoff`-block model. -/
theorem deriv_bracketCharacteristic_nativeLine_tail_le {camera cutoff : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : 2 ≤ cutoff) (t : ℝ) :
    ‖deriv (bracketCharacteristic camera) (nativeLine t) -
        deriv (finiteBracketCharacteristic camera cutoff) (nativeLine t)‖ ≤
      nativeDerivativeTailConstant camera t *
        ((2 / 3 : ℝ) * Real.log cutoff + 10 / 9) *
          (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  rw [deriv_bracketCharacteristic_nativeLine hcamera,
    deriv_finiteBracketCharacteristic hcamera]
  exact bracketCharacteristicExponentDeriv_tail_le hcamera hcutoff t

/-! ## Derivatives in the native-line parameter -/

theorem deriv_finiteBracketCharacteristic_nativeLine {camera : ℕ}
    (hcamera : 2 ≤ camera) (cutoff : ℕ) (t : ℝ) :
    deriv (fun u : ℝ => finiteBracketCharacteristic camera cutoff (nativeLine u)) t =
      finiteBracketCharacteristicExponentDeriv camera cutoff (nativeLine t) *
        Complex.I := by
  have hid : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hline :=
    (hasDerivAt_const t (1 / 2 : ℂ)).add (hid.mul_const Complex.I)
  have hlineFun :
      ((fun _u : ℝ => (1 / 2 : ℂ)) + fun u : ℝ => (u : ℂ) * Complex.I) =
        nativeLine := by
    funext u
    simp only [Pi.add_apply, nativeLine]
  rw [hlineFun] at hline
  have hcomp :=
    (finiteBracketCharacteristic_hasDerivAt hcamera cutoff (nativeLine t)).scomp t
      hline
  have hd := hcomp.deriv
  change deriv (finiteBracketCharacteristic camera cutoff ∘ nativeLine) t = _
  simpa only [smul_eq_mul, zero_add, mul_one, mul_comm] using hd

theorem deriv_bracketCharacteristic_along_nativeLine {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    deriv (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) t =
      bracketCharacteristicExponentDeriv camera (nativeLine t) * Complex.I := by
  have hid : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hline :=
    (hasDerivAt_const t (1 / 2 : ℂ)).add (hid.mul_const Complex.I)
  have hlineFun :
      ((fun _u : ℝ => (1 / 2 : ℂ)) + fun u : ℝ => (u : ℂ) * Complex.I) =
        nativeLine := by
    funext u
    simp only [Pi.add_apply, nativeLine]
  rw [hlineFun] at hline
  have hdomain : nativeLine t ∈ bracketDomain := by
    simp [bracketDomain]
    norm_num
  have hdifferentiable : DifferentiableAt ℂ (bracketCharacteristic camera)
      (nativeLine t) :=
    (bracketCharacteristic_differentiableOn hcamera).differentiableAt
      (isOpen_bracketDomain.mem_nhds hdomain)
  have houter : HasDerivAt (bracketCharacteristic camera)
      (bracketCharacteristicExponentDeriv camera (nativeLine t))
      (nativeLine t) := by
    rw [← deriv_bracketCharacteristic_nativeLine hcamera]
    exact hdifferentiable.hasDerivAt
  have hcomp := houter.scomp t hline
  have hd := hcomp.deriv
  change deriv (bracketCharacteristic camera ∘ nativeLine) t = _
  simpa only [smul_eq_mul, zero_add, mul_one, mul_comm] using hd

/-- Source-form estimate for the actual `t` derivative on
`s = 1/2 + it`.  Multiplication by `I` does not change the norm. -/
theorem deriv_along_nativeLine_tail_le {camera cutoff : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : 2 ≤ cutoff) (t : ℝ) :
    ‖deriv (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) t -
        deriv (fun u : ℝ =>
          finiteBracketCharacteristic camera cutoff (nativeLine u)) t‖ ≤
      nativeDerivativeTailConstant camera t *
        ((2 / 3 : ℝ) * Real.log cutoff + 10 / 9) *
          (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  rw [deriv_bracketCharacteristic_along_nativeLine hcamera,
    deriv_finiteBracketCharacteristic_nativeLine hcamera]
  rw [← sub_mul, norm_mul, Complex.norm_I, mul_one]
  exact bracketCharacteristicExponentDeriv_tail_le hcamera hcutoff t

/-- Asymptotic source rate for the first native-line derivative:
`O(cutoff⁻³ᐟ² log cutoff)`. -/
theorem deriv_along_nativeLine_tail_isBigO {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    (fun cutoff : ℕ =>
      deriv (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) t -
        deriv (fun u : ℝ =>
          finiteBracketCharacteristic camera cutoff (nativeLine u)) t) =O[atTop]
      (fun cutoff : ℕ =>
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) * Real.log cutoff) := by
  let K : ℝ := nativeDerivativeTailConstant camera t * (16 / 9 : ℝ)
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop 3] with cutoff hcutoff
  have hlogThree : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_three_gt_d9
    norm_num at h ⊢
    linarith
  have hlogMono : Real.log 3 ≤ Real.log cutoff := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hcutoff
  have hlogOne : (1 : ℝ) ≤ Real.log cutoff :=
    (le_of_lt hlogThree).trans hlogMono
  have hpowNonneg : 0 ≤ (cutoff : ℝ) ^ (-(3 : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg cutoff) _
  have hconstant := nativeDerivativeTailConstant_nonneg hcamera t
  have htail := deriv_along_nativeLine_tail_le (cutoff := cutoff)
    hcamera (by omega) t
  calc
    ‖deriv (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) t -
        deriv (fun u : ℝ =>
          finiteBracketCharacteristic camera cutoff (nativeLine u)) t‖ ≤
        nativeDerivativeTailConstant camera t *
          ((2 / 3 : ℝ) * Real.log cutoff + 10 / 9) *
            (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := htail
    _ ≤ nativeDerivativeTailConstant camera t *
          ((16 / 9 : ℝ) * Real.log cutoff) *
            (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
      gcongr
      linarith
    _ = K * ‖(cutoff : ℝ) ^ (-(3 : ℝ) / 2) * Real.log cutoff‖ := by
      have hcutoffOne : (1 : ℝ) ≤ cutoff := by exact_mod_cast (by omega : 1 ≤ cutoff)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpowNonneg
        (Real.log_nonneg hcutoffOne))]
      dsimp [K]
      ring

end

end NativeCarrySpectralWeyl.Camera
