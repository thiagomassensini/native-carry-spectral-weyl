import NativeCarrySpectralWeyl.Camera.DerivativeTail
import Mathlib.Analysis.Complex.Liouville

/-!
# Higher native-line derivative tails

The source notes assert that every fixed derivative order costs one logarithm:

`∂ₜ^k (χ_b - χ_{b,M}) = O(M⁻³ᐟ² log(M)^k)`.

The proof below keeps the centered-second-difference cancellation intact.  It
first extends the quantitative order-zero estimate to a small complex
neighborhood of the native line.  Cauchy's estimate on a disc whose radius is
`1 / log M` then supplies the `k` logarithmic factors without expanding the
`k`-th derivative of every summand.
-/

open scoped BigOperators
open Set
open Filter

namespace NativeCarrySpectralWeyl.Camera

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- Shifted real-power weight used by the off-line tail estimate. -/
def shiftedRpowWeight (exponent : ℝ) (index : ℕ) : ℝ :=
  (((index + 1 : ℕ) : ℝ) ^ exponent)

theorem shiftedRpowWeight_summable {exponent : ℝ} (hexponent : exponent < -1) :
    Summable (shiftedRpowWeight exponent) := by
  have hbase : Summable
      (fun index : ℕ => (((index + 1 : ℕ) : ℝ) ^ exponent)) := by
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hexponent)
  exact hbase

/-- Integral-test bound for a general decreasing shifted real power. -/
theorem shiftedRpowWeight_tsum_nat_add_le {exponent : ℝ} {cutoff : ℕ}
    (hexponent : exponent < -1) (hcutoff : 1 ≤ cutoff) :
    (∑' index : ℕ, shiftedRpowWeight exponent (index + cutoff)) ≤
      (cutoff : ℝ) ^ (exponent + 1) / (-exponent - 1) := by
  let f : ℝ → ℝ := fun x => x ^ exponent
  have hcutoffPos : (0 : ℝ) < cutoff := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hcutoff)
  have hexponentNonpos : exponent ≤ 0 := by linarith
  have hanti : AntitoneOn f (Ici (cutoff : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hexponentNonpos).mono
    intro x hx
    exact hcutoffPos.trans_le hx
  have hint : MeasureTheory.IntegrableOn f (Ioi (cutoff : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hexponent hcutoffPos
  have hnonneg : ∀ x ∈ Ioi (cutoff : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg (hcutoffPos.trans hx).le _
  have h := hanti.tsum_comp_add_le_integral cutoff hint hnonneg
  rw [integral_Ioi_rpow_of_lt hexponent hcutoffPos] at h
  calc
    (∑' index : ℕ, shiftedRpowWeight exponent (index + cutoff)) =
        ∑' index : ℕ, f (((index + cutoff + 1 : ℕ) : ℝ)) := by
      apply tsum_congr
      intro index
      simp only [shiftedRpowWeight, f, Nat.cast_add, Nat.cast_one]
    _ ≤ -((cutoff : ℝ) ^ (exponent + 1)) / (exponent + 1) := h
    _ = (cutoff : ℝ) ^ (exponent + 1) / (-exponent - 1) := by
      rw [show -exponent - 1 = -(exponent + 1) by ring, div_neg]
      exact neg_div _ _

/-- The compact-normal majorant factors into its camera coefficient and one
shifted real-power weight. -/
theorem centerBracketMajorant_eq_cameraRadiusSqSum (camera index : ℕ)
    (sigma bound : ℝ) :
    centerBracketMajorant camera sigma bound index =
      (bound * cameraRadiusSqSum camera) *
        shiftedRpowWeight (-sigma - 2) index := by
  unfold centerBracketMajorant cameraRadiusSqSum radiusBracketMajorant
    shiftedRpowWeight
  by_cases h2 : camera = 2
  · subst camera
    simp only [if_pos]
    ring
  · simp only [h2, if_false]
    rw [← Finset.mul_sum]
    ring

/-- The infinite-minus-finite characteristic is the shifted tail throughout
the full bracket domain, not only on the native line. -/
theorem bracketCharacteristic_sub_finite_eq_tsum_nat_add_of_mem_domain
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    bracketCharacteristic camera s - finiteBracketCharacteristic camera cutoff s =
      ∑' index : ℕ, centerBracketTerm camera s (index + cutoff) := by
  have hsum := centerBracketTerm_summable hcamera (s := s) (by
    simpa [bracketDomain] using hs)
  have hsplit := hsum.sum_add_tsum_nat_add cutoff
  unfold bracketCharacteristic finiteBracketCharacteristic
  rw [← hsplit]
  ring

/-- Explicit order-zero tail estimate at any point whose real part and
quadratic exponent coefficient have fixed lower/upper bounds. -/
theorem bracketCharacteristic_tail_le_of_re_ge {camera cutoff : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : 1 ≤ cutoff) {s : ℂ} {sigma bound : ℝ}
    (hdomain : -1 < sigma) (hsigma : sigma ≤ s.re)
    (hbound : ‖s * (s + 1)‖ ≤ bound) :
    ‖bracketCharacteristic camera s - finiteBracketCharacteristic camera cutoff s‖ ≤
      (bound * cameraRadiusSqSum camera) *
        ((cutoff : ℝ) ^ (-sigma - 1) / (sigma + 1)) := by
  have hs : s ∈ bracketDomain := by
    simp only [bracketDomain, mem_setOf_eq]
    exact hdomain.trans_le hsigma
  rw [bracketCharacteristic_sub_finite_eq_tsum_nat_add_of_mem_domain hcamera hs]
  have hshiftInjective : Function.Injective (fun index : ℕ => index + cutoff) := by
    intro left right h
    exact Nat.add_right_cancel h
  have hnormSummable : Summable (fun index : ℕ =>
      ‖centerBracketTerm camera s (index + cutoff)‖) :=
    (centerBracketTerm_norm_summable hcamera (hdomain.trans_le hsigma))
      |>.comp_injective hshiftInjective
  have hcoefficientNonneg : 0 ≤ bound * cameraRadiusSqSum camera := by
    apply mul_nonneg
    · exact (norm_nonneg (s * (s + 1))).trans hbound
    · exact cameraRadiusSqSum_nonneg camera
  have hexponent : -sigma - 2 < -1 := by linarith
  calc
    ‖∑' index : ℕ, centerBracketTerm camera s (index + cutoff)‖ ≤
        ∑' index : ℕ, ‖centerBracketTerm camera s (index + cutoff)‖ :=
      norm_tsum_le_tsum_norm hnormSummable
    _ ≤ ∑' index : ℕ,
        (bound * cameraRadiusSqSum camera) *
          shiftedRpowWeight (-sigma - 2) (index + cutoff) := by
      apply Summable.tsum_le_tsum
      · intro index
        rw [← centerBracketMajorant_eq_cameraRadiusSqSum]
        exact centerBracketTerm_norm_le_majorant hcamera hsigma hbound hdomain _
      · exact hnormSummable
      · exact ((shiftedRpowWeight_summable hexponent).comp_injective hshiftInjective).mul_left _
    _ = (bound * cameraRadiusSqSum camera) *
        ∑' index : ℕ, shiftedRpowWeight (-sigma - 2) (index + cutoff) := by
      rw [tsum_mul_left]
    _ ≤ (bound * cameraRadiusSqSum camera) *
        ((cutoff : ℝ) ^ ((-sigma - 2) + 1) / (-(-sigma - 2) - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (shiftedRpowWeight_tsum_nat_add_le hexponent hcutoff)
        hcoefficientNonneg
    _ = (bound * cameraRadiusSqSum camera) *
        ((cutoff : ℝ) ^ (-sigma - 1) / (sigma + 1)) := by
      rw [show (-sigma - 2) + 1 = -sigma - 1 by ring,
        show -(-sigma - 2) - 1 = sigma + 1 by ring]

/-- Radius of the Cauchy disc used at cutoff `M`. -/
def higherDerivativeCauchyRadius (cutoff : ℕ) : ℝ :=
  (Real.log (cutoff : ℝ))⁻¹

/-- A cutoff-independent order-zero bound on the dynamic Cauchy circle. -/
def higherDerivativeCircleConstant (camera : ℕ) (t : ℝ) : ℝ :=
  ((‖nativeLine t‖ + 1 / 2) * (‖nativeLine t + 1‖ + 1 / 2) *
      cameraRadiusSqSum camera) * Real.exp 1

theorem higherDerivativeCircleConstant_nonneg (camera : ℕ) (t : ℝ) :
    0 ≤ higherDerivativeCircleConstant camera t := by
  unfold higherDerivativeCircleConstant
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg <;> positivity
    · exact cameraRadiusSqSum_nonneg camera
  · exact (Real.exp_pos 1).le

private theorem higherDerivative_cutoff_facts {cutoff : ℕ}
    (hcutoff : Real.exp 2 ≤ (cutoff : ℝ)) :
    0 < (cutoff : ℝ) ∧
      2 ≤ Real.log (cutoff : ℝ) ∧
      0 < higherDerivativeCauchyRadius cutoff ∧
      higherDerivativeCauchyRadius cutoff ≤ 1 / 2 := by
  have hcutoffPos : 0 < (cutoff : ℝ) := (Real.exp_pos 2).trans_le hcutoff
  have hlog : 2 ≤ Real.log (cutoff : ℝ) :=
    (Real.le_log_iff_exp_le hcutoffPos).mpr hcutoff
  have hlogPos : 0 < Real.log (cutoff : ℝ) := by linarith
  have hradiusPos : 0 < higherDerivativeCauchyRadius cutoff := by
    simpa [higherDerivativeCauchyRadius] using inv_pos.mpr hlogPos
  have hradiusLe : higherDerivativeCauchyRadius cutoff ≤ 1 / 2 := by
    rw [higherDerivativeCauchyRadius]
    simpa [one_div] using
      (inv_le_inv₀ hlogPos (by norm_num : (0 : ℝ) < 2)).mpr hlog
  exact ⟨hcutoffPos, hlog, hradiusPos, hradiusLe⟩

private theorem nativeLine_closedBall_subset_bracketDomain {cutoff : ℕ} (t : ℝ)
    (hcutoff : Real.exp 2 ≤ (cutoff : ℝ)) :
    Metric.closedBall (nativeLine t) (higherDerivativeCauchyRadius cutoff) ⊆
      bracketDomain := by
  rcases higherDerivative_cutoff_facts hcutoff with
    ⟨_hcutoffPos, _hlog, _hradiusPos, hradiusLe⟩
  intro z hz
  have hnorm : ‖z - nativeLine t‖ ≤ higherDerivativeCauchyRadius cutoff := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have habs : |(z - nativeLine t).re| ≤
      higherDerivativeCauchyRadius cutoff :=
    (Complex.abs_re_le_norm _).trans hnorm
  have hre : (1 / 2 : ℝ) - higherDerivativeCauchyRadius cutoff ≤ z.re := by
    have hleft := (abs_le.mp habs).1
    rw [Complex.sub_re, nativeLine_re] at hleft
    linarith
  simp only [bracketDomain, mem_setOf_eq]
  have hsigmaNonneg : 0 ≤ (1 / 2 : ℝ) - higherDerivativeCauchyRadius cutoff := by
    linarith
  linarith

/-- Uniform order-zero remainder bound on the dynamic Cauchy circle. -/
theorem bracketCharacteristic_dynamic_circle_tail_le {camera cutoff : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : Real.exp 2 ≤ (cutoff : ℝ)) (t : ℝ)
    {z : ℂ} (hz : z ∈ Metric.sphere (nativeLine t)
      (higherDerivativeCauchyRadius cutoff)) :
    ‖bracketCharacteristic camera z - finiteBracketCharacteristic camera cutoff z‖ ≤
      higherDerivativeCircleConstant camera t *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
  rcases higherDerivative_cutoff_facts hcutoff with
    ⟨hcutoffPos, hlog, hradiusPos, hradiusLe⟩
  let radius := higherDerivativeCauchyRadius cutoff
  let sigma : ℝ := 1 / 2 - radius
  let bound : ℝ :=
    (‖nativeLine t‖ + 1 / 2) * (‖nativeLine t + 1‖ + 1 / 2)
  have hnorm : ‖z - nativeLine t‖ = radius := by
    simpa only [Metric.mem_sphere, dist_eq_norm, radius] using hz
  have habs : |(z - nativeLine t).re| ≤ radius :=
    (Complex.abs_re_le_norm _).trans_eq hnorm
  have hsigma : sigma ≤ z.re := by
    have hleft := (abs_le.mp habs).1
    rw [Complex.sub_re, nativeLine_re] at hleft
    dsimp [sigma]
    linarith
  have hdomain : -1 < sigma := by
    dsimp [sigma, radius]
    linarith
  have hnormZ : ‖z‖ ≤ ‖nativeLine t‖ + 1 / 2 := by
    calc
      ‖z‖ = ‖(z - nativeLine t) + nativeLine t‖ := by ring_nf
      _ ≤ ‖z - nativeLine t‖ + ‖nativeLine t‖ := norm_add_le _ _
      _ ≤ ‖nativeLine t‖ + 1 / 2 := by rw [hnorm]; linarith
  have hnormZOne : ‖z + 1‖ ≤ ‖nativeLine t + 1‖ + 1 / 2 := by
    calc
      ‖z + 1‖ = ‖(z - nativeLine t) + (nativeLine t + 1)‖ := by ring_nf
      _ ≤ ‖z - nativeLine t‖ + ‖nativeLine t + 1‖ := norm_add_le _ _
      _ ≤ ‖nativeLine t + 1‖ + 1 / 2 := by rw [hnorm]; linarith
  have hbound : ‖z * (z + 1)‖ ≤ bound := by
    rw [norm_mul]
    dsimp [bound]
    gcongr
  have hcutoffOne : 1 ≤ cutoff := by
    have hone : (1 : ℝ) < Real.exp 2 :=
      Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)
    have honeNat : 1 < cutoff := by exact_mod_cast (hone.trans_le hcutoff)
    omega
  have htail := bracketCharacteristic_tail_le_of_re_ge hcamera hcutoffOne
    hdomain hsigma hbound
  have hboundNonneg : 0 ≤ bound := by dsimp [bound]; positivity
  have hcoefficientNonneg : 0 ≤ bound * cameraRadiusSqSum camera :=
    mul_nonneg hboundNonneg (cameraRadiusSqSum_nonneg camera)
  have hdenom : 1 ≤ sigma + 1 := by
    dsimp [sigma, radius]
    linarith
  have hpowerNonneg : 0 ≤ (cutoff : ℝ) ^ (-sigma - 1) :=
    Real.rpow_nonneg hcutoffPos.le _
  have hdiv : (cutoff : ℝ) ^ (-sigma - 1) / (sigma + 1) ≤
      (cutoff : ℝ) ^ (-sigma - 1) := by
    exact div_le_self hpowerNonneg hdenom
  calc
    ‖bracketCharacteristic camera z - finiteBracketCharacteristic camera cutoff z‖ ≤
        (bound * cameraRadiusSqSum camera) *
          ((cutoff : ℝ) ^ (-sigma - 1) / (sigma + 1)) := htail
    _ ≤ (bound * cameraRadiusSqSum camera) *
          (cutoff : ℝ) ^ (-sigma - 1) :=
      mul_le_mul_of_nonneg_left hdiv hcoefficientNonneg
    _ = (bound * cameraRadiusSqSum camera) *
          ((cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
            (cutoff : ℝ) ^ radius) := by
      rw [← Real.rpow_add hcutoffPos]
      congr 2
      dsimp [sigma]
      ring
    _ = (bound * cameraRadiusSqSum camera) *
          ((cutoff : ℝ) ^ (-(3 : ℝ) / 2) * Real.exp 1) := by
      rw [show radius = (Real.log (cutoff : ℝ))⁻¹ by rfl]
      rw [Real.rpow_inv_log hcutoffPos (by
        have hone : (1 : ℝ) < Real.exp 2 := by
          exact Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)
        nlinarith)]
    _ = higherDerivativeCircleConstant camera t *
          (cutoff : ℝ) ^ (-(3 : ℝ) / 2) := by
      dsimp [higherDerivativeCircleConstant, bound]
      ring

/-- Cauchy's estimate converts the dynamic-circle bound into the claimed
`log(cutoff)^order` loss for every complex derivative order. -/
theorem iteratedDeriv_characteristicTail_nativeLine_le {camera cutoff order : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : Real.exp 2 ≤ (cutoff : ℝ)) (t : ℝ) :
    ‖iteratedDeriv order
        (fun s : ℂ => bracketCharacteristic camera s -
          finiteBracketCharacteristic camera cutoff s)
        (nativeLine t)‖ ≤
      (order.factorial * higherDerivativeCircleConstant camera t) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (cutoff : ℝ)) ^ order := by
  rcases higherDerivative_cutoff_facts hcutoff with
    ⟨_hcutoffPos, _hlog, hradiusPos, _hradiusLe⟩
  have hdiff : DifferentiableOn ℂ
      (fun s : ℂ => bracketCharacteristic camera s -
        finiteBracketCharacteristic camera cutoff s) bracketDomain :=
    (bracketCharacteristic_differentiableOn hcamera).sub
      (finiteBracketCharacteristic_differentiable hcamera cutoff).differentiableOn
  have hdiffCl : DiffContOnCl ℂ
      (fun s : ℂ => bracketCharacteristic camera s -
        finiteBracketCharacteristic camera cutoff s)
      (Metric.ball (nativeLine t) (higherDerivativeCauchyRadius cutoff)) :=
    hdiff.diffContOnCl_ball (nativeLine_closedBall_subset_bracketDomain t hcutoff)
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    order hradiusPos hdiffCl
    (fun z hz => bracketCharacteristic_dynamic_circle_tail_le hcamera hcutoff t hz)
  calc
    ‖iteratedDeriv order
        (fun s : ℂ => bracketCharacteristic camera s -
          finiteBracketCharacteristic camera cutoff s)
        (nativeLine t)‖ ≤
      order.factorial *
          (higherDerivativeCircleConstant camera t *
            (cutoff : ℝ) ^ (-(3 : ℝ) / 2)) /
        higherDerivativeCauchyRadius cutoff ^ order := hcauchy
    _ = (order.factorial * higherDerivativeCircleConstant camera t) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (cutoff : ℝ)) ^ order := by
      simp only [higherDerivativeCauchyRadius, inv_pow, div_inv_eq_mul]
      ring

/-- Difference form of the arbitrary-order complex derivative tail. -/
theorem iteratedDeriv_bracketCharacteristic_nativeLine_tail_le
    {camera cutoff order : ℕ} (hcamera : 2 ≤ camera)
    (hcutoff : Real.exp 2 ≤ (cutoff : ℝ)) (t : ℝ) :
    ‖iteratedDeriv order (bracketCharacteristic camera) (nativeLine t) -
        iteratedDeriv order (finiteBracketCharacteristic camera cutoff)
          (nativeLine t)‖ ≤
      (order.factorial * higherDerivativeCircleConstant camera t) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (cutoff : ℝ)) ^ order := by
  have hdomain : nativeLine t ∈ bracketDomain := by
    simp [bracketDomain]
    norm_num
  have hbracketCont : ContDiffAt ℂ order (bracketCharacteristic camera)
      (nativeLine t) :=
    ((bracketCharacteristic_differentiableOn hcamera).contDiffOn
      isOpen_bracketDomain).contDiffAt (isOpen_bracketDomain.mem_nhds hdomain)
  have hfiniteCont : ContDiffAt ℂ order
      (finiteBracketCharacteristic camera cutoff) (nativeLine t) :=
    (finiteBracketCharacteristic_differentiable hcamera cutoff).contDiff.contDiffAt
  rw [← iteratedDeriv_sub hbracketCont hfiniteCont]
  exact iteratedDeriv_characteristicTail_nativeLine_le hcamera hcutoff t

/-- Asymptotic form of the arbitrary-order complex derivative theorem.  The
order is fixed while the literal center-block cutoff tends to infinity. -/
theorem iteratedDeriv_bracketCharacteristic_nativeLine_tail_isBigO
    {camera : ℕ} (hcamera : 2 ≤ camera) (order : ℕ) (t : ℝ) :
    (fun cutoff : ℕ =>
      iteratedDeriv order (bracketCharacteristic camera) (nativeLine t) -
        iteratedDeriv order (finiteBracketCharacteristic camera cutoff)
          (nativeLine t)) =O[atTop]
      (fun cutoff : ℕ =>
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (cutoff : ℝ)) ^ order) := by
  apply Asymptotics.IsBigO.of_bound
    (order.factorial * higherDerivativeCircleConstant camera t)
  have heventually : ∀ᶠ cutoff : ℕ in atTop,
      Real.exp 2 ≤ (cutoff : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 2))
  filter_upwards [heventually] with cutoff hcutoff
  have htail := iteratedDeriv_bracketCharacteristic_nativeLine_tail_le
    hcamera hcutoff t (order := order)
  have hlogNonneg : 0 ≤ Real.log (cutoff : ℝ) := by
    have hcutoffPos : 0 < (cutoff : ℝ) := (Real.exp_pos 2).trans_le hcutoff
    have hlog : 2 ≤ Real.log (cutoff : ℝ) :=
      (Real.le_log_iff_exp_le hcutoffPos).mpr hcutoff
    linarith
  have htargetNonneg : 0 ≤
      (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
        (Real.log (cutoff : ℝ)) ^ order :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg cutoff) _) (pow_nonneg hlogNonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg htargetNonneg, mul_assoc] using htail

/-! ## Arbitrary derivatives in the native-line parameter -/

/-- One real derivative along `t ↦ 1/2 + it` is one complex derivative followed
by multiplication by `I`. -/
theorem deriv_comp_nativeLine_eq {f : ℂ → ℂ} {t : ℝ}
    (hf : DifferentiableAt ℂ f (nativeLine t)) :
    deriv (fun u : ℝ => f (nativeLine u)) t =
      deriv f (nativeLine t) * Complex.I := by
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
  have hcomp := hf.hasDerivAt.scomp t hline
  have hd := hcomp.deriv
  change deriv (f ∘ nativeLine) t = _
  simpa only [smul_eq_mul, zero_add, mul_one, mul_comm] using hd

private theorem differentiableOn_iteratedDeriv_of_differentiableOn
    {f : ℂ → ℂ} {domain : Set ℂ} (hf : DifferentiableOn ℂ f domain)
    (hdomain : IsOpen domain) (order : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv order f) domain := by
  induction order with
  | zero => simpa using hf
  | succ order ih =>
      rw [show order + 1 = Nat.succ order by omega, iteratedDeriv_succ]
      exact ih.deriv hdomain

/-- Exact chain rule for every derivative order along the native line. -/
theorem iteratedDeriv_comp_nativeLine_eq {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f bracketDomain) (order : ℕ) (t : ℝ) :
    iteratedDeriv order (fun u : ℝ => f (nativeLine u)) t =
      iteratedDeriv order f (nativeLine t) * Complex.I ^ order := by
  induction order generalizing t with
  | zero => simp
  | succ order ih =>
      have hfunction :
          iteratedDeriv order (fun u : ℝ => f (nativeLine u)) =
            fun u : ℝ => iteratedDeriv order f (nativeLine u) *
              Complex.I ^ order := by
        funext u
        exact ih u
      have hdomain : nativeLine t ∈ bracketDomain := by
        simp [bracketDomain]
        norm_num
      have houter : DifferentiableAt ℂ (iteratedDeriv order f) (nativeLine t) :=
        (differentiableOn_iteratedDeriv_of_differentiableOn hf
          isOpen_bracketDomain order).differentiableAt
            (isOpen_bracketDomain.mem_nhds hdomain)
      rw [iteratedDeriv_succ, hfunction,
        deriv_mul_const_field, deriv_comp_nativeLine_eq houter, ← iteratedDeriv_succ]
      rw [pow_succ]
      ring

/-- Exact `I^order` transport for the infinite bracket characteristic. -/
theorem iteratedDeriv_bracketCharacteristic_along_nativeLine {camera : ℕ}
    (hcamera : 2 ≤ camera) (order : ℕ) (t : ℝ) :
    iteratedDeriv order
        (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) t =
      iteratedDeriv order (bracketCharacteristic camera) (nativeLine t) *
        Complex.I ^ order :=
  iteratedDeriv_comp_nativeLine_eq
    (bracketCharacteristic_differentiableOn hcamera) order t

/-- Exact `I^order` transport for every finite-cutoff characteristic. -/
theorem iteratedDeriv_finiteBracketCharacteristic_along_nativeLine {camera : ℕ}
    (hcamera : 2 ≤ camera) (cutoff order : ℕ) (t : ℝ) :
    iteratedDeriv order
        (fun u : ℝ => finiteBracketCharacteristic camera cutoff (nativeLine u)) t =
      iteratedDeriv order (finiteBracketCharacteristic camera cutoff) (nativeLine t) *
        Complex.I ^ order :=
  iteratedDeriv_comp_nativeLine_eq
    (finiteBracketCharacteristic_differentiable hcamera cutoff).differentiableOn order t

/-- Source-form estimate for every fixed real derivative order in the native
parameter `t`. -/
theorem iteratedDeriv_along_nativeLine_tail_le {camera cutoff order : ℕ}
    (hcamera : 2 ≤ camera) (hcutoff : Real.exp 2 ≤ (cutoff : ℝ)) (t : ℝ) :
    ‖iteratedDeriv order
          (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) t -
        iteratedDeriv order
          (fun u : ℝ => finiteBracketCharacteristic camera cutoff (nativeLine u)) t‖ ≤
      (order.factorial * higherDerivativeCircleConstant camera t) *
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (cutoff : ℝ)) ^ order := by
  rw [iteratedDeriv_bracketCharacteristic_along_nativeLine hcamera,
    iteratedDeriv_finiteBracketCharacteristic_along_nativeLine hcamera]
  rw [← sub_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one]
  exact iteratedDeriv_bracketCharacteristic_nativeLine_tail_le
    hcamera hcutoff t

/-- The statement from the source notes: for every fixed `order`, the actual
native-line `t`-derivative remainder is
`O(cutoff⁻³ᐟ² log(cutoff)^order)`. -/
theorem iteratedDeriv_along_nativeLine_tail_isBigO {camera : ℕ}
    (hcamera : 2 ≤ camera) (order : ℕ) (t : ℝ) :
    (fun cutoff : ℕ =>
      iteratedDeriv order
          (fun u : ℝ => bracketCharacteristic camera (nativeLine u)) t -
        iteratedDeriv order
          (fun u : ℝ => finiteBracketCharacteristic camera cutoff (nativeLine u)) t) =O[atTop]
      (fun cutoff : ℕ =>
        (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
          (Real.log (cutoff : ℝ)) ^ order) := by
  apply Asymptotics.IsBigO.of_bound
    (order.factorial * higherDerivativeCircleConstant camera t)
  have heventually : ∀ᶠ cutoff : ℕ in atTop,
      Real.exp 2 ≤ (cutoff : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp 2))
  filter_upwards [heventually] with cutoff hcutoff
  have htail := iteratedDeriv_along_nativeLine_tail_le
    hcamera hcutoff t (order := order)
  have hcutoffPos : 0 < (cutoff : ℝ) := (Real.exp_pos 2).trans_le hcutoff
  have hlogNonneg : 0 ≤ Real.log (cutoff : ℝ) := by
    have hlog : 2 ≤ Real.log (cutoff : ℝ) :=
      (Real.le_log_iff_exp_le hcutoffPos).mpr hcutoff
    linarith
  have htargetNonneg : 0 ≤
      (cutoff : ℝ) ^ (-(3 : ℝ) / 2) *
        (Real.log (cutoff : ℝ)) ^ order :=
    mul_nonneg (Real.rpow_nonneg hcutoffPos.le _) (pow_nonneg hlogNonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg htargetNonneg, mul_assoc] using htail

end

end NativeCarrySpectralWeyl.Camera
