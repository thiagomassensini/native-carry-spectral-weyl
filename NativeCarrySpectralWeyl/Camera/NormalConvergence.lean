import NativeCarrySpectralWeyl.Camera.BracketSeries
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Normal convergence of native camera bracket characteristics

For each fixed supported camera, the center-block series converges normally on
`re s > -1`.  Consequently the finite characteristics converge locally
uniformly there and the infinite characteristic is holomorphic.

This module does not identify the bracket characteristic with the periodic
profile Dirichlet series.  That comparison belongs to the absolutely
convergent half-plane `re s > 1` and remains a separate theorem layer.
-/

open scoped BigOperators
open Set

namespace NativeCarrySpectralWeyl.Camera

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- Natural holomorphy domain of the bracket characteristics. -/
def bracketDomain : Set ℂ := {s | -1 < s.re}

theorem isOpen_bracketDomain : IsOpen bracketDomain := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- A compact-uniform version of the individual bracket estimate. -/
theorem centeredBracketTerm_norm_le_uniform
    {s : ℂ} {sigma bound : ℝ} {center radius index : ℕ}
    (hsigma : sigma ≤ s.re) (hbound : ‖s * (s + 1)‖ ≤ bound)
    (hradius : radius < center) (hlower : index + 1 ≤ center - radius)
    (hdomain : -1 < sigma) :
    ‖centeredBracketTerm s center radius‖ ≤
      (bound * ((index + 1 : ℕ) : ℝ) ^ (-sigma - 2)) * (radius : ℝ) ^ 2 := by
  have hterm := centeredBracketTerm_norm_le s hradius (hdomain.trans_le hsigma)
  have hone : (1 : ℝ) ≤ ((center - radius : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : center - radius ≠ 0))
  have hleg : ((index + 1 : ℕ) : ℝ) ≤ ((center - radius : ℕ) : ℝ) := by
    exact_mod_cast hlower
  have hexponent : -s.re - 2 ≤ -sigma - 2 := by linarith
  have hp₁ : ((center - radius : ℕ) : ℝ) ^ (-s.re - 2) ≤
      ((center - radius : ℕ) : ℝ) ^ (-sigma - 2) :=
    Real.rpow_le_rpow_of_exponent_le hone hexponent
  have hp₂ : ((center - radius : ℕ) : ℝ) ^ (-sigma - 2) ≤
      ((index + 1 : ℕ) : ℝ) ^ (-sigma - 2) := by
    apply Real.rpow_le_rpow_of_nonpos (x := ((index + 1 : ℕ) : ℝ))
      (y := ((center - radius : ℕ) : ℝ))
    · positivity
    · exact hleg
    · linarith
  have hp := hp₁.trans hp₂
  have hbound_nonneg : 0 ≤ bound := (norm_nonneg (s * (s + 1))).trans hbound
  calc
    ‖centeredBracketTerm s center radius‖ ≤
        (‖s * (s + 1)‖ * ((center - radius : ℕ) : ℝ) ^ (-s.re - 2)) *
          (radius : ℝ) ^ 2 := hterm
    _ ≤ (bound * ((index + 1 : ℕ) : ℝ) ^ (-sigma - 2)) * (radius : ℝ) ^ 2 := by
      gcongr

/-- Per-radius Weierstrass majorant on a compact subset of the bracket domain. -/
def radiusBracketMajorant (sigma bound : ℝ) (radius index : ℕ) : ℝ :=
  (bound * ((index + 1 : ℕ) : ℝ) ^ (-sigma - 2)) * (radius : ℝ) ^ 2

/-- Sum of the radius majorants in one camera block. -/
def centerBracketMajorant (camera : ℕ) (sigma bound : ℝ) (index : ℕ) : ℝ :=
  if camera = 2 then radiusBracketMajorant sigma bound 1 index
  else ∑ radius ∈ radiusSet camera, radiusBracketMajorant sigma bound radius index

theorem radiusBracketMajorant_summable {sigma bound : ℝ} (hsigma : -1 < sigma)
    (radius : ℕ) : Summable (radiusBracketMajorant sigma bound radius) := by
  have hp : -sigma - 2 < -1 := by linarith
  have hbase : Summable (fun index : ℕ => ((index + 1 : ℕ) : ℝ) ^ (-sigma - 2)) := by
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  have heq : radiusBracketMajorant sigma bound radius =
      fun index => (bound * (radius : ℝ) ^ 2) *
        ((index + 1 : ℕ) : ℝ) ^ (-sigma - 2) := by
    funext index
    simp only [radiusBracketMajorant]
    ring
  rw [heq]
  exact hbase.mul_left _

theorem centerBracketMajorant_summable {camera : ℕ} {sigma bound : ℝ}
    (hsigma : -1 < sigma) : Summable (centerBracketMajorant camera sigma bound) := by
  by_cases h2 : camera = 2
  · subst camera
    change Summable (radiusBracketMajorant sigma bound 1)
    exact radiusBracketMajorant_summable hsigma 1
  · change Summable (fun index => if camera = 2 then _ else _)
    simp only [h2, if_false]
    exact summable_sum fun radius _ =>
      radiusBracketMajorant_summable (bound := bound) hsigma radius

theorem centerBracketTerm_norm_le_majorant {camera : ℕ} (hcamera : 2 ≤ camera)
    {s : ℂ} {sigma bound : ℝ} (hsigma : sigma ≤ s.re)
    (hbound : ‖s * (s + 1)‖ ≤ bound) (hdomain : -1 < sigma) (index : ℕ) :
    ‖centerBracketTerm camera s index‖ ≤ centerBracketMajorant camera sigma bound index := by
  by_cases h2 : camera = 2
  · subst camera
    simp only [centerBracketTerm, centerBracketMajorant, if_pos, radiusBracketMajorant]
    apply centeredBracketTerm_norm_le_uniform hsigma hbound
    · rw [alignedCenter_eq_cameraSlope_mul]
      simp only [cameraSlope_two]
      omega
    · exact c2_index_succ_le_alignedCenter_sub index
    · exact hdomain
  · have hcamera3 : 3 ≤ camera := by omega
    simp only [centerBracketTerm, centerBracketMajorant, h2, if_false]
    calc
      ‖∑ radius ∈ radiusSet camera,
          centeredBracketTerm s (alignedCenter camera index) radius‖ ≤
          ∑ radius ∈ radiusSet camera,
            ‖centeredBracketTerm s (alignedCenter camera index) radius‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ radius ∈ radiusSet camera,
          radiusBracketMajorant sigma bound radius index := by
        apply Finset.sum_le_sum
        intro radius hradius
        apply centeredBracketTerm_norm_le_uniform hsigma hbound
        · have hlower := natural_index_succ_le_alignedCenter_sub hcamera3 hradius
            (index := index)
          omega
        · exact natural_index_succ_le_alignedCenter_sub hcamera3 hradius
        · exact hdomain

/-- The center-block series converges normally on the full bracket domain. -/
theorem centerBracketTerm_summableLocallyUniformlyOn {camera : ℕ}
    (hcamera : 2 ≤ camera) :
    SummableLocallyUniformlyOn (fun index s => centerBracketTerm camera s index)
      bracketDomain := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_bracketDomain
  intro K hK hKcompact
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · subst K
    exact ⟨0, summable_zero, by simp⟩
  · obtain ⟨sigma, hsigmaDomain, hsigma⟩ :=
      hKcompact.exists_forall_le' Complex.continuous_re.continuousOn
        (fun s hs => by simpa [bracketDomain] using hK hs)
    have hcontinuous : Continuous (fun s : ℂ => ‖s * (s + 1)‖) := by fun_prop
    obtain ⟨smax, hsmax, hmax⟩ :=
      hKcompact.exists_isMaxOn hNonempty hcontinuous.continuousOn
    refine ⟨centerBracketMajorant camera sigma ‖smax * (smax + 1)‖,
      centerBracketMajorant_summable hsigmaDomain, ?_⟩
    intro index s hs
    exact centerBracketTerm_norm_le_majorant hcamera (hsigma s hs) (hmax hs)
      hsigmaDomain index

/-- A positive native sample is entire in the Dirichlet exponent. -/
theorem dirichletValue_differentiable {n : ℕ} (hn : 0 < n) :
    Differentiable ℂ (fun s => dirichletValue s n) := by
  unfold dirichletValue
  exact differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast hn.ne'))

/-- Every geometrically valid centered bracket is entire in the exponent. -/
theorem centeredBracketTerm_differentiable {center radius : ℕ}
    (hradius : radius < center) :
    Differentiable ℂ (fun s => centeredBracketTerm s center radius) := by
  have hleft : 0 < center - radius := Nat.sub_pos_of_lt hradius
  have hcenter : 0 < center := hleft.trans_le (Nat.sub_le center radius)
  have hright : 0 < center + radius := hcenter.trans_le (Nat.le_add_right center radius)
  exact ((dirichletValue_differentiable hleft).sub
    ((dirichletValue_differentiable hcenter).const_mul 2)).add
      (dirichletValue_differentiable hright)

/-- Every supported aligned center block is entire in the exponent. -/
theorem centerBracketTerm_differentiable {camera : ℕ} (hcamera : 2 ≤ camera)
    (index : ℕ) : Differentiable ℂ (fun s => centerBracketTerm camera s index) := by
  by_cases h2 : camera = 2
  · subst camera
    simp only [centerBracketTerm, if_pos]
    apply centeredBracketTerm_differentiable
    rw [alignedCenter_eq_cameraSlope_mul]
    simp only [cameraSlope_two]
    omega
  · have hcamera3 : 3 ≤ camera := by omega
    simp only [centerBracketTerm, h2, if_false]
    exact Differentiable.fun_sum fun radius hradius =>
      centeredBracketTerm_differentiable (by
        have hlower := natural_index_succ_le_alignedCenter_sub hcamera3 hradius
          (index := index)
        omega)

/-- The finite seed block of every supported camera is entire. -/
theorem seedDirichletTerm_differentiable {camera : ℕ} (hcamera : 2 ≤ camera) :
    Differentiable ℂ (fun s => seedDirichletTerm camera s) := by
  by_cases h2 : camera = 2
  · subst camera
    simp only [seedDirichletTerm, if_pos]
    exact dirichletValue_differentiable (by norm_num)
  · simp only [seedDirichletTerm, h2, if_false]
    exact Differentiable.fun_sum fun radius hradius =>
      dirichletValue_differentiable ((mem_radiusSet_iff.mp hradius).1.trans_lt' (by omega))

/-- Every finite bracket characteristic is entire. -/
theorem finiteBracketCharacteristic_differentiable {camera : ℕ}
    (hcamera : 2 ≤ camera) (cutoff : ℕ) :
    Differentiable ℂ (finiteBracketCharacteristic camera cutoff) := by
  exact (seedDirichletTerm_differentiable hcamera).add
    (Differentiable.fun_sum fun index _ => centerBracketTerm_differentiable hcamera index)

/-- The normally convergent infinite bracket characteristic is holomorphic on
its complete source domain. -/
theorem bracketCharacteristic_differentiableOn {camera : ℕ} (hcamera : 2 ≤ camera) :
    DifferentiableOn ℂ (bracketCharacteristic camera) bracketDomain := by
  have hsum : DifferentiableOn ℂ
      (fun s => ∑' index, centerBracketTerm camera s index) bracketDomain :=
    (centerBracketTerm_summableLocallyUniformlyOn hcamera).differentiableOn
      isOpen_bracketDomain (fun index s _ =>
        (centerBracketTerm_differentiable hcamera index) s)
  exact (seedDirichletTerm_differentiable hcamera).differentiableOn.add hsum

/-- Finite bracket characteristics converge locally uniformly to their infinite
counterpart throughout `re s > -1`. -/
theorem finiteBracketCharacteristic_tendstoLocallyUniformlyOn {camera : ℕ}
    (hcamera : 2 ≤ camera) :
    TendstoLocallyUniformlyOn
      (fun cutoff s => finiteBracketCharacteristic camera cutoff s)
      (bracketCharacteristic camera) Filter.atTop bracketDomain := by
  have hsum := (centerBracketTerm_summableLocallyUniformlyOn hcamera)
    |>.hasSumLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hseedUniform : TendstoUniformlyOn
      (fun (_cutoff : ℕ) (_s : ℂ) => seedDirichletTerm camera _s)
      (seedDirichletTerm camera) Filter.atTop bracketDomain := by
    intro entourage hentourage
    exact Filter.Eventually.of_forall fun _cutoff _s _hs =>
      refl_mem_uniformity hentourage
  have hseed := hseedUniform.tendstoLocallyUniformlyOn
  change TendstoLocallyUniformlyOn
    (fun cutoff s => seedDirichletTerm camera s +
      ∑ index ∈ Finset.range cutoff, centerBracketTerm camera s index)
    (fun s => seedDirichletTerm camera s +
      ∑' index, centerBracketTerm camera s index) Filter.atTop bracketDomain
  exact (hseed.add hsum).congr (fun _cutoff _s _hs => rfl)
    |>.congr_right (fun _s _hs => rfl)

end

end NativeCarrySpectralWeyl.Camera
