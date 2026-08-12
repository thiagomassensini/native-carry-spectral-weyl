import NativeCarrySpectralWeyl.Boundary.RiggedAngularOrbit
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closed logarithmic unrigging and the canonical rigged dual port

The weighted coordinates in `RiggedAngularOrbit` naturally support two
different maps, and keeping them separate is essential.

* The bounded rigging injection
  `Jx(n) = x(n) / (1 + log n)` has dense range.
* Its inverse is the maximal unrigging operator
  `Mx(n) = (1 + log n) x(n)` on the explicit domain
  `{x : ℓ² | ((1 + log n) x(n)) ∈ ℓ²}`.

The inverse is proved densely defined, closed and self-adjoint; its domain is
proper and invariant under the logarithmic angular evolution.  The critical
orbit is deliberately proved to lie outside this unrigging domain, since its
unrigged coordinates have harmonic energy.

The correct everywhere-defined port for the critical orbit is instead the
Fréchet--Riesz anti-linear isometric equivalence from the `H₋₁` coordinate
realization into the strong dual of the corresponding `H₁` test-coordinate
realization.  This canonical dual port contains the whole critical orbit and
is stronger than a merely closable map.

This module does not identify that canonical dual port with the
research-specific all-bases camera readout.  Constructing the latter still
requires a typed boundary synthesis supplied by the Green/Haar analysis.
-/

open scoped ENNReal InnerProductSpace lp
open scoped LinearPMap
open Set

noncomputable section

namespace NativeCarrySpectralWeyl.Boundary

/-- Positive logarithmic weight used to pass from the ambient `H₋₁`
coordinate realization to unweighted coordinates. -/
def logRiggingWeight (n : PNat) : ℝ :=
  1 + Real.log ((n : ℕ) : ℝ)

theorem logRiggingWeight_one_le (n : PNat) :
    1 ≤ logRiggingWeight n := by
  rw [logRiggingWeight]
  have hn : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast n.2
  linarith [Real.log_nonneg hn]

theorem logRiggingWeight_pos (n : PNat) :
    0 < logRiggingWeight n :=
  lt_of_lt_of_le zero_lt_one (logRiggingWeight_one_le n)

theorem logRiggingWeight_ne_zero (n : PNat) :
    logRiggingWeight n ≠ 0 :=
  (logRiggingWeight_pos n).ne'

private def logRiggingCoordinate (x : LogRiggedState) (n : PNat) : ℂ :=
  (((logRiggingWeight n)⁻¹ : ℝ) : ℂ) * x n

private theorem logRiggingCoordinate_energy_le (x : LogRiggedState)
    (n : PNat) :
    Complex.normSq (logRiggingCoordinate x n) ≤
      GreenFrame.Concrete.stateEnergy x n := by
  rw [logRiggingCoordinate, GreenFrame.Concrete.stateEnergy,
    Complex.normSq_mul, Complex.normSq_ofReal]
  have hw : 1 ≤ logRiggingWeight n := logRiggingWeight_one_le n
  have hinv : (logRiggingWeight n)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity)).2 hw
  have hinv_nonneg : 0 ≤ (logRiggingWeight n)⁻¹ := by positivity
  have hsquare : ((logRiggingWeight n)⁻¹) ^ 2 ≤ 1 := by nlinarith
  simpa only [pow_two, one_mul] using
    mul_le_mul_of_nonneg_right hsquare (Complex.normSq_nonneg (x n))

private def logRiggingValue (x : LogRiggedState) : LogRiggedState :=
  ⟨logRiggingCoordinate x, by
    apply memℓp_gen
    have hs : Summable (fun n : PNat =>
        Complex.normSq (logRiggingCoordinate x n)) :=
      Summable.of_nonneg_of_le
        (fun n => Complex.normSq_nonneg _)
        (logRiggingCoordinate_energy_le x)
        (GreenFrame.Concrete.stateEnergy_summable x)
    apply hs.congr
    intro n
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (logRiggingCoordinate x n)).symm⟩

@[simp] private theorem logRiggingValue_apply (x : LogRiggedState)
    (n : PNat) :
    logRiggingValue x n =
      (((logRiggingWeight n)⁻¹ : ℝ) : ℂ) * x n := rfl

private theorem logRiggingValue_add (x y : LogRiggedState) :
    logRiggingValue (x + y) = logRiggingValue x + logRiggingValue y := by
  apply lp.ext
  funext n
  simp [mul_add]

private theorem logRiggingValue_smul (c : ℂ) (x : LogRiggedState) :
    logRiggingValue (c • x) = c • logRiggingValue x := by
  apply lp.ext
  funext n
  simp [mul_left_comm]

private theorem logRiggingValue_norm_sq_le (x : LogRiggedState) :
    ‖logRiggingValue x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [← GreenFrame.Concrete.stateEnergy_tsum_eq_norm_sq,
    ← GreenFrame.Concrete.stateEnergy_tsum_eq_norm_sq]
  exact (GreenFrame.Concrete.stateEnergy_summable (logRiggingValue x)).tsum_le_tsum
    (logRiggingCoordinate_energy_le x)
    (GreenFrame.Concrete.stateEnergy_summable x)

private theorem logRiggingValue_norm_le (x : LogRiggedState) :
    ‖logRiggingValue x‖ ≤ ‖x‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (logRiggingValue_norm_sq_le x)

/-- Bounded logarithmic rigging map `J`, acting by division by
`1 + log n` on coordinates. -/
def logRigging : LogRiggedState →L[ℂ] LogRiggedState :=
  ({
    toFun := logRiggingValue
    map_add' := logRiggingValue_add
    map_smul' := logRiggingValue_smul
  } : LogRiggedState →ₗ[ℂ] LogRiggedState).mkContinuous 1 fun x => by
    change ‖logRiggingValue x‖ ≤ 1 * ‖x‖
    simpa using logRiggingValue_norm_le x

@[simp] theorem logRigging_apply (x : LogRiggedState) (n : PNat) :
    logRigging x n =
      (((logRiggingWeight n)⁻¹ : ℝ) : ℂ) * x n := rfl

theorem logRigging_injective : Function.Injective logRigging := by
  intro x y hxy
  apply lp.ext
  funext n
  have hn := congrArg (fun z : LogRiggedState => z n) hxy
  simp only [logRigging_apply] at hn
  exact mul_left_cancel₀ (by
    exact_mod_cast (inv_ne_zero (logRiggingWeight_ne_zero n))) hn

theorem logRigging_isSymmetric :
    LinearMap.IsSymmetric logRigging.toLinearMap := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ
      ((((logRiggingWeight n)⁻¹ : ℝ) : ℂ) * x n) (y n) =
    inner ℂ (x n)
      ((((logRiggingWeight n)⁻¹ : ℝ) : ℂ) * y n)
  simp
  ring

theorem logRigging_denseRange :
    Dense (LinearMap.range logRigging.toLinearMap : Set LogRiggedState) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  rw [← (LinearMap.range logRigging.toLinearMap).orthogonal_orthogonal_eq_closure]
  rw [logRigging_isSymmetric.orthogonal_range,
    LinearMap.ker_eq_bot.mpr logRigging_injective,
    Submodule.bot_orthogonal_eq_top]

/-- Explicit maximal domain on which multiplication by `1 + log n`
still has square-summable coordinates. -/
def logUnriggingDomain : Submodule ℂ LogRiggedState where
  carrier := {x | Memℓp (fun n : PNat =>
    ((logRiggingWeight n : ℝ) : ℂ) * x n) 2}
  zero_mem' := by
    change Memℓp (fun n : PNat =>
      ((logRiggingWeight n : ℝ) : ℂ) *
        ((0 : LogRiggedState) : PNat → ℂ) n) 2
    simpa only [lp.coeFn_zero, Pi.zero_apply, mul_zero] using
      (zero_mem_ℓp' : Memℓp (fun _ : PNat => (0 : ℂ)) 2)
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun n : PNat =>
      ((logRiggingWeight n : ℝ) : ℂ) * (x + y) n) 2
    have hsum := hx.add hy
    convert hsum using 1
    funext n
    simp [mul_add]
  smul_mem' := by
    intro c x hx
    change Memℓp (fun n : PNat =>
      ((logRiggingWeight n : ℝ) : ℂ) * (c • x) n) 2
    have hsmul := hx.const_mul c
    have heq :
        (fun n : PNat =>
          ((logRiggingWeight n : ℝ) : ℂ) * (c • x) n) =
        (fun n : PNat => c *
          (((logRiggingWeight n : ℝ) : ℂ) * x n)) := by
      funext n
      change ((logRiggingWeight n : ℝ) : ℂ) * (c * x n) =
        c * (((logRiggingWeight n : ℝ) : ℂ) * x n)
      ring
    rw [heq]
    exact hsmul

/-- The bounded rigging map as an everywhere-defined partial operator. -/
def logRiggingPMap : LogRiggedState →ₗ.[ℂ] LogRiggedState :=
  logRigging.toLinearMap.toPMap ⊤

@[simp] theorem logRiggingPMap_domain : logRiggingPMap.domain = ⊤ := rfl

@[simp] theorem logRiggingPMap_apply (x : logRiggingPMap.domain) :
    logRiggingPMap x = logRigging x := rfl

theorem logRiggingPMap_toFun_injective :
    Function.Injective logRiggingPMap.toFun := by
  intro x y hxy
  apply Subtype.ext
  apply logRigging_injective
  exact hxy

theorem logRiggingPMap_ker_eq_bot :
    LinearMap.ker logRiggingPMap.toFun = ⊥ :=
  LinearMap.ker_eq_bot.mpr logRiggingPMap_toFun_injective

theorem logRiggingPMap_range :
    LinearMap.range logRiggingPMap.toFun =
      LinearMap.range logRigging.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, by simp⟩, rfl⟩

private def logUnriggingValue (x : logUnriggingDomain) : LogRiggedState :=
  ⟨fun n : PNat => ((logRiggingWeight n : ℝ) : ℂ) * x.1 n, x.2⟩

@[simp] private theorem logUnriggingValue_apply
    (x : logUnriggingDomain) (n : PNat) :
    logUnriggingValue x n =
      ((logRiggingWeight n : ℝ) : ℂ) * x.1 n := rfl

theorem range_logRigging_eq_logUnriggingDomain :
    LinearMap.range logRigging.toLinearMap = logUnriggingDomain := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change Memℓp (fun n : PNat =>
      ((logRiggingWeight n : ℝ) : ℂ) * logRigging y n) 2
    convert lp.memℓp y using 1
    funext n
    rw [logRigging_apply]
    have hwC : ((logRiggingWeight n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast logRiggingWeight_ne_zero n
    push_cast
    field_simp [hwC]
  · intro hx
    let y : LogRiggedState :=
      ⟨fun n : PNat => ((logRiggingWeight n : ℝ) : ℂ) * x n, hx⟩
    refine ⟨y, ?_⟩
    apply lp.ext
    funext n
    change (((logRiggingWeight n)⁻¹ : ℝ) : ℂ) *
        (((logRiggingWeight n : ℝ) : ℂ) * x n) = x n
    have hwC : ((logRiggingWeight n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast logRiggingWeight_ne_zero n
    push_cast
    field_simp [hwC]

/-- Maximal logarithmic unrigging operator, defined as the inverse of the
bounded injective rigging map. -/
def logUnrigging : LogRiggedState →ₗ.[ℂ] LogRiggedState :=
  logRiggingPMap.inverse

theorem logUnrigging_domain :
    logUnrigging.domain = logUnriggingDomain := by
  rw [logUnrigging, LinearPMap.inverse_domain, logRiggingPMap_range,
    range_logRigging_eq_logUnriggingDomain]

@[simp] theorem mem_logUnrigging_domain_iff (x : LogRiggedState) :
    x ∈ logUnrigging.domain ↔
      Memℓp (fun n : PNat =>
        ((logRiggingWeight n : ℝ) : ℂ) * x n) 2 := by
  rw [logUnrigging_domain]
  rfl

theorem logUnrigging_denseDomain :
    Dense (logUnrigging.domain : Set LogRiggedState) := by
  rw [logUnrigging_domain, ← range_logRigging_eq_logUnriggingDomain]
  exact logRigging_denseRange

theorem logRiggingPMap_isClosed : logRiggingPMap.IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph : (logRiggingPMap.graph : Set
      (LogRiggedState × LogRiggedState)) =
      {z | logRigging z.1 = z.2} := by
    ext z
    simp [LinearPMap.mem_graph_iff, logRiggingPMap]
  rw [hgraph]
  exact isClosed_eq (logRigging.continuous.comp continuous_fst) continuous_snd

/-- The maximal logarithmic unrigging operator is closed. -/
theorem logUnrigging_isClosed : logUnrigging.IsClosed := by
  exact (LinearPMap.inverse_closed_iff logRiggingPMap_ker_eq_bot).2
    logRiggingPMap_isClosed

/-- In particular, the maximal logarithmic unrigging operator is closable. -/
theorem logUnrigging_isClosable : logUnrigging.IsClosable :=
  logUnrigging_isClosed.isClosable

private def logRiggingDomainElement (x : LogRiggedState) :
    logRiggingPMap.domain := ⟨x, by simp⟩

def logRiggingRangeElement (x : LogRiggedState) :
    logUnrigging.domain :=
  ⟨logRigging x, by
    rw [logUnrigging_domain, ← range_logRigging_eq_logUnriggingDomain]
    exact LinearMap.mem_range_self _ x⟩

@[simp] theorem logUnrigging_apply_logRiggingRangeElement
    (x : LogRiggedState) :
    logUnrigging (logRiggingRangeElement x) = x := by
  simpa [logUnrigging, logRiggingDomainElement] using
    (LinearPMap.inverse_apply_eq logRiggingPMap_ker_eq_bot
      (x := logRiggingDomainElement x)
      (y := logRiggingRangeElement x) (by rfl))

theorem logUnrigging_apply_coordinate (x : logUnrigging.domain)
    (n : PNat) :
    logUnrigging x n =
      ((logRiggingWeight n : ℝ) : ℂ) * (x : LogRiggedState) n := by
  let x' : logUnriggingDomain :=
    ⟨x, by simpa only [logUnrigging_domain] using x.2⟩
  let y := logUnriggingValue x'
  have hJ : logRigging y = x := by
    apply lp.ext
    funext k
    change (((logRiggingWeight k)⁻¹ : ℝ) : ℂ) *
        (((logRiggingWeight k : ℝ) : ℂ) * (x : LogRiggedState) k) =
      (x : LogRiggedState) k
    have hwC : ((logRiggingWeight k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast logRiggingWeight_ne_zero k
    push_cast
    field_simp [hwC]
  have hrange : logRiggingRangeElement y = x := by
    apply Subtype.ext
    exact hJ
  rw [← hrange, logUnrigging_apply_logRiggingRangeElement]
  change y n = ((logRiggingWeight n : ℝ) : ℂ) * logRigging y n
  rw [logRigging_apply]
  have hwC : ((logRiggingWeight n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast logRiggingWeight_ne_zero n
  push_cast
  field_simp [hwC]

/-- Applying bounded rigging after maximal unrigging recovers every vector in
the explicit unrigging domain. -/
theorem logRigging_apply_logUnrigging (x : logUnrigging.domain) :
    logRigging (logUnrigging x) = (x : LogRiggedState) := by
  apply lp.ext
  funext n
  rw [logRigging_apply, logUnrigging_apply_coordinate]
  have hwC : ((logRiggingWeight n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast logRiggingWeight_ne_zero n
  push_cast
  field_simp [hwC]

/-- The maximal unrigging operator reaches every unweighted square-summable
coordinate vector. -/
theorem logUnrigging_range_eq_top :
    LinearMap.range logUnrigging.toFun = ⊤ := by
  rw [logUnrigging, LinearPMap.inverse_range logRiggingPMap_ker_eq_bot,
    logRiggingPMap_domain]

/-- Surjectivity of maximal unrigging onto unweighted square-summable
coordinates. -/
theorem logUnrigging_surjective : Function.Surjective logUnrigging.toFun := by
  rw [← LinearMap.range_eq_top]
  exact logUnrigging_range_eq_top

/-- The maximal unrigging domain is invariant under the logarithmic
angular evolution. -/
theorem riggedAngularEvolution_mem_logUnrigging_domain (t : ℝ)
    {x : LogRiggedState} (hx : x ∈ logUnrigging.domain) :
    riggedAngularEvolution t x ∈ logUnrigging.domain := by
  rw [mem_logUnrigging_domain_iff] at hx ⊢
  apply hx.mono'
  intro n
  rw [riggedAngularEvolution_apply]
  simp only [norm_mul, nativeLogPhase_norm, one_mul]
  exact le_rfl

/-- Evolution of a vector in the maximal unrigging domain, bundled back
into that domain. -/
def riggedAngularEvolutionDomainElement (t : ℝ)
    (x : logUnrigging.domain) : logUnrigging.domain :=
  ⟨riggedAngularEvolution t x,
    riggedAngularEvolution_mem_logUnrigging_domain t x.2⟩

/-- The closed unrigging operator intertwines the logarithmic angular
evolution on its invariant maximal domain. -/
theorem logUnrigging_commutes_riggedAngularEvolution (t : ℝ)
    (x : logUnrigging.domain) :
    logUnrigging (riggedAngularEvolutionDomainElement t x) =
      riggedAngularEvolution t (logUnrigging x) := by
  apply lp.ext
  funext n
  change logUnrigging (riggedAngularEvolutionDomainElement t x) n =
    nativeLogPhase t n * logUnrigging x n
  rw [logUnrigging_apply_coordinate]
  change ((logRiggingWeight n : ℝ) : ℂ) *
      (nativeLogPhase t n * (x : LogRiggedState) n) =
    nativeLogPhase t n * logUnrigging x n
  rw [logUnrigging_apply_coordinate]
  ring

/-- No point of the distinguished critical orbit belongs to the maximal
unrigging domain.  Pointwise unrigging exists, but it is the non-square-
summable native amplitude. -/
theorem criticalRiggedOrbit_not_mem_logUnrigging_domain (t : ℝ) :
    criticalRiggedOrbit t ∉ logUnrigging.domain := by
  intro horbit
  rw [mem_logUnrigging_domain_iff] at horbit
  have hunrigged : Memℓp
      (fun n : PNat => unriggedCoordinate (criticalRiggedOrbit t) n) 2 := by
    simpa only [unriggedCoordinate, logRiggingWeight] using horbit
  apply nativeCriticalAmplitude_not_memLp
  apply hunrigged.mono'
  intro n
  rw [unriggedCoordinate_criticalRiggedOrbit]
  change ‖nativeCriticalAmplitude n‖ ≤
    ‖nativeLogPhase t n * nativeCriticalAmplitude n‖
  rw [norm_mul, nativeLogPhase_norm, one_mul]

/-- The maximal unrigging domain is proper; in particular, the logarithmic
multiplier is genuinely a partial rather than an everywhere-defined
operator on the ambient Hilbert realization. -/
theorem logUnrigging_domain_ne_top : logUnrigging.domain ≠ ⊤ := by
  intro htop
  apply criticalRiggedOrbit_not_mem_logUnrigging_domain 0
  rw [htop]
  exact Submodule.mem_top

/-- Multiplication by the real logarithmic weight is symmetric on its
maximal domain. -/
theorem logUnrigging_isFormalAdjoint :
    logUnrigging.IsFormalAdjoint logUnrigging := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [logUnrigging_apply_coordinate, logUnrigging_apply_coordinate]
  change inner ℂ
      (((logRiggingWeight n : ℝ) : ℂ) * (x : LogRiggedState) n)
      ((y : LogRiggedState) n) =
    inner ℂ ((x : LogRiggedState) n)
      (((logRiggingWeight n : ℝ) : ℂ) * (y : LogRiggedState) n)
  simp
  ring

/-- Every adjoint-domain vector is obtained by applying the bounded rigging
map to its adjoint image.  This is the maximality step behind
self-adjointness. -/
theorem logRigging_apply_logUnrigging_adjoint (y : logUnrigging†.domain) :
    logRigging (logUnrigging† y) = (y : LogRiggedState) := by
  apply (InnerProductSpace.toDualMap ℂ LogRiggedState).injective
  apply ContinuousLinearMap.ext
  intro u
  simp only [InnerProductSpace.toDualMap_apply_apply]
  calc
    ⟪logRigging (logUnrigging† y), u⟫_ℂ =
        ⟪logUnrigging† y, logRigging u⟫_ℂ :=
      logRigging_isSymmetric _ _
    _ = ⟪(y : LogRiggedState),
          logUnrigging (logRiggingRangeElement u)⟫_ℂ :=
      logUnrigging.adjoint_isFormalAdjoint logUnrigging_denseDomain y
        (logRiggingRangeElement u)
    _ = ⟪(y : LogRiggedState), u⟫_ℂ := by
      rw [logUnrigging_apply_logRiggingRangeElement]

/-- The adjoint has no vectors beyond the explicit maximal logarithmic
domain. -/
theorem logUnrigging_adjoint_domain_le :
    logUnrigging†.domain ≤ logUnrigging.domain := by
  intro y hy
  rw [logUnrigging_domain, ← range_logRigging_eq_logUnriggingDomain]
  let y' : logUnrigging†.domain := ⟨y, hy⟩
  refine ⟨logUnrigging† y', ?_⟩
  exact logRigging_apply_logUnrigging_adjoint y'

/-- Maximality of the real diagonal multiplication operator. -/
theorem logUnrigging_adjoint_le : logUnrigging† ≤ logUnrigging := by
  refine ⟨logUnrigging_adjoint_domain_le, ?_⟩
  intro x y hxy
  let z : LogRiggedState := logUnrigging† x
  have hz : logRigging z = (x : LogRiggedState) :=
    logRigging_apply_logUnrigging_adjoint x
  have hrange : logRiggingRangeElement z = y := by
    apply Subtype.ext
    exact hz.trans hxy
  calc
    logUnrigging† x = z := rfl
    _ = logUnrigging (logRiggingRangeElement z) :=
      (logUnrigging_apply_logRiggingRangeElement z).symm
    _ = logUnrigging y := by rw [hrange]

/-- The maximal logarithmic unrigging operator is self-adjoint.  This is
strictly stronger than closedness, while retaining the explicit proper,
dense domain. -/
theorem logUnrigging_isSelfAdjoint : IsSelfAdjoint logUnrigging := by
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm logUnrigging_adjoint_le
    (logUnrigging_isFormalAdjoint.le_adjoint logUnrigging_denseDomain)

/-- Because maximal unrigging is already closed, taking its canonical graph
closure does not enlarge it. -/
theorem logUnrigging_closure_eq :
    logUnrigging.closure = logUnrigging := by
  apply LinearPMap.eq_of_eq_graph
  rw [← logUnrigging_isClosable.graph_closure_eq_closure_graph]
  exact logUnrigging_isClosed.submodule_topologicalClosure_eq

/-- Canonical rigged port into the strong dual.  In the complete Hilbert
realization this is the global Fréchet--Riesz anti-linear isometric
equivalence, stronger than a merely closable port. -/
abbrev LogRiggedTestState := LogRiggedState

def logRiggedDualPort :
    LogRiggedState ≃ₗᵢ⋆[ℂ] StrongDual ℂ LogRiggedTestState :=
  InnerProductSpace.toDual ℂ LogRiggedTestState

@[simp] theorem logRiggedDualPort_apply (x : LogRiggedState)
    (y : LogRiggedTestState) :
    logRiggedDualPort x y = ⟪x, y⟫_ℂ := rfl

theorem logRiggedDualPort_norm (x : LogRiggedState) :
    ‖logRiggedDualPort x‖ = ‖x‖ :=
  logRiggedDualPort.norm_map x

/-- Distinguished critical orbit viewed through the canonical strong-dual
rigged port. -/
def criticalRiggedDualOrbit (t : ℝ) : StrongDual ℂ LogRiggedTestState :=
  logRiggedDualPort (criticalRiggedOrbit t)

theorem continuous_criticalRiggedDualOrbit :
    Continuous criticalRiggedDualOrbit :=
  logRiggedDualPort.continuous.comp continuous_criticalRiggedOrbit

@[simp] theorem criticalRiggedDualOrbit_apply (t : ℝ)
    (x : LogRiggedState) :
    criticalRiggedDualOrbit t x = ⟪criticalRiggedOrbit t, x⟫_ℂ := rfl

theorem criticalRiggedDualOrbit_norm (t : ℝ) :
    ‖criticalRiggedDualOrbit t‖ = ‖criticalRiggedState‖ := by
  rw [criticalRiggedDualOrbit, logRiggedDualPort_norm,
    criticalRiggedOrbit_norm]

end NativeCarrySpectralWeyl.Boundary
