import NativeCarrySpectralWeyl.Boundary.GreenRelation
import NativeCarrySpectralWeyl.Infinite.Cauchy

/-!
# Source-extended boundary relation

This file realizes the next Phase 6 object from the research notes.  Given a
self-adjoint partial operator `Y` on an ambient Hilbert space and a bounded
port map `V` from a boundary Hilbert space, the source-extended relation is

`T_C = { (f, Y f + V u) | f in dom(Y), u in B }`.

When `V` is injective, each relation vector has unique parameters `(f, u)`.
This makes the reference and Weyl boundary charts honest linear maps:

`Gamma_H(f, Y f + V u) = (u, -V^* f)`,

`Gamma_W(f, Y f + V u) = (V^* f, u)`.

The two charts differ by the symplectic quarter-turn already formalized in
`Boundary.GreenRelation`.  We then place the interior relation and its Weyl
boundary value in the product Green space.  Formal symmetry of `Y` gives the
Green identity, while self-adjointness gives maximality of this coupled
boundary graph.

The final section instantiates the construction with maximal logarithmic
multiplication and the all-bases Naimark isometry.  This is the exact boundary
relation needed before defining the gamma field and identifying its Weyl
family with the compressed resolvent.
-/

noncomputable section

open RCLike LinearPMap
open scoped ComplexConjugate

namespace NativeCarrySpectralWeyl.Boundary

variable {𝕜 H B : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [NormedAddCommGroup B] [InnerProductSpace 𝕜 B]

/-! ## The source-extended relation and its unique coordinates -/

/-- Linear parameterization `(f,u) |-> (f, Y f + V u)` of the
source-extended relation. -/
def sourceRelationParameterization (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) :
    operator.domain × B →ₗ[𝕜] H × H where
  toFun p := ((p.1 : H), operator p.1 + port p.2)
  map_add' p q := by
    ext
    · rfl
    · change operator (p.1 + q.1) + port (p.2 + q.2) =
        (operator p.1 + port p.2) + (operator q.1 + port q.2)
      rw [LinearPMap.map_add, port.map_add]
      abel
  map_smul' c p := by
    ext
    · rfl
    · change operator (c • p.1) + port (c • p.2) =
        c • (operator p.1 + port p.2)
      rw [LinearPMap.map_smul, port.map_smul]
      exact (smul_add c (operator p.1) (port p.2)).symm

/-- The source-extended relation
`{(f, Y f + V u) | f in dom(Y), u in B}`. -/
def sourceExtendedRelation (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) : GreenRelation 𝕜 H :=
  LinearMap.range (sourceRelationParameterization operator port)

/-- Exact membership in the source-extended relation. -/
theorem mem_sourceExtendedRelation_iff (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) (pair : H × H) :
    pair ∈ sourceExtendedRelation operator port ↔
      ∃ f : operator.domain, ∃ u : B,
        pair = ((f : H), operator f + port u) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨f, u, rfl⟩
    exact ⟨(f, u), rfl⟩

/-- An injective port map makes the source parameters unique. -/
theorem sourceRelationParameterization_injective
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hport : Function.Injective port) :
    Function.Injective (sourceRelationParameterization operator port) := by
  intro p q hpq
  have hdomain : p.1 = q.1 := by
    apply Subtype.ext
    exact congrArg Prod.fst hpq
  have hboundary : p.2 = q.2 := by
    apply hport
    have hsecond := congrArg Prod.snd hpq
    change operator p.1 + port p.2 = operator q.1 + port q.2 at hsecond
    rw [hdomain] at hsecond
    exact add_left_cancel hsecond
  exact Prod.ext hdomain hboundary

/-- Unique linear coordinates on the source-extended relation. -/
def sourceRelationEquiv (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) (hport : Function.Injective port) :
    (operator.domain × B) ≃ₗ[𝕜] sourceExtendedRelation operator port :=
  LinearEquiv.ofInjective (sourceRelationParameterization operator port)
    (sourceRelationParameterization_injective operator port hport)

@[simp] theorem coe_sourceRelationEquiv
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hport : Function.Injective port) (p : operator.domain × B) :
    ((sourceRelationEquiv operator port hport p :
      sourceExtendedRelation operator port) : H × H) =
        ((p.1 : H), operator p.1 + port p.2) :=
  rfl

/-! ## Reference and Weyl boundary charts -/

section Charts

variable [CompleteSpace H] [CompleteSpace B]

/-- Reference-chart boundary coordinates on source parameters. -/
def referenceBoundaryParameters (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) :
    operator.domain × B →ₗ[𝕜] B × B where
  toFun p := (p.2, -port.adjoint (p.1 : H))
  map_add' p q := by
    ext
    · simp
    · simp
      abel
  map_smul' c p := by
    ext <;> simp

/-- Weyl/impedance-chart boundary coordinates on source parameters. -/
def weylBoundaryParameters (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) :
    operator.domain × B →ₗ[𝕜] B × B where
  toFun p := (port.adjoint (p.1 : H), p.2)
  map_add' p q := by
    ext <;> simp
  map_smul' c p := by
    ext <;> simp

/-- The Weyl parameters are the symplectic rotation of the reference
parameters. -/
theorem weylBoundaryParameters_eq_rotation
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (p : operator.domain × B) :
    weylBoundaryParameters operator port p =
      weylChartRotation (𝕜 := 𝕜)
        (referenceBoundaryParameters operator port p) := by
  simp [weylBoundaryParameters, referenceBoundaryParameters,
    weylChartRotation]

/-- Reference boundary chart on the source-extended relation. -/
def referenceBoundaryMap (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) (hport : Function.Injective port) :
    sourceExtendedRelation operator port →ₗ[𝕜] B × B :=
  (referenceBoundaryParameters operator port).comp
    (sourceRelationEquiv operator port hport).symm.toLinearMap

/-- Weyl/impedance boundary chart on the source-extended relation. -/
def weylBoundaryMap (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) (hport : Function.Injective port) :
    sourceExtendedRelation operator port →ₗ[𝕜] B × B :=
  (weylBoundaryParameters operator port).comp
    (sourceRelationEquiv operator port hport).symm.toLinearMap

@[simp] theorem referenceBoundaryMap_sourceRelationEquiv
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hport : Function.Injective port) (p : operator.domain × B) :
    referenceBoundaryMap operator port hport
        (sourceRelationEquiv operator port hport p) =
      (p.2, -port.adjoint (p.1 : H)) := by
  simp [referenceBoundaryMap, referenceBoundaryParameters]

@[simp] theorem weylBoundaryMap_sourceRelationEquiv
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hport : Function.Injective port) (p : operator.domain × B) :
    weylBoundaryMap operator port hport
        (sourceRelationEquiv operator port hport p) =
      (port.adjoint (p.1 : H), p.2) := by
  simp [weylBoundaryMap, weylBoundaryParameters]

/-- The two boundary charts differ by the documented symplectic
quarter-turn. -/
theorem weylBoundaryMap_eq_rotation_referenceBoundaryMap
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hport : Function.Injective port)
    (relationVector : sourceExtendedRelation operator port) :
    weylBoundaryMap operator port hport relationVector =
      weylChartRotation (𝕜 := 𝕜)
        (referenceBoundaryMap operator port hport relationVector) := by
  let p := (sourceRelationEquiv operator port hport).symm relationVector
  have hp : sourceRelationEquiv operator port hport p = relationVector := by
    exact (sourceRelationEquiv operator port hport).apply_symm_apply relationVector
  rw [← hp]
  simp [weylChartRotation]

end Charts

/-! ## Coupled interior-boundary Green space -/

/-- Green form on an interior relation pair together with a boundary pair.
The boundary contribution is subtracted, so a boundary realization is
isotropic exactly when the interior and boundary Green forms agree. -/
def coupledGreenForm (x y : (H × H) × (B × B)) : 𝕜 :=
  greenForm (𝕜 := 𝕜) x.1 y.1 - greenForm (𝕜 := 𝕜) x.2 y.2

@[simp] theorem coupledGreenForm_zero_left (x : (H × H) × (B × B)) :
    coupledGreenForm (𝕜 := 𝕜) (0 : (H × H) × (B × B)) x = 0 := by
  simp [coupledGreenForm]

@[simp] theorem coupledGreenForm_zero_right (x : (H × H) × (B × B)) :
    coupledGreenForm (𝕜 := 𝕜) x (0 : (H × H) × (B × B)) = 0 := by
  simp [coupledGreenForm]

theorem coupledGreenForm_add_right (x y z : (H × H) × (B × B)) :
    coupledGreenForm (𝕜 := 𝕜) x (y + z) =
      coupledGreenForm (𝕜 := 𝕜) x y +
        coupledGreenForm (𝕜 := 𝕜) x z := by
  simp only [coupledGreenForm, Prod.fst_add, Prod.snd_add,
    greenForm_add_right]
  ring

theorem coupledGreenForm_smul_right (c : 𝕜)
    (x y : (H × H) × (B × B)) :
    coupledGreenForm (𝕜 := 𝕜) x (c • y) =
      c * coupledGreenForm (𝕜 := 𝕜) x y := by
  simp only [coupledGreenForm, Prod.smul_fst, Prod.smul_snd,
    greenForm_smul_right]
  ring

/-- Symplectic orthogonal for the coupled interior-boundary Green form. -/
def coupledGreenAdjoint
    (relation : Submodule 𝕜 ((H × H) × (B × B))) :
    Submodule 𝕜 ((H × H) × (B × B)) where
  carrier := {y | ∀ x, x ∈ relation → coupledGreenForm (𝕜 := 𝕜) x y = 0}
  zero_mem' := fun x _ => coupledGreenForm_zero_right x
  add_mem' := by
    intro y z hy hz x hx
    rw [coupledGreenForm_add_right, hy x hx, hz x hx, add_zero]
  smul_mem' := by
    intro c y hy x hx
    rw [coupledGreenForm_smul_right, hy x hx, mul_zero]

@[simp] theorem mem_coupledGreenAdjoint_iff
    (relation : Submodule 𝕜 ((H × H) × (B × B)))
    (y : (H × H) × (B × B)) :
    y ∈ coupledGreenAdjoint relation ↔
      ∀ x, x ∈ relation → coupledGreenForm (𝕜 := 𝕜) x y = 0 :=
  Iff.rfl

/-- Maximal isotropy in the coupled interior-boundary Green space. -/
def IsMaximalCoupledGreenIsotropic
    (relation : Submodule 𝕜 ((H × H) × (B × B))) : Prop :=
  coupledGreenAdjoint relation = relation

section CoupledGraph

variable [CompleteSpace H] [CompleteSpace B]

/-- Parameterization of the graph of the Weyl boundary chart in the coupled
interior-boundary space. -/
def weylBoundaryGraphParameterization (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) :
    operator.domain × B →ₗ[𝕜] (H × H) × (B × B) where
  toFun p :=
    (((p.1 : H), operator p.1 + port p.2),
      (port.adjoint (p.1 : H), p.2))
  map_add' p q := by
    ext
    · rfl
    · change operator (p.1 + q.1) + port (p.2 + q.2) =
        (operator p.1 + port p.2) + (operator q.1 + port q.2)
      rw [LinearPMap.map_add, port.map_add]
      abel
    · simp
    · rfl
  map_smul' c p := by
    ext
    · rfl
    · change operator (c • p.1) + port (c • p.2) =
        c • (operator p.1 + port p.2)
      rw [LinearPMap.map_smul, port.map_smul]
      exact (smul_add c (operator p.1) (port p.2)).symm
    · simp
    · rfl

/-- Graph of the Weyl boundary chart, embedded in the ambient coupled Green
space. -/
def weylBoundaryGraph (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) :
    Submodule 𝕜 ((H × H) × (B × B)) :=
  LinearMap.range (weylBoundaryGraphParameterization operator port)

/-- Exact membership in the coupled Weyl boundary graph. -/
theorem mem_weylBoundaryGraph_iff (operator : H →ₗ.[𝕜] H)
    (port : B →L[𝕜] H) (z : (H × H) × (B × B)) :
    z ∈ weylBoundaryGraph operator port ↔
      ∃ f : operator.domain, ∃ u : B,
        z = (((f : H), operator f + port u),
          (port.adjoint (f : H), u)) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨f, u, rfl⟩
    exact ⟨(f, u), rfl⟩

/-- The source-extended Green identity: the interior Green form equals the
Weyl boundary Green form. -/
theorem weylBoundaryGraph_green_identity
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hformal : operator.IsFormalAdjoint operator)
    (p q : operator.domain × B) :
    coupledGreenForm (𝕜 := 𝕜)
      (weylBoundaryGraphParameterization operator port p)
      (weylBoundaryGraphParameterization operator port q) = 0 := by
  rcases p with ⟨f, u⟩
  rcases q with ⟨g, v⟩
  simp only [coupledGreenForm, weylBoundaryGraphParameterization,
    greenForm, LinearMap.coe_mk, AddHom.coe_mk,
    inner_add_left, inner_add_right]
  rw [hformal f g, port.adjoint_inner_right u (g : H),
    port.adjoint_inner_left v (f : H)]
  ring

/-- Green identity stated directly on relation vectors and their Weyl-chart
boundary values. -/
theorem sourceExtendedRelation_weyl_green_identity
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hport : Function.Injective port)
    (hformal : operator.IsFormalAdjoint operator)
    (x y : sourceExtendedRelation operator port) :
    greenForm (𝕜 := 𝕜) (x : H × H) (y : H × H) =
      greenForm (𝕜 := 𝕜)
        (weylBoundaryMap operator port hport x)
        (weylBoundaryMap operator port hport y) := by
  let p := (sourceRelationEquiv operator port hport).symm x
  let q := (sourceRelationEquiv operator port hport).symm y
  have hx : sourceRelationEquiv operator port hport p = x :=
    (sourceRelationEquiv operator port hport).apply_symm_apply x
  have hy : sourceRelationEquiv operator port hport q = y :=
    (sourceRelationEquiv operator port hport).apply_symm_apply y
  rw [← hx, ← hy]
  have hgreen :=
    weylBoundaryGraph_green_identity operator port hformal p q
  have heq := sub_eq_zero.mp (by
    simpa [coupledGreenForm, weylBoundaryGraphParameterization] using hgreen)
  simpa only [coe_sourceRelationEquiv,
    weylBoundaryMap_sourceRelationEquiv] using heq

/-- The same Green identity in the reference chart.  It follows from the
Weyl identity because the two charts differ by a symplectic quarter-turn. -/
theorem sourceExtendedRelation_reference_green_identity
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hport : Function.Injective port)
    (hformal : operator.IsFormalAdjoint operator)
    (x y : sourceExtendedRelation operator port) :
    greenForm (𝕜 := 𝕜) (x : H × H) (y : H × H) =
      greenForm (𝕜 := 𝕜)
        (referenceBoundaryMap operator port hport x)
        (referenceBoundaryMap operator port hport y) := by
  calc
    greenForm (𝕜 := 𝕜) (x : H × H) (y : H × H) =
        greenForm (𝕜 := 𝕜)
          (weylBoundaryMap operator port hport x)
          (weylBoundaryMap operator port hport y) :=
      sourceExtendedRelation_weyl_green_identity operator port hport
        hformal x y
    _ = greenForm (𝕜 := 𝕜)
          (referenceBoundaryMap operator port hport x)
          (referenceBoundaryMap operator port hport y) := by
      rw [weylBoundaryMap_eq_rotation_referenceBoundaryMap,
        weylBoundaryMap_eq_rotation_referenceBoundaryMap,
        greenForm_weylChartRotation]

/-- Formal symmetry makes the coupled Weyl boundary graph isotropic. -/
theorem weylBoundaryGraph_le_coupledGreenAdjoint
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hformal : operator.IsFormalAdjoint operator) :
    weylBoundaryGraph operator port ≤
      coupledGreenAdjoint (weylBoundaryGraph operator port) := by
  intro z hz
  rw [mem_coupledGreenAdjoint_iff]
  intro w hw
  rcases hw with ⟨p, rfl⟩
  rcases hz with ⟨q, rfl⟩
  exact weylBoundaryGraph_green_identity operator port hformal p q

/-- A self-adjoint interior operator makes the coupled Weyl boundary graph
maximal Green-isotropic.  The proof recovers the boundary coordinate from
tests `(0,u)` and recovers membership in `dom(Y)` from tests `(f,0)` via the
Hilbert-space adjoint. -/
theorem weylBoundaryGraph_isMaximalCoupledGreenIsotropic
    (operator : H →ₗ.[𝕜] H) (port : B →L[𝕜] H)
    (hself : IsSelfAdjoint operator) :
    IsMaximalCoupledGreenIsotropic (weylBoundaryGraph operator port) := by
  have hformal : operator.IsFormalAdjoint operator := by
    have hadjointFormal :=
      LinearPMap.adjoint_isFormalAdjoint (T := operator) hself.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hself] at hadjointFormal
    exact hadjointFormal
  apply le_antisymm
  · rintro ⟨⟨x, y⟩, ⟨a, b⟩⟩ hz
    rw [mem_coupledGreenAdjoint_iff] at hz
    have ha : port.adjoint x = a := by
      apply ext_inner_left 𝕜
      intro u
      rw [port.adjoint_inner_right u x]
      apply sub_eq_zero.mp
      simpa [coupledGreenForm, weylBoundaryGraphParameterization,
        weylBoundaryGraph, greenForm] using
        hz (weylBoundaryGraphParameterization operator port (0, u))
          ⟨(0, u), rfl⟩
    have hpair (f : operator.domain) :
        inner 𝕜 (operator f) x = inner 𝕜 (f : H) (y - port b) := by
      have htest :=
        hz (weylBoundaryGraphParameterization operator port (f, 0))
          ⟨(f, 0), rfl⟩
      simp [coupledGreenForm, weylBoundaryGraphParameterization,
        greenForm] at htest
      rw [port.adjoint_inner_left b (f : H)] at htest
      rw [inner_sub_right]
      linear_combination htest
    let witness : H := y - port b
    have hwitness (f : operator.domain) :
        inner 𝕜 witness (f : H) = inner 𝕜 x (operator f) := by
      calc
        inner 𝕜 witness (f : H) =
            conj (inner 𝕜 (f : H) witness) :=
          (inner_conj_symm witness (f : H)).symm
        _ = conj (inner 𝕜 (operator f) x) :=
          congrArg conj (hpair f).symm
        _ = inner 𝕜 x (operator f) :=
          inner_conj_symm x (operator f)
    have hxAdjoint : x ∈ operator.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists (T := operator) x
        ⟨witness, hwitness⟩
    have hadjoint : operator.adjoint = operator :=
      LinearPMap.isSelfAdjoint_def.mp hself
    have hx : x ∈ operator.domain := by
      rw [← hadjoint]
      exact hxAdjoint
    have hoperator : operator (⟨x, hx⟩ : operator.domain) = witness := by
      apply hself.dense_domain.eq_of_inner_left 𝕜
      intro f hf
      let fd : operator.domain := ⟨f, hf⟩
      calc
        inner 𝕜 (operator (⟨x, hx⟩ : operator.domain)) f =
            inner 𝕜 x (operator fd) := hformal ⟨x, hx⟩ fd
        _ = inner 𝕜 witness f := (hwitness fd).symm
    have hy : y = operator (⟨x, hx⟩ : operator.domain) + port b := by
      rw [hoperator]
      change y = (y - port b) + port b
      abel
    rw [mem_weylBoundaryGraph_iff]
    refine ⟨⟨x, hx⟩, b, ?_⟩
    rw [← ha, hy]
  · exact weylBoundaryGraph_le_coupledGreenAdjoint operator port hformal

end CoupledGraph

/-! ## Concrete all-bases logarithmic boundary relation -/

/-- The Naimark port, viewed as a bounded map from the all-bases camera
Hilbert space into the ambient logarithmic Hilbert space. -/
def carryNaimarkPort :
    Infinite.CameraHilbert →L[ℝ] Infinite.NaimarkSpace :=
  Infinite.naimarkIsometry.toContinuousLinearMap

/-- The all-bases Naimark port is injective. -/
theorem carryNaimarkPort_injective : Function.Injective carryNaimarkPort :=
  Infinite.naimarkIsometry.injective

/-- The Hilbert-space adjoint of the carry port is the already constructed
Naimark compression map. -/
@[simp] theorem carryNaimarkPort_adjoint_eq :
    carryNaimarkPort.adjoint = Infinite.naimarkAdjoint :=
  rfl

/-- The concrete source-extended carry relation
`T_C = {(f, Y f + V u)}`. -/
def carrySourceRelation : GreenRelation ℝ Infinite.NaimarkSpace :=
  sourceExtendedRelation Infinite.logarithmicMultiplication carryNaimarkPort

/-- Exact membership in the concrete all-bases carry relation. -/
theorem mem_carrySourceRelation_iff
    (pair : Infinite.NaimarkSpace × Infinite.NaimarkSpace) :
    pair ∈ carrySourceRelation ↔
      ∃ f : Infinite.logarithmicMultiplication.domain,
        ∃ u : Infinite.CameraHilbert,
          pair = ((f : Infinite.NaimarkSpace),
            Infinite.logarithmicMultiplication f +
              Infinite.naimarkIsometry u) := by
  simpa [carrySourceRelation, carryNaimarkPort] using
    (mem_sourceExtendedRelation_iff Infinite.logarithmicMultiplication
      carryNaimarkPort pair)

/-- Canonical relation vector with logarithmic-domain coordinate `f` and
camera source `u`. -/
def carrySourceRelationElement
    (f : Infinite.logarithmicMultiplication.domain)
    (u : Infinite.CameraHilbert) : carrySourceRelation :=
  sourceRelationEquiv Infinite.logarithmicMultiplication carryNaimarkPort
    carryNaimarkPort_injective (f, u)

@[simp] theorem coe_carrySourceRelationElement
    (f : Infinite.logarithmicMultiplication.domain)
    (u : Infinite.CameraHilbert) :
    ((carrySourceRelationElement f u : carrySourceRelation) :
      Infinite.NaimarkSpace × Infinite.NaimarkSpace) =
        ((f : Infinite.NaimarkSpace),
          Infinite.logarithmicMultiplication f +
            Infinite.naimarkIsometry u) := by
  rfl

/-- Reference boundary chart
`Gamma_H(f, Yf + Vu) = (u, -V^*f)` for the carry relation. -/
def carryReferenceBoundaryMap :
    carrySourceRelation →ₗ[ℝ]
      Infinite.CameraHilbert × Infinite.CameraHilbert :=
  referenceBoundaryMap Infinite.logarithmicMultiplication carryNaimarkPort
    carryNaimarkPort_injective

/-- Weyl/impedance boundary chart
`Gamma_W(f, Yf + Vu) = (V^*f, u)` for the carry relation. -/
def carryWeylBoundaryMap :
    carrySourceRelation →ₗ[ℝ]
      Infinite.CameraHilbert × Infinite.CameraHilbert :=
  weylBoundaryMap Infinite.logarithmicMultiplication carryNaimarkPort
    carryNaimarkPort_injective

@[simp] theorem carryReferenceBoundaryMap_element
    (f : Infinite.logarithmicMultiplication.domain)
    (u : Infinite.CameraHilbert) :
    carryReferenceBoundaryMap (carrySourceRelationElement f u) =
      (u, -Infinite.naimarkAdjoint (f : Infinite.NaimarkSpace)) := by
  exact referenceBoundaryMap_sourceRelationEquiv
    Infinite.logarithmicMultiplication carryNaimarkPort
      carryNaimarkPort_injective (f, u)

@[simp] theorem carryWeylBoundaryMap_element
    (f : Infinite.logarithmicMultiplication.domain)
    (u : Infinite.CameraHilbert) :
    carryWeylBoundaryMap (carrySourceRelationElement f u) =
      (Infinite.naimarkAdjoint (f : Infinite.NaimarkSpace), u) := by
  exact weylBoundaryMap_sourceRelationEquiv
    Infinite.logarithmicMultiplication carryNaimarkPort
      carryNaimarkPort_injective (f, u)

/-- The concrete Weyl chart is the symplectic rotation of the concrete
reference chart. -/
theorem carryWeylBoundaryMap_eq_rotation
    (relationVector : carrySourceRelation) :
    carryWeylBoundaryMap relationVector =
      weylChartRotation (𝕜 := ℝ)
        (carryReferenceBoundaryMap relationVector) :=
  weylBoundaryMap_eq_rotation_referenceBoundaryMap
    Infinite.logarithmicMultiplication carryNaimarkPort
      carryNaimarkPort_injective relationVector

/-- Concrete all-bases Green identity in the Weyl chart. -/
theorem carrySourceRelation_weyl_green_identity
    (x y : carrySourceRelation) :
    greenForm (𝕜 := ℝ)
        (x : Infinite.NaimarkSpace × Infinite.NaimarkSpace)
        (y : Infinite.NaimarkSpace × Infinite.NaimarkSpace) =
      greenForm (𝕜 := ℝ)
        (carryWeylBoundaryMap x) (carryWeylBoundaryMap y) :=
  sourceExtendedRelation_weyl_green_identity
    Infinite.logarithmicMultiplication carryNaimarkPort
      carryNaimarkPort_injective
      Infinite.logarithmicMultiplication_isFormalAdjoint x y

/-- Concrete all-bases Green identity in the reference chart. -/
theorem carrySourceRelation_reference_green_identity
    (x y : carrySourceRelation) :
    greenForm (𝕜 := ℝ)
        (x : Infinite.NaimarkSpace × Infinite.NaimarkSpace)
        (y : Infinite.NaimarkSpace × Infinite.NaimarkSpace) =
      greenForm (𝕜 := ℝ)
        (carryReferenceBoundaryMap x) (carryReferenceBoundaryMap y) :=
  sourceExtendedRelation_reference_green_identity
    Infinite.logarithmicMultiplication carryNaimarkPort
      carryNaimarkPort_injective
      Infinite.logarithmicMultiplication_isFormalAdjoint x y

/-- Coupled graph of the concrete all-bases Weyl boundary chart. -/
def carryWeylBoundaryGraph :
    Submodule ℝ
      ((Infinite.NaimarkSpace × Infinite.NaimarkSpace) ×
        (Infinite.CameraHilbert × Infinite.CameraHilbert)) :=
  weylBoundaryGraph Infinite.logarithmicMultiplication carryNaimarkPort

/-- Exact parameterization of the concrete coupled Weyl boundary graph. -/
theorem mem_carryWeylBoundaryGraph_iff
    (z : (Infinite.NaimarkSpace × Infinite.NaimarkSpace) ×
      (Infinite.CameraHilbert × Infinite.CameraHilbert)) :
    z ∈ carryWeylBoundaryGraph ↔
      ∃ f : Infinite.logarithmicMultiplication.domain,
        ∃ u : Infinite.CameraHilbert,
          z = (((f : Infinite.NaimarkSpace),
              Infinite.logarithmicMultiplication f +
                Infinite.naimarkIsometry u),
            (Infinite.naimarkAdjoint (f : Infinite.NaimarkSpace), u)) := by
  simpa [carryWeylBoundaryGraph, carryNaimarkPort,
    Infinite.naimarkAdjoint] using
    (mem_weylBoundaryGraph_iff Infinite.logarithmicMultiplication
      carryNaimarkPort z)

/-- The concrete all-bases coupled boundary graph is maximal
Green-isotropic. -/
theorem carryWeylBoundaryGraph_isMaximalCoupledGreenIsotropic :
    IsMaximalCoupledGreenIsotropic carryWeylBoundaryGraph := by
  exact weylBoundaryGraph_isMaximalCoupledGreenIsotropic
    Infinite.logarithmicMultiplication carryNaimarkPort
      Infinite.logarithmicMultiplication_isSelfAdjoint

/-- Equivalently, the coupled Green adjoint of the concrete Weyl boundary
graph is the graph itself. -/
theorem carryWeylBoundaryGraph_coupledGreenAdjoint_eq :
    coupledGreenAdjoint carryWeylBoundaryGraph = carryWeylBoundaryGraph :=
  carryWeylBoundaryGraph_isMaximalCoupledGreenIsotropic

end NativeCarrySpectralWeyl.Boundary
