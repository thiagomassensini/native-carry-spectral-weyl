import NativeCarrySpectralWeyl.Infinite.LogarithmicMultiplication

/-!
# Green relations and the reference logarithmic graph

This file opens Phase 6 with the algebraic layer shared by the boundary-
relation constructions in the research notes.  A linear relation on a Hilbert
space is represented by a submodule of the product space.  On pairs
`(f, f')`, `(g, g')` we use the documented Green form

`inner f' g - inner f g'`.

Mathlib's `Submodule.adjoint` is exactly the symplectic orthogonal for this
form.  We expose that identification, formalize isotropy and maximality, and
prove that the graph of a densely defined partial operator is maximal
Green-isotropic exactly when the operator is self-adjoint.  The symplectic
rotation `(Gamma₀, Gamma₁) ↦ (-Gamma₁, Gamma₀)` used by the Weyl/impedance
chart preserves the Green form.

Finally, the already kernel-checked maximal logarithmic multiplication
operator gives a concrete closed maximal Green relation.  This is the
reference self-adjoint graph needed by the subsequent source-extended
boundary relation; it is not yet the full relation
`{(f, Y f + V u)}` and does not yet define a gamma field.
-/

noncomputable section

open RCLike LinearPMap
open scoped ComplexConjugate

namespace NativeCarrySpectralWeyl.Boundary

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A Hilbert-space linear relation is a linear subspace of the product of
the input and output spaces. -/
abbrev GreenRelation (𝕜 H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :=
  Submodule 𝕜 (H × H)

/-- The Green form on graph pairs, with the sign convention used in the
carry-native boundary-relation notes. -/
def greenForm (x y : H × H) : 𝕜 :=
  inner 𝕜 x.2 y.1 - inner 𝕜 x.1 y.2

@[simp] theorem greenForm_zero_left (x : H × H) :
    greenForm (𝕜 := 𝕜) (0 : H × H) x = 0 := by
  simp [greenForm]

@[simp] theorem greenForm_zero_right (x : H × H) :
    greenForm (𝕜 := 𝕜) x (0 : H × H) = 0 := by
  simp [greenForm]

theorem greenForm_add_left (x y z : H × H) :
    greenForm (𝕜 := 𝕜) (x + y) z =
      greenForm (𝕜 := 𝕜) x z + greenForm (𝕜 := 𝕜) y z := by
  simp [greenForm]
  simp only [inner_add_left]
  ring

theorem greenForm_add_right (x y z : H × H) :
    greenForm (𝕜 := 𝕜) x (y + z) =
      greenForm (𝕜 := 𝕜) x y + greenForm (𝕜 := 𝕜) x z := by
  simp [greenForm]
  simp only [inner_add_right]
  ring

theorem greenForm_smul_left (c : 𝕜) (x y : H × H) :
    greenForm (𝕜 := 𝕜) (c • x) y =
      conj c * greenForm (𝕜 := 𝕜) x y := by
  simp [greenForm, inner_smul_left]
  ring

theorem greenForm_smul_right (c : 𝕜) (x y : H × H) :
    greenForm (𝕜 := 𝕜) x (c • y) =
      c * greenForm (𝕜 := 𝕜) x y := by
  simp [greenForm, inner_smul_right]
  ring

/-- The Green form is skew-Hermitian. -/
theorem greenForm_skew (x y : H × H) :
    greenForm (𝕜 := 𝕜) y x =
      -conj (greenForm (𝕜 := 𝕜) x y) := by
  simp [greenForm]

/-- The symplectic quarter-turn used to pass from the reference `H` chart to
the Weyl/impedance chart. -/
def weylChartRotation : (H × H) ≃ₗ[𝕜] (H × H) :=
  LinearEquiv.skewSwap 𝕜 H H

@[simp] theorem weylChartRotation_apply (x : H × H) :
    weylChartRotation (𝕜 := 𝕜) x = (-x.2, x.1) :=
  rfl

/-- The Weyl-chart rotation is symplectic for the documented Green form. -/
theorem greenForm_weylChartRotation (x y : H × H) :
    greenForm (𝕜 := 𝕜) (weylChartRotation (𝕜 := 𝕜) x)
        (weylChartRotation (𝕜 := 𝕜) y) =
      greenForm (𝕜 := 𝕜) x y := by
  simp [greenForm, weylChartRotation]
  ring

/-- Symplectic orthogonal of a Hilbert-space relation.  This is an explicit
name for Mathlib's graph-adjoint construction. -/
def greenAdjoint (relation : GreenRelation 𝕜 H) : GreenRelation 𝕜 H :=
  relation.adjoint

/-- Membership in the Green adjoint is exactly vanishing of the Green form
against every vector of the original relation. -/
theorem mem_greenAdjoint_iff (relation : GreenRelation 𝕜 H) (y : H × H) :
    y ∈ greenAdjoint relation ↔
      ∀ x, x ∈ relation → greenForm (𝕜 := 𝕜) x y = 0 := by
  rw [greenAdjoint, Submodule.mem_adjoint_iff]
  constructor
  · intro hy x hx
    simpa [greenForm] using hy x.1 x.2 hx
  · intro hy a b hab
    simpa [greenForm] using hy (a, b) hab

/-- Taking the Green adjoint reverses relation inclusion. -/
theorem greenAdjoint_antitone {relation₁ relation₂ : GreenRelation 𝕜 H}
    (h : relation₁ ≤ relation₂) :
    greenAdjoint relation₂ ≤ greenAdjoint relation₁ := by
  intro y hy
  rw [mem_greenAdjoint_iff] at hy ⊢
  intro x hx
  exact hy x (h hx)

/-- A relation is Green-isotropic when it is contained in its Green
adjoint. -/
def IsGreenIsotropic (relation : GreenRelation 𝕜 H) : Prop :=
  relation ≤ greenAdjoint relation

/-- A relation is maximal Green-isotropic when it equals its Green adjoint. -/
def IsMaximalGreenIsotropic (relation : GreenRelation 𝕜 H) : Prop :=
  greenAdjoint relation = relation

/-- Isotropy is equivalent to the Green identity on every two relation
vectors. -/
theorem isGreenIsotropic_iff_green_identity
    (relation : GreenRelation 𝕜 H) :
    IsGreenIsotropic relation ↔
      ∀ x, x ∈ relation → ∀ y, y ∈ relation →
        greenForm (𝕜 := 𝕜) x y = 0 := by
  constructor
  · intro h x hx y hy
    exact (mem_greenAdjoint_iff relation y).mp (h hy) x hx
  · intro h y hy
    exact (mem_greenAdjoint_iff relation y).mpr fun x hx => h x hx y hy

/-- The Green identity supplied by an isotropic relation. -/
theorem isGreenIsotropic_green_identity {relation : GreenRelation 𝕜 H}
    (h : IsGreenIsotropic relation) {x y : H × H}
    (hx : x ∈ relation) (hy : y ∈ relation) :
    greenForm (𝕜 := 𝕜) x y = 0 :=
  (isGreenIsotropic_iff_green_identity relation).mp h x hx y hy

/-- Every maximal Green-isotropic relation is Green-isotropic. -/
theorem isMaximalGreenIsotropic_isGreenIsotropic
    {relation : GreenRelation 𝕜 H}
    (h : IsMaximalGreenIsotropic relation) :
    IsGreenIsotropic relation := by
  intro x hx
  rw [h]
  exact hx

/-- The relation associated with a partial linear operator is its graph. -/
def operatorRelation (operator : H →ₗ.[𝕜] H) : GreenRelation 𝕜 H :=
  operator.graph

/-- For a densely defined operator, the Green adjoint of its graph is exactly
the graph of its Hilbert-space adjoint. -/
theorem operatorRelation_greenAdjoint_eq
    [CompleteSpace H]
    (operator : H →ₗ.[𝕜] H)
    (hDense : Dense (operator.domain : Set H)) :
    greenAdjoint (operatorRelation operator) =
      operatorRelation operator.adjoint := by
  simpa [greenAdjoint, operatorRelation] using
    (LinearPMap.adjoint_graph_eq_graph_adjoint
      (T := operator) hDense).symm

/-- The graph Green identity is precisely formal symmetry of the partial
operator. -/
theorem operatorRelation_isGreenIsotropic_iff
    (operator : H →ₗ.[𝕜] H) :
    IsGreenIsotropic (operatorRelation operator) ↔
      operator.IsFormalAdjoint operator := by
  constructor
  · intro h x y
    have hgreen := isGreenIsotropic_green_identity h
      (LinearPMap.mem_graph operator x)
      (LinearPMap.mem_graph operator y)
    exact sub_eq_zero.mp (by simpa [greenForm, operatorRelation] using hgreen)
  · intro h
    rw [isGreenIsotropic_iff_green_identity]
    intro x hx y hy
    rcases (LinearPMap.mem_graph_iff operator).mp hx with
      ⟨xd, hxd, hxv⟩
    rcases (LinearPMap.mem_graph_iff operator).mp hy with
      ⟨yd, hyd, hyv⟩
    simpa [greenForm, hxd, hxv, hyd, hyv] using
      (sub_eq_zero.mpr (h xd yd))

/-- For a densely defined partial operator, maximal Green-isotropy of the
graph is equivalent to Hilbert-space self-adjointness. -/
theorem operatorRelation_isMaximalGreenIsotropic_iff
    [CompleteSpace H]
    (operator : H →ₗ.[𝕜] H)
    (hDense : Dense (operator.domain : Set H)) :
    IsMaximalGreenIsotropic (operatorRelation operator) ↔
      IsSelfAdjoint operator := by
  rw [LinearPMap.isSelfAdjoint_def]
  constructor
  · intro h
    apply LinearPMap.eq_of_eq_graph
    calc
      operator.adjoint.graph =
          greenAdjoint (operatorRelation operator) :=
        (operatorRelation_greenAdjoint_eq operator hDense).symm
      _ = operatorRelation operator := h
      _ = operator.graph := rfl
  · intro h
    rw [IsMaximalGreenIsotropic,
      operatorRelation_greenAdjoint_eq operator hDense, h]

/-- A self-adjoint partial operator has a maximal Green-isotropic graph. -/
theorem operatorRelation_isMaximalGreenIsotropic
    [CompleteSpace H]
    (operator : H →ₗ.[𝕜] H) (hSelf : IsSelfAdjoint operator) :
    IsMaximalGreenIsotropic (operatorRelation operator) :=
  (operatorRelation_isMaximalGreenIsotropic_iff operator
    hSelf.dense_domain).mpr hSelf

/-! ## Concrete reference relation -/

/-- The graph relation of maximal logarithmic multiplication on the ambient
Naimark space. -/
def logarithmicGreenRelation : GreenRelation ℝ Infinite.NaimarkSpace :=
  operatorRelation Infinite.logarithmicMultiplication

/-- Exact graph membership for the logarithmic reference relation. -/
theorem mem_logarithmicGreenRelation_iff
    (pair : Infinite.NaimarkSpace × Infinite.NaimarkSpace) :
    pair ∈ logarithmicGreenRelation ↔
      ∃ f : Infinite.logarithmicMultiplication.domain,
        pair = ((f : Infinite.NaimarkSpace),
          Infinite.logarithmicMultiplication f) := by
  constructor
  · intro hpair
    rcases (LinearPMap.mem_graph_iff'
      Infinite.logarithmicMultiplication).mp hpair with ⟨f, hvalue⟩
    exact ⟨f, hvalue.symm⟩
  · rintro ⟨f, rfl⟩
    exact LinearPMap.mem_graph Infinite.logarithmicMultiplication f

/-- The concrete Green identity on two logarithmic-domain vectors. -/
theorem logarithmicGreenRelation_green_identity
    (f g : Infinite.logarithmicMultiplication.domain) :
    greenForm (𝕜 := ℝ)
      ((f : Infinite.NaimarkSpace), Infinite.logarithmicMultiplication f)
      ((g : Infinite.NaimarkSpace), Infinite.logarithmicMultiplication g) = 0 := by
  simpa [greenForm] using
    (sub_eq_zero.mpr
      (Infinite.logarithmicMultiplication_isFormalAdjoint f g))

/-- The graph of logarithmic multiplication is Green-isotropic. -/
theorem logarithmicGreenRelation_isGreenIsotropic :
    IsGreenIsotropic logarithmicGreenRelation := by
  rw [logarithmicGreenRelation,
    operatorRelation_isGreenIsotropic_iff]
  exact Infinite.logarithmicMultiplication_isFormalAdjoint

/-- The graph of maximal logarithmic multiplication is maximal
Green-isotropic. -/
theorem logarithmicGreenRelation_isMaximalGreenIsotropic :
    IsMaximalGreenIsotropic logarithmicGreenRelation := by
  exact operatorRelation_isMaximalGreenIsotropic
    Infinite.logarithmicMultiplication
    Infinite.logarithmicMultiplication_isSelfAdjoint

/-- The Green adjoint of the logarithmic reference graph is the graph itself. -/
theorem logarithmicGreenRelation_greenAdjoint_eq :
    greenAdjoint logarithmicGreenRelation = logarithmicGreenRelation :=
  logarithmicGreenRelation_isMaximalGreenIsotropic

/-- The logarithmic maximal Green relation is closed in the product Hilbert
space. -/
theorem logarithmicGreenRelation_isClosed :
    IsClosed (logarithmicGreenRelation :
      Set (Infinite.NaimarkSpace × Infinite.NaimarkSpace)) := by
  simpa [logarithmicGreenRelation, operatorRelation,
    LinearPMap.IsClosed] using Infinite.logarithmicMultiplication_isClosed

end NativeCarrySpectralWeyl.Boundary
