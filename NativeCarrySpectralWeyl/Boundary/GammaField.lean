import NativeCarrySpectralWeyl.Boundary.SourceRelation
import NativeCarrySpectralWeyl.Infinite.ComplexifiedResolvent
import NativeCarrySpectralWeyl.Infinite.WeylUnbounded

/-!
# Gamma field and realified carry Weyl family

For a nonreal spectral parameter `lambda`, the research notes solve the defect
equation for the source-extended relation by

`f = (lambda - Y)^(-1) V u`.

The current all-bases construction is a real Hilbert-space model.  Therefore
this file works in the already established canonical real `2 x 2`
complexification.  The preceding ambient-resolvent module proves that this
bounded resolvent value lies in the exact maximal domain of the unbounded
logarithmic multiplier and satisfies

`lambda f = Y f + V u`.

The source-to-defect map is the bounded gamma field.  Its Weyl boundary trace
is the compressed Cauchy block.  Reparameterizing the same defect states by
the trace on the exact dense range of that block gives a partial gamma field;
its second boundary value is exactly the previously constructed closed
unbounded Weyl inverse.

No independent complex scalar action and no everywhere-defined inverse are
introduced.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace NativeCarrySpectralWeyl.Boundary

open NativeCarrySpectralWeyl.Infinite

/-- Source-parameterized realified gamma field
`u |-> (lambda-Y)^(-1) V u`. -/
def carryGammaSource (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  logarithmicResolventBlock lambda hlambda ∘L realifiedNaimarkPort

@[simp] theorem carryGammaSource_fst
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    (carryGammaSource lambda hlambda u).fst =
      logarithmicResolventRealOperator lambda hlambda (naimarkIsometry u.fst) -
        logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry u.snd) := by
  simp [carryGammaSource, ContinuousLinearMap.comp_apply]

@[simp] theorem carryGammaSource_snd
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    (carryGammaSource lambda hlambda u).snd =
      logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry u.fst) +
        logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry u.snd) := by
  simp [carryGammaSource, ContinuousLinearMap.comp_apply]

/-- The source-parameterized gamma field is injective: the defect vector
remembers its unique boundary source. -/
theorem carryGammaSource_injective
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Function.Injective (carryGammaSource lambda hlambda) := by
  intro u v huv
  apply realifiedNaimarkPort_injective
  apply logarithmicResolventBlock_injective lambda hlambda
  simpa [carryGammaSource, ContinuousLinearMap.comp_apply] using huv

/-- The gamma field with its codomain restricted to the exact realified
maximal logarithmic domain. -/
def carryGammaIntoDomain (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →ₗ[ℝ]
      RealifiedLogarithmicDomain :=
  (logarithmicResolventIntoDomain lambda hlambda).comp
    realifiedNaimarkPort.toLinearMap

@[simp] theorem carryGammaIntoDomain_fst_coe
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    ((carryGammaIntoDomain lambda hlambda u).1 : NaimarkSpace) =
      (carryGammaSource lambda hlambda u).fst :=
  rfl

@[simp] theorem carryGammaIntoDomain_snd_coe
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    ((carryGammaIntoDomain lambda hlambda u).2 : NaimarkSpace) =
      (carryGammaSource lambda hlambda u).snd :=
  rfl

/-- A source-parameterized defect state is a pair `(f, lambda f)` in the
realified ambient space. -/
def carryDefectStateFromSource
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →ₗ[ℝ]
      (RealifiedNaimarkComplexification ×
        RealifiedNaimarkComplexification) where
  toFun u :=
    (carryGammaSource lambda hlambda u,
      realifiedNaimarkScalar lambda (carryGammaSource lambda hlambda u))
  map_add' u v := by simp
  map_smul' c u := by simp

/-- The canonical parametrization of the defect subspace is injective. -/
theorem carryDefectStateFromSource_injective
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Function.Injective (carryDefectStateFromSource lambda hlambda) := by
  intro u v huv
  apply carryGammaSource_injective lambda hlambda
  exact congrArg Prod.fst huv

/-- The defect equation in the source-extended relation:
`lambda gamma(lambda)u = Y gamma(lambda)u + V u`. -/
theorem carryGammaSource_defect_equation
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    realifiedNaimarkScalar lambda (carryGammaSource lambda hlambda u) =
      realifiedLogarithmicMultiplication
          (carryGammaIntoDomain lambda hlambda u) +
        realifiedNaimarkPort u := by
  have heq := realified_logarithmic_resolvent_equation lambda hlambda
    (realifiedNaimarkPort u)
  change realifiedNaimarkScalar lambda
      (logarithmicResolventBlock lambda hlambda (realifiedNaimarkPort u)) =
    realifiedLogarithmicMultiplication
      (logarithmicResolventDomainElement lambda hlambda
        (realifiedNaimarkPort u)) + realifiedNaimarkPort u
  exact heq

/-- The gamma vector is the unique maximal-domain solution of the realified
defect equation with source `u`. -/
theorem carryGammaIntoDomain_unique
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification)
    (f : RealifiedLogarithmicDomain)
    (hdefect :
      realifiedNaimarkScalar lambda
          (realifiedLogarithmicDomainEmbedding f) =
        realifiedLogarithmicMultiplication f + realifiedNaimarkPort u) :
    f = carryGammaIntoDomain lambda hlambda u := by
  apply realifiedLambdaMinusLogarithmicMultiplication_injective lambda hlambda
  calc
    realifiedLambdaMinusLogarithmicMultiplication lambda f =
        realifiedNaimarkPort u := by
      change realifiedNaimarkScalar lambda
          (realifiedLogarithmicDomainEmbedding f) -
            realifiedLogarithmicMultiplication f = realifiedNaimarkPort u
      rw [hdefect]
      module
    _ = realifiedLambdaMinusLogarithmicMultiplication lambda
          (carryGammaIntoDomain lambda hlambda u) := by
      change realifiedNaimarkPort u =
        realifiedLambdaMinusLogarithmicMultiplication lambda
          (logarithmicResolventIntoDomain lambda hlambda
            (realifiedNaimarkPort u))
      rw [realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent]

/-- First Weyl boundary trace of a source-parameterized defect state. -/
def carryDefectGammaZero
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →L[ℝ]
      RealifiedCameraComplexification :=
  realifiedNaimarkAdjoint ∘L carryGammaSource lambda hlambda

/-- Second Weyl boundary trace of a source-parameterized defect state. -/
def carryDefectGammaOne
    (_lambda : ℂ) (_hlambda : _lambda.im ≠ 0) :
    RealifiedCameraComplexification →L[ℝ]
      RealifiedCameraComplexification :=
  ContinuousLinearMap.id ℝ RealifiedCameraComplexification

/-- The first defect boundary trace is exactly the compressed Cauchy block. -/
theorem carryDefectGammaZero_eq_allBasesCauchyBlock
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    carryDefectGammaZero lambda hlambda =
      allBasesCauchyBlock lambda hlambda := by
  rw [allBasesCauchyBlock_eq_realified_compression]
  rfl

@[simp] theorem carryDefectGammaZero_apply
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    carryDefectGammaZero lambda hlambda u =
      allBasesCauchyBlock lambda hlambda u := by
  rw [carryDefectGammaZero_eq_allBasesCauchyBlock]

@[simp] theorem carryDefectGammaOne_apply
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    carryDefectGammaOne lambda hlambda u = u := by
  rfl

/-- Defect subspace at `lambda`, represented as the range of the canonical
source-parametrized defect-state map. -/
def carryDefectSpace (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Submodule ℝ
      (RealifiedNaimarkComplexification ×
        RealifiedNaimarkComplexification) :=
  LinearMap.range (carryDefectStateFromSource lambda hlambda)

/-- Exact membership in the realified defect subspace. -/
theorem mem_carryDefectSpace_iff
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (state : RealifiedNaimarkComplexification ×
      RealifiedNaimarkComplexification) :
    state ∈ carryDefectSpace lambda hlambda ↔
      ∃ u : RealifiedCameraComplexification,
        state =
          (carryGammaSource lambda hlambda u,
            realifiedNaimarkScalar lambda
              (carryGammaSource lambda hlambda u)) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩

/-- Trace-parameterized gamma field on the exact domain of the Weyl inverse.
It is partial because that domain is the dense, generally proper range of the
compressed Cauchy block. -/
def carryGammaField (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →ₗ.[ℝ]
      RealifiedNaimarkComplexification where
  domain := (allBasesWeylInverse lambda hlambda).domain
  toFun := (carryGammaSource lambda hlambda).toLinearMap.comp
    (allBasesWeylInverse lambda hlambda).toFun

/-- The gamma field has exactly the dense Weyl-inverse domain. -/
@[simp] theorem carryGammaField_domain
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    (carryGammaField lambda hlambda).domain =
      (allBasesWeylInverse lambda hlambda).domain :=
  rfl

/-- The trace-parametrized gamma field is densely defined. -/
theorem carryGammaField_denseDomain
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Dense ((carryGammaField lambda hlambda).domain :
      Set RealifiedCameraComplexification) := by
  rw [carryGammaField_domain]
  exact allBasesWeylInverse_denseDomain lambda hlambda

@[simp] theorem carryGammaField_apply
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (trace : (carryGammaField lambda hlambda).domain) :
    carryGammaField lambda hlambda trace =
      carryGammaSource lambda hlambda
        (allBasesWeylInverse lambda hlambda trace) :=
  rfl

/-- Every trace-parametrized gamma vector satisfies the defect equation with
source equal to the Weyl inverse of that trace. -/
theorem carryGammaField_defect_equation
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (trace : (carryGammaField lambda hlambda).domain) :
    realifiedNaimarkScalar lambda
        (carryGammaField lambda hlambda trace) =
      realifiedLogarithmicMultiplication
          (carryGammaIntoDomain lambda hlambda
            (allBasesWeylInverse lambda hlambda trace)) +
        realifiedNaimarkPort
          (allBasesWeylInverse lambda hlambda trace) := by
  rw [carryGammaField_apply]
  exact carryGammaSource_defect_equation lambda hlambda
    (allBasesWeylInverse lambda hlambda trace)

/-- The trace-parametrized gamma vector is the unique maximal-domain
solution of its defect equation. -/
theorem carryGammaFieldIntoDomain_unique
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (trace : (carryGammaField lambda hlambda).domain)
    (f : RealifiedLogarithmicDomain)
    (hdefect :
      realifiedNaimarkScalar lambda
          (realifiedLogarithmicDomainEmbedding f) =
        realifiedLogarithmicMultiplication f +
          realifiedNaimarkPort
            (allBasesWeylInverse lambda hlambda trace)) :
    f = carryGammaIntoDomain lambda hlambda
      (allBasesWeylInverse lambda hlambda trace) :=
  carryGammaIntoDomain_unique lambda hlambda
    (allBasesWeylInverse lambda hlambda trace) f hdefect

/-- The first boundary trace of the trace-parametrized gamma field is the
input trace itself. -/
theorem carryGammaField_gammaZero
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (trace : (carryGammaField lambda hlambda).domain) :
    realifiedNaimarkAdjoint (carryGammaField lambda hlambda trace) =
      (trace : RealifiedCameraComplexification) := by
  rw [carryGammaField_apply]
  change carryDefectGammaZero lambda hlambda
      (allBasesWeylInverse lambda hlambda trace) = trace
  rw [carryDefectGammaZero_apply]
  exact allBasesCauchyBlock_apply_weylInverse lambda hlambda trace

/-- The second boundary trace on the gamma field is exactly the previously
constructed closed unbounded Weyl inverse. -/
theorem carryGammaField_gammaOne_eq_weylInverse
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (trace : (carryGammaField lambda hlambda).domain) :
    carryDefectGammaOne lambda hlambda
        (allBasesWeylInverse lambda hlambda trace) =
      allBasesWeylInverse lambda hlambda trace :=
  carryDefectGammaOne_apply lambda hlambda
    (allBasesWeylInverse lambda hlambda trace)

/-- Source and trace parametrizations agree on every canonical Cauchy-range
element. -/
theorem carryGammaField_apply_cauchyRangeElement
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    carryGammaField lambda hlambda
        (allBasesCauchyRangeElement lambda hlambda u) =
      carryGammaSource lambda hlambda u := by
  rw [carryGammaField_apply,
    allBasesWeylInverse_apply_cauchyRangeElement]

/-- On every source-parametrized defect state, the Weyl boundary law is
`Gamma_1 = M(lambda)^(-1) Gamma_0`. -/
theorem carryDefect_weyl_boundary_law
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    allBasesWeylInverse lambda hlambda
        (allBasesCauchyRangeElement lambda hlambda u) =
      carryDefectGammaOne lambda hlambda u := by
  rw [allBasesWeylInverse_apply_cauchyRangeElement,
    carryDefectGammaOne_apply]

/-- The boundary Weyl family of the carry gamma field is definitionally the
closed densely defined inverse of the compressed resolvent. -/
def carryBoundaryWeylFamily
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →ₗ.[ℝ]
      RealifiedCameraComplexification :=
  allBasesWeylInverse lambda hlambda

theorem carryBoundaryWeylFamily_eq_allBasesWeylInverse
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    carryBoundaryWeylFamily lambda hlambda =
      allBasesWeylInverse lambda hlambda :=
  rfl

/-- The gamma field has boundary values
`(Gamma_0 gamma(lambda) trace, Gamma_1 gamma(lambda) trace) =
  (trace, W(lambda) trace)` on its exact dense domain. -/
theorem carryGammaField_boundary_values
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (trace : (carryGammaField lambda hlambda).domain) :
    (realifiedNaimarkAdjoint (carryGammaField lambda hlambda trace),
      carryDefectGammaOne lambda hlambda
        (allBasesWeylInverse lambda hlambda trace)) =
      ((trace : RealifiedCameraComplexification),
        carryBoundaryWeylFamily lambda hlambda trace) := by
  apply Prod.ext
  · exact carryGammaField_gammaZero lambda hlambda trace
  · exact carryGammaField_gammaOne_eq_weylInverse lambda hlambda trace

/-- Consequently the Weyl boundary law on the gamma field is exactly
`Gamma_1 = W(lambda) Gamma_0`. -/
theorem carryGammaField_weyl_boundary_law
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (trace : (carryGammaField lambda hlambda).domain) :
    carryDefectGammaOne lambda hlambda
        (allBasesWeylInverse lambda hlambda trace) =
      carryBoundaryWeylFamily lambda hlambda trace :=
  congrArg Prod.snd (carryGammaField_boundary_values lambda hlambda trace)

/-- The realized boundary Weyl family is closed. -/
theorem carryBoundaryWeylFamily_isClosed
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    (carryBoundaryWeylFamily lambda hlambda).IsClosed :=
  allBasesWeylInverse_isClosed lambda hlambda

/-- The realized boundary Weyl family is densely defined. -/
theorem carryBoundaryWeylFamily_denseDomain
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Dense ((carryBoundaryWeylFamily lambda hlambda).domain :
      Set RealifiedCameraComplexification) :=
  allBasesWeylInverse_denseDomain lambda hlambda

/-- The realized boundary Weyl family admits no global norm bound on its
exact domain. -/
theorem carryBoundaryWeylFamily_not_normBounded
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    ¬ ∃ C : ℝ,
      ∀ trace : (carryBoundaryWeylFamily lambda hlambda).domain,
        ‖carryBoundaryWeylFamily lambda hlambda trace‖ ≤ C * ‖trace‖ :=
  allBasesWeylInverse_not_normBounded lambda hlambda

end NativeCarrySpectralWeyl.Boundary
