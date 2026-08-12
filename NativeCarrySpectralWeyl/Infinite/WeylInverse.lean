import NativeCarrySpectralWeyl.Infinite.ComplexifiedCauchy
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The densely defined all-bases Weyl inverse

Away from the real axis, the complete realified Cauchy block is bounded,
injective, and has dense range.  Its inverse is therefore canonically defined
on that range.  Mathlib's `LinearPMap.inverse` packages precisely this
construction.

This file defines

`W_infinity(lambda) = M_infinity(lambda)⁻¹`

as a partial real-linear operator on the realified canonical
complexification.  Its domain is exactly `range(M_infinity(lambda))`, hence is
dense.  The graph of the bounded Cauchy block is closed, and swapping the two
coordinates of that graph proves that the inverse is closed.  Exact left and
right inverse laws are also recorded.

The result is a closed, densely defined `LinearPMap`.  No boundedness or
unboundedness assertion for this inverse is made here.
-/

open scoped RealInnerProductSpace
open Set

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

/-- The bounded complete Cauchy block viewed as an everywhere-defined partial
linear operator. -/
def allBasesCauchyPMap (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →ₗ.[ℝ]
      RealifiedCameraComplexification :=
  (allBasesCauchyBlock lambda hlambda).toLinearMap.toPMap ⊤

/-- The bounded Cauchy partial map is defined everywhere. -/
@[simp]
theorem allBasesCauchyPMap_domain (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    (allBasesCauchyPMap lambda hlambda).domain = ⊤ := by
  rfl

/-- On its full domain, the partial map acts by the complete Cauchy block. -/
@[simp]
theorem allBasesCauchyPMap_apply (lambda : ℂ)
    (hlambda : lambda.im ≠ 0)
    (z : (allBasesCauchyPMap lambda hlambda).domain) :
    allBasesCauchyPMap lambda hlambda z =
      allBasesCauchyBlock lambda hlambda z := by
  rfl

/-- The full-domain partial Cauchy map is injective. -/
theorem allBasesCauchyPMap_toFun_injective (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    Function.Injective (allBasesCauchyPMap lambda hlambda).toFun := by
  intro z w hzw
  apply Subtype.ext
  apply allBasesCauchyBlock_injective lambda hlambda
  simpa using hzw

/-- The full-domain partial Cauchy map has trivial kernel. -/
theorem allBasesCauchyPMap_ker_eq_bot (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    LinearMap.ker (allBasesCauchyPMap lambda hlambda).toFun = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (allBasesCauchyPMap_toFun_injective lambda hlambda)

/-- Passing through the full-domain subtype does not change the range of the
bounded Cauchy block. -/
theorem allBasesCauchyPMap_range (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    LinearMap.range (allBasesCauchyPMap lambda hlambda).toFun =
      LinearMap.range
        (allBasesCauchyBlock lambda hlambda :
          RealifiedCameraComplexification →ₗ[ℝ]
            RealifiedCameraComplexification) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z, by simp⟩, rfl⟩

/-- The all-bases Weyl operator is the inverse of the complete Cauchy block,
defined on the latter's range. -/
def allBasesWeylInverse (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →ₗ.[ℝ]
      RealifiedCameraComplexification :=
  (allBasesCauchyPMap lambda hlambda).inverse

/-- The domain of the Weyl inverse is exactly the range of the bounded Cauchy
block. -/
theorem allBasesWeylInverse_domain (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    (allBasesWeylInverse lambda hlambda).domain =
      LinearMap.range
        (allBasesCauchyBlock lambda hlambda :
          RealifiedCameraComplexification →ₗ[ℝ]
            RealifiedCameraComplexification) := by
  rw [allBasesWeylInverse, LinearPMap.inverse_domain,
    allBasesCauchyPMap_range]

/-- The all-bases Weyl inverse is densely defined. -/
theorem allBasesWeylInverse_denseDomain (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    Dense ((allBasesWeylInverse lambda hlambda).domain :
      Set RealifiedCameraComplexification) := by
  rw [allBasesWeylInverse_domain]
  exact allBasesCauchyBlock_denseRange lambda hlambda

/-- The graph of the everywhere-defined bounded Cauchy partial map is closed. -/
theorem allBasesCauchyPMap_isClosed (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    (allBasesCauchyPMap lambda hlambda).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph :
      ((allBasesCauchyPMap lambda hlambda).graph :
          Set (RealifiedCameraComplexification ×
            RealifiedCameraComplexification)) =
        {z | allBasesCauchyBlock lambda hlambda z.1 = z.2} := by
    ext z
    simp [LinearPMap.mem_graph_iff, allBasesCauchyPMap]
  rw [hgraph]
  exact isClosed_eq
    ((allBasesCauchyBlock lambda hlambda).continuous.comp continuous_fst)
    continuous_snd

/-- The inverse graph is obtained by swapping the two coordinates of the
Cauchy graph. -/
theorem allBasesWeylInverse_graph (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    (allBasesWeylInverse lambda hlambda).graph =
      (allBasesCauchyPMap lambda hlambda).graph.map
        (LinearEquiv.prodComm ℝ
          RealifiedCameraComplexification
          RealifiedCameraComplexification :
          (RealifiedCameraComplexification ×
              RealifiedCameraComplexification) →ₗ[ℝ]
            (RealifiedCameraComplexification ×
              RealifiedCameraComplexification)) := by
  exact LinearPMap.inverse_graph
    (allBasesCauchyPMap_ker_eq_bot lambda hlambda)

/-- The all-bases Weyl inverse is a closed partial operator. -/
theorem allBasesWeylInverse_isClosed (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    (allBasesWeylInverse lambda hlambda).IsClosed := by
  exact (LinearPMap.inverse_closed_iff
    (allBasesCauchyPMap_ker_eq_bot lambda hlambda)).2
      (allBasesCauchyPMap_isClosed lambda hlambda)

/-- A source vector, viewed in the everywhere-defined Cauchy domain. -/
def allBasesCauchyDomainElement (lambda : ℂ)
    (hlambda : lambda.im ≠ 0)
    (z : RealifiedCameraComplexification) :
    (allBasesCauchyPMap lambda hlambda).domain :=
  ⟨z, by simp⟩

/-- The Cauchy image of a source vector, viewed in the domain of the Weyl
inverse. -/
def allBasesCauchyRangeElement (lambda : ℂ)
    (hlambda : lambda.im ≠ 0)
    (z : RealifiedCameraComplexification) :
    (allBasesWeylInverse lambda hlambda).domain :=
  ⟨allBasesCauchyBlock lambda hlambda z, by
    rw [allBasesWeylInverse_domain]
    exact LinearMap.mem_range_self _ z⟩

/-- The Weyl inverse is a left inverse of the complete Cauchy block. -/
@[simp]
theorem allBasesWeylInverse_apply_cauchyRangeElement (lambda : ℂ)
    (hlambda : lambda.im ≠ 0)
    (z : RealifiedCameraComplexification) :
    allBasesWeylInverse lambda hlambda
        (allBasesCauchyRangeElement lambda hlambda z) = z := by
  simpa [allBasesWeylInverse, allBasesCauchyDomainElement] using
    (LinearPMap.inverse_apply_eq
      (allBasesCauchyPMap_ker_eq_bot lambda hlambda)
      (x := allBasesCauchyDomainElement lambda hlambda z)
      (y := allBasesCauchyRangeElement lambda hlambda z) (by rfl))

/-- Applying the complete Cauchy block after the Weyl inverse recovers every
vector in the inverse domain. -/
theorem allBasesCauchyBlock_apply_weylInverse (lambda : ℂ)
    (hlambda : lambda.im ≠ 0)
    (z : (allBasesWeylInverse lambda hlambda).domain) :
    allBasesCauchyBlock lambda hlambda
        (allBasesWeylInverse lambda hlambda z) = z := by
  rcases z with ⟨z, hz⟩
  rw [allBasesWeylInverse_domain] at hz
  rcases hz with ⟨x, rfl⟩
  have hinverse :
      allBasesWeylInverse lambda hlambda
          ⟨allBasesCauchyBlock lambda hlambda x, hz⟩ = x := by
    rw [show
      (⟨allBasesCauchyBlock lambda hlambda x, hz⟩ :
        (allBasesWeylInverse lambda hlambda).domain) =
          allBasesCauchyRangeElement lambda hlambda x from Subtype.ext rfl]
    exact allBasesWeylInverse_apply_cauchyRangeElement lambda hlambda x
  change allBasesCauchyBlock lambda hlambda
      (allBasesWeylInverse lambda hlambda
        ⟨allBasesCauchyBlock lambda hlambda x, hz⟩) =
    allBasesCauchyBlock lambda hlambda x
  rw [hinverse]

/-- The range of the Weyl inverse is the whole realified complexification. -/
theorem allBasesWeylInverse_range_eq_top (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    LinearMap.range (allBasesWeylInverse lambda hlambda).toFun = ⊤ := by
  rw [allBasesWeylInverse, LinearPMap.inverse_range
    (allBasesCauchyPMap_ker_eq_bot lambda hlambda),
    allBasesCauchyPMap_domain]

/-- The Weyl inverse is surjective onto the realified complexification. -/
theorem allBasesWeylInverse_surjective (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    Function.Surjective (allBasesWeylInverse lambda hlambda).toFun := by
  rw [← LinearMap.range_eq_top]
  exact allBasesWeylInverse_range_eq_top lambda hlambda

end NativeCarrySpectralWeyl.Infinite
