import NativeCarrySpectralWeyl.Infinite.Cauchy
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The canonical real block of the all-bases Cauchy family

The all-bases camera Hilbert space is real.  This file passes to the underlying
real Hilbert space of its canonical complexification,

`H_C,real = WithLp 2 (H × H)`,

and combines the real and imaginary Cauchy components into the standard block

`(x, y) ↦ (A x - B y, B x + A y)`.

Here `A = Re M_infinity(lambda)` and `B = Im M_infinity(lambda)`.  This is the
real `2 × 2` model of the complex operator `M_infinity(lambda)`; no independent
complex scalar action is asserted in this file.

The strict anti-Herglotz sign of `B` proves that the full block is injective.
Its adjoint is the block at the conjugate spectral parameter, which is also
injective.  The Hilbert-space identity

`range(T)ᗮ = ker(T†)`

then proves that the block has dense range.  These are the two inputs needed
to define the inverse Weyl operator as a densely defined `LinearPMap`.
-/

open scoped RealInnerProductSpace ComplexConjugate
open Set

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

/-- The underlying real Hilbert space of the canonical complexification of
the all-bases camera Hilbert space. -/
abbrev RealifiedCameraComplexification :=
  WithLp 2 (CameraHilbert × CameraHilbert)

/-- The standard real block representing the complex operator `A + i B`. -/
def realifiedCameraBlock (A B : CameraHilbert →L[ℝ] CameraHilbert) :
    RealifiedCameraComplexification →L[ℝ]
      RealifiedCameraComplexification :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ CameraHilbert CameraHilbert).symm.toContinuousLinearMap ∘L
    ((A.coprod (-B)).prod (B.coprod A)) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ CameraHilbert CameraHilbert).toContinuousLinearMap

/-- Coordinate formula for the canonical real block. -/
@[simp]
theorem realifiedCameraBlock_fst (A B : CameraHilbert →L[ℝ] CameraHilbert)
    (z : RealifiedCameraComplexification) :
    (realifiedCameraBlock A B z).fst = A z.fst - B z.snd := by
  simp [realifiedCameraBlock, ContinuousLinearMap.comp_apply, sub_eq_add_neg]

/-- Coordinate formula for the second component of the canonical real block. -/
@[simp]
theorem realifiedCameraBlock_snd (A B : CameraHilbert →L[ℝ] CameraHilbert)
    (z : RealifiedCameraComplexification) :
    (realifiedCameraBlock A B z).snd = B z.fst + A z.snd := by
  simp [realifiedCameraBlock, ContinuousLinearMap.comp_apply]

/-- In the skew quadratic form of a real block, the self-adjoint real part
cancels and only the imaginary component remains. -/
theorem realifiedCameraBlock_skewQuadratic
    (A B : CameraHilbert →L[ℝ] CameraHilbert)
    (hA : (A : CameraHilbert →ₗ[ℝ] CameraHilbert).IsSymmetric)
    (z : RealifiedCameraComplexification) :
    inner ℝ z.fst (realifiedCameraBlock A B z).snd -
        inner ℝ z.snd (realifiedCameraBlock A B z).fst =
      inner ℝ z.fst (B z.fst) + inner ℝ z.snd (B z.snd) := by
  rw [realifiedCameraBlock_fst, realifiedCameraBlock_snd]
  simp only [inner_add_right, inner_sub_right]
  have hcross : inner ℝ z.fst (A z.snd) = inner ℝ z.snd (A z.fst) := by
    calc
      inner ℝ z.fst (A z.snd) = inner ℝ (A z.fst) z.snd :=
        (hA.apply_clm z.fst z.snd).symm
      _ = inner ℝ z.snd (A z.fst) := real_inner_comm _ _
  linarith

/-- The adjoint of the block `A + i B` is the conjugate block `A - i B`
when both components are symmetric. -/
theorem realifiedCameraBlock_adjoint
    (A B : CameraHilbert →L[ℝ] CameraHilbert)
    (hA : (A : CameraHilbert →ₗ[ℝ] CameraHilbert).IsSymmetric)
    (hB : (B : CameraHilbert →ₗ[ℝ] CameraHilbert).IsSymmetric) :
    (realifiedCameraBlock A B).adjoint = realifiedCameraBlock A (-B) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro z w
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change
    inner ℝ (realifiedCameraBlock A (-B) z).fst w.fst +
        inner ℝ (realifiedCameraBlock A (-B) z).snd w.snd =
      inner ℝ z.fst (realifiedCameraBlock A B w).fst +
        inner ℝ z.snd (realifiedCameraBlock A B w).snd
  rw [realifiedCameraBlock_fst, realifiedCameraBlock_snd,
    realifiedCameraBlock_fst, realifiedCameraBlock_snd]
  simp only [neg_apply, sub_neg_eq_add]
  simp only [inner_add_left, inner_neg_left, inner_sub_right, inner_add_right]
  have hA₁ : inner ℝ (A z.fst) w.fst = inner ℝ z.fst (A w.fst) :=
    hA.apply_clm z.fst w.fst
  have hA₂ : inner ℝ (A z.snd) w.snd = inner ℝ z.snd (A w.snd) :=
    hA.apply_clm z.snd w.snd
  have hB₁ : inner ℝ (B z.snd) w.fst = inner ℝ z.snd (B w.fst) :=
    hB.apply_clm z.snd w.fst
  have hB₂ : inner ℝ (B z.fst) w.snd = inner ℝ z.fst (B w.snd) :=
    hB.apply_clm z.fst w.snd
  rw [hA₁, hA₂, hB₁, hB₂]
  ring

/-- The complete all-bases Cauchy operator on the realified canonical
complexification. -/
def allBasesCauchyBlock (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification →L[ℝ]
      RealifiedCameraComplexification :=
  realifiedCameraBlock
    (allBasesCauchyRealPart lambda hlambda)
    (allBasesCauchyImaginaryPart lambda hlambda)

/-- First-coordinate formula for the complete all-bases Cauchy block. -/
@[simp]
theorem allBasesCauchyBlock_fst (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (z : RealifiedCameraComplexification) :
    (allBasesCauchyBlock lambda hlambda z).fst =
      allBasesCauchyRealPart lambda hlambda z.fst -
        allBasesCauchyImaginaryPart lambda hlambda z.snd := by
  exact realifiedCameraBlock_fst _ _ z

/-- Second-coordinate formula for the complete all-bases Cauchy block. -/
@[simp]
theorem allBasesCauchyBlock_snd (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (z : RealifiedCameraComplexification) :
    (allBasesCauchyBlock lambda hlambda z).snd =
      allBasesCauchyImaginaryPart lambda hlambda z.fst +
        allBasesCauchyRealPart lambda hlambda z.snd := by
  exact realifiedCameraBlock_snd _ _ z

/-- The skew quadratic form of the complete Cauchy block is the sum of the
two imaginary-component quadratic forms. -/
theorem allBasesCauchyBlock_skewQuadratic (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (z : RealifiedCameraComplexification) :
    inner ℝ z.fst (allBasesCauchyBlock lambda hlambda z).snd -
        inner ℝ z.snd (allBasesCauchyBlock lambda hlambda z).fst =
      inner ℝ z.fst (allBasesCauchyImaginaryPart lambda hlambda z.fst) +
        inner ℝ z.snd
          (allBasesCauchyImaginaryPart lambda hlambda z.snd) := by
  exact realifiedCameraBlock_skewQuadratic _ _
    (allBasesCauchyRealPart_isSelfAdjoint lambda hlambda).isSymmetric z

/-- A nonzero vector in the realified complexification has a nonzero real or
imaginary coordinate. -/
theorem realifiedCameraComplexification_fst_ne_or_snd_ne
    {z : RealifiedCameraComplexification} (hz : z ≠ 0) :
    z.fst ≠ 0 ∨ z.snd ≠ 0 := by
  by_cases hfst : z.fst ≠ 0
  · exact Or.inl hfst
  · right
    intro hsnd
    apply hz
    rw [← WithLp.ofLp_eq_zero]
    exact Prod.ext (not_ne_iff.mp hfst) hsnd

/-- In the upper half-plane the skew quadratic form of the complete Cauchy
block is strictly negative on nonzero vectors. -/
theorem allBasesCauchyBlock_skewQuadratic_neg {lambda : ℂ}
    (hlambda : 0 < lambda.im) {z : RealifiedCameraComplexification}
    (hz : z ≠ 0) :
    inner ℝ z.fst (allBasesCauchyBlock lambda hlambda.ne' z).snd -
        inner ℝ z.snd (allBasesCauchyBlock lambda hlambda.ne' z).fst < 0 := by
  rw [allBasesCauchyBlock_skewQuadratic]
  have hxle := allBasesCauchyImaginaryPart_inner_nonpos hlambda z.fst
  have hyle := allBasesCauchyImaginaryPart_inner_nonpos hlambda z.snd
  rcases realifiedCameraComplexification_fst_ne_or_snd_ne hz with hx | hy
  · have hxlt := allBasesCauchyImaginaryPart_inner_neg hlambda hx
    linarith
  · have hylt := allBasesCauchyImaginaryPart_inner_neg hlambda hy
    linarith

/-- In the lower half-plane the skew quadratic form of the complete Cauchy
block is strictly positive on nonzero vectors. -/
theorem allBasesCauchyBlock_skewQuadratic_pos {lambda : ℂ}
    (hlambda : lambda.im < 0) {z : RealifiedCameraComplexification}
    (hz : z ≠ 0) :
    0 < inner ℝ z.fst (allBasesCauchyBlock lambda hlambda.ne z).snd -
        inner ℝ z.snd (allBasesCauchyBlock lambda hlambda.ne z).fst := by
  rw [allBasesCauchyBlock_skewQuadratic]
  have hxle := allBasesCauchyImaginaryPart_inner_nonneg hlambda z.fst
  have hyle := allBasesCauchyImaginaryPart_inner_nonneg hlambda z.snd
  rcases realifiedCameraComplexification_fst_ne_or_snd_ne hz with hx | hy
  · have hxlt := allBasesCauchyImaginaryPart_inner_pos hlambda hx
    linarith
  · have hylt := allBasesCauchyImaginaryPart_inner_pos hlambda hy
    linarith

/-- Away from the real axis, the complete all-bases Cauchy block is
injective. -/
theorem allBasesCauchyBlock_injective (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    Function.Injective (allBasesCauchyBlock lambda hlambda) := by
  intro z w hzw
  have hkernel : allBasesCauchyBlock lambda hlambda (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  have hsub : z - w = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hlambda with hlower | hupper
    · have hstrict := allBasesCauchyBlock_skewQuadratic_pos hlower hne
      rw [hkernel] at hstrict
      simp at hstrict
    · have hstrict := allBasesCauchyBlock_skewQuadratic_neg hupper hne
      rw [hkernel] at hstrict
      simp at hstrict
  exact sub_eq_zero.mp hsub

/-- Conjugating the parameter gives the conjugate real block. -/
theorem allBasesCauchyBlock_conj (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    allBasesCauchyBlock (conj lambda) (by simpa using hlambda) =
      realifiedCameraBlock
        (allBasesCauchyRealPart lambda hlambda)
        (-allBasesCauchyImaginaryPart lambda hlambda) := by
  unfold allBasesCauchyBlock
  rw [allBasesCauchyRealPart_conj lambda hlambda,
    allBasesCauchyImaginaryPart_conj lambda hlambda]

/-- The adjoint of the complete Cauchy block is the block at the conjugate
spectral parameter. -/
theorem allBasesCauchyBlock_adjoint (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    (allBasesCauchyBlock lambda hlambda).adjoint =
      allBasesCauchyBlock (conj lambda) (by simpa using hlambda) := by
  rw [allBasesCauchyBlock_conj lambda hlambda]
  exact realifiedCameraBlock_adjoint _ _
    (allBasesCauchyRealPart_isSelfAdjoint lambda hlambda).isSymmetric
    (allBasesCauchyImaginaryPart_isSelfAdjoint lambda hlambda).isSymmetric

/-- Away from the real axis, the complete all-bases Cauchy block has dense
range. -/
theorem allBasesCauchyBlock_denseRange (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    Dense (LinearMap.range
      (allBasesCauchyBlock lambda hlambda :
        RealifiedCameraComplexification →ₗ[ℝ]
          RealifiedCameraComplexification) :
      Set RealifiedCameraComplexification) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  rw [← (LinearMap.range
    (allBasesCauchyBlock lambda hlambda :
      RealifiedCameraComplexification →ₗ[ℝ]
        RealifiedCameraComplexification)).orthogonal_orthogonal_eq_closure]
  rw [(allBasesCauchyBlock lambda hlambda).orthogonal_range,
    allBasesCauchyBlock_adjoint lambda hlambda,
    LinearMap.ker_eq_bot.mpr
      (allBasesCauchyBlock_injective (conj lambda) (by simpa using hlambda)),
    Submodule.bot_orthogonal_eq_top]

end NativeCarrySpectralWeyl.Infinite
