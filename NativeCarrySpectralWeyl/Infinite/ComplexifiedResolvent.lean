import NativeCarrySpectralWeyl.Infinite.ComplexifiedCauchy

/-!
# Realified ambient logarithmic resolvent

The camera Cauchy family is already represented on the underlying real
Hilbert space of a canonical complexification.  A gamma field also needs the
corresponding realification of the ambient Naimark space.  This file builds a
generic rectangular real block

`A + i B : E_C,real -> F_C,real`

and uses it for the Naimark port, its adjoint, and the ambient logarithmic
resolvent.  It then proves that compression of the ambient block is exactly
the existing all-bases Cauchy block.

The second half records the domain-sensitive resolvent identities.  Although
the resolvent components are bounded, their images actually lie in the
maximal domain of multiplication by `1 + log x`; applying that unbounded
operator gives the two real components of

`(lambda - Y) (lambda - Y)^(-1) = I`.

No independent complex scalar action is introduced: every statement is made
in the explicit real `2 x 2` model.
-/

open scoped RealInnerProductSpace
open MeasureTheory

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

/-- The standard rectangular real block representing a complex-linear map
`A + iB` between canonical realified product spaces. -/
def realifiedContinuousLinearBlock
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A B : E →L[ℝ] F) :
    WithLp 2 (E × E) →L[ℝ] WithLp 2 (F × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F F).symm.toContinuousLinearMap ∘L
    ((A.coprod (-B)).prod (B.coprod A)) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

@[simp] theorem realifiedContinuousLinearBlock_fst
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A B : E →L[ℝ] F) (z : WithLp 2 (E × E)) :
    (realifiedContinuousLinearBlock A B z).fst =
      A z.fst - B z.snd := by
  simp [realifiedContinuousLinearBlock, ContinuousLinearMap.comp_apply,
    sub_eq_add_neg]

@[simp] theorem realifiedContinuousLinearBlock_snd
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A B : E →L[ℝ] F) (z : WithLp 2 (E × E)) :
    (realifiedContinuousLinearBlock A B z).snd =
      B z.fst + A z.snd := by
  simp [realifiedContinuousLinearBlock, ContinuousLinearMap.comp_apply]

/-- The generic block specializes definitionally to the existing camera
block. -/
theorem realifiedContinuousLinearBlock_camera_eq
    (A B : CameraHilbert →L[ℝ] CameraHilbert) :
    realifiedContinuousLinearBlock A B = realifiedCameraBlock A B :=
  rfl

/-- Underlying real Hilbert space of the canonical complexification of the
ambient Naimark space. -/
abbrev RealifiedNaimarkComplexification :=
  WithLp 2 (NaimarkSpace × NaimarkSpace)

/-- Coordinatewise realification of the all-bases Naimark port. -/
def realifiedNaimarkPort :
    RealifiedCameraComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedContinuousLinearBlock naimarkIsometry.toContinuousLinearMap 0

@[simp] theorem realifiedNaimarkPort_fst
    (u : RealifiedCameraComplexification) :
    (realifiedNaimarkPort u).fst = naimarkIsometry u.fst := by
  simp [realifiedNaimarkPort]

@[simp] theorem realifiedNaimarkPort_snd
    (u : RealifiedCameraComplexification) :
    (realifiedNaimarkPort u).snd = naimarkIsometry u.snd := by
  simp [realifiedNaimarkPort]

/-- Realification preserves injectivity of the all-bases Naimark port. -/
theorem realifiedNaimarkPort_injective :
    Function.Injective realifiedNaimarkPort := by
  intro u v huv
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply naimarkIsometry.injective
    simpa using congrArg WithLp.fst huv
  · apply naimarkIsometry.injective
    simpa using congrArg WithLp.snd huv

/-- Coordinatewise realification of the Naimark adjoint/compression map. -/
def realifiedNaimarkAdjoint :
    RealifiedNaimarkComplexification →L[ℝ]
      RealifiedCameraComplexification :=
  realifiedContinuousLinearBlock naimarkAdjoint 0

@[simp] theorem realifiedNaimarkAdjoint_fst
    (f : RealifiedNaimarkComplexification) :
    (realifiedNaimarkAdjoint f).fst = naimarkAdjoint f.fst := by
  simp [realifiedNaimarkAdjoint]

@[simp] theorem realifiedNaimarkAdjoint_snd
    (f : RealifiedNaimarkComplexification) :
    (realifiedNaimarkAdjoint f).snd = naimarkAdjoint f.snd := by
  simp [realifiedNaimarkAdjoint]

/-- Ambient real block of `(lambda - Y)^(-1)` on the Naimark space. -/
def logarithmicResolventBlock (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedContinuousLinearBlock
    (logarithmicResolventRealOperator lambda hlambda)
    (logarithmicResolventImaginaryOperator lambda hlambda)

@[simp] theorem logarithmicResolventBlock_fst
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (f : RealifiedNaimarkComplexification) :
    (logarithmicResolventBlock lambda hlambda f).fst =
      logarithmicResolventRealOperator lambda hlambda f.fst -
        logarithmicResolventImaginaryOperator lambda hlambda f.snd := by
  exact realifiedContinuousLinearBlock_fst _ _ f

@[simp] theorem logarithmicResolventBlock_snd
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (f : RealifiedNaimarkComplexification) :
    (logarithmicResolventBlock lambda hlambda f).snd =
      logarithmicResolventImaginaryOperator lambda hlambda f.fst +
        logarithmicResolventRealOperator lambda hlambda f.snd := by
  exact realifiedContinuousLinearBlock_snd _ _ f

/-- The existing all-bases Cauchy block is exactly the compression
`V^* (lambda-Y)^(-1) V` of the realified ambient resolvent. -/
theorem allBasesCauchyBlock_eq_realified_compression
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    allBasesCauchyBlock lambda hlambda =
      realifiedNaimarkAdjoint ∘L
        logarithmicResolventBlock lambda hlambda ∘L
          realifiedNaimarkPort := by
  apply ContinuousLinearMap.ext
  intro u
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [allBasesCauchyBlock_fst, allBasesCauchyRealPart,
      allBasesCauchyImaginaryPart, ContinuousLinearMap.comp_apply]
  · simp [allBasesCauchyBlock_snd, allBasesCauchyRealPart,
      allBasesCauchyImaginaryPart, ContinuousLinearMap.comp_apply]

/-! ## Resolvent range and the maximal logarithmic domain -/

/-- The real resolvent component maps the whole Naimark space into the
maximal domain of logarithmic multiplication. -/
theorem logarithmicResolventRealOperator_mem_domain
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (f : NaimarkSpace) :
    logarithmicResolventRealOperator lambda hlambda f ∈
      logarithmicMultiplication.domain := by
  rw [logarithmicMultiplication_domain,
    mem_logarithmicMultiplicationDomain_iff]
  let realPart := logarithmicResolventRealOperator lambda hlambda f
  let imaginaryPart := logarithmicResolventImaginaryOperator lambda hlambda f
  have hraw : MemLp
      (fun x => lambda.re • realPart x -
        lambda.im • imaginaryPart x - f x)
      2 positiveLebesgueMeasure :=
    (((Lp.memLp realPart).const_smul lambda.re).sub
      ((Lp.memLp imaginaryPart).const_smul lambda.im)).sub (Lp.memLp f)
  apply hraw.ae_eq
  filter_upwards
      [logarithmicResolventRealOperator_coeFn lambda hlambda f,
       logarithmicResolventImaginaryOperator_coeFn lambda hlambda f]
      with x hreal himag
  change lambda.re • realPart x - lambda.im • imaginaryPart x - f x =
    logarithmicCoordinate x • realPart x
  rw [hreal, himag]
  have hscalar :
      logarithmicCoordinate x *
          logarithmicResolventRealCoefficient lambda x =
        lambda.re * logarithmicResolventRealCoefficient lambda x -
          lambda.im * logarithmicResolventImaginaryCoefficient lambda x - 1 := by
    linarith [logarithmicResolventCoefficient_real_identity hlambda x]
  simp only [smul_smul]
  rw [hscalar]
  module

/-- The imaginary resolvent component also maps the whole Naimark space into
the maximal logarithmic domain. -/
theorem logarithmicResolventImaginaryOperator_mem_domain
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (f : NaimarkSpace) :
    logarithmicResolventImaginaryOperator lambda hlambda f ∈
      logarithmicMultiplication.domain := by
  rw [logarithmicMultiplication_domain,
    mem_logarithmicMultiplicationDomain_iff]
  let realPart := logarithmicResolventRealOperator lambda hlambda f
  let imaginaryPart := logarithmicResolventImaginaryOperator lambda hlambda f
  have hraw : MemLp
      (fun x => lambda.im • realPart x + lambda.re • imaginaryPart x)
      2 positiveLebesgueMeasure :=
    ((Lp.memLp realPart).const_smul lambda.im).add
      ((Lp.memLp imaginaryPart).const_smul lambda.re)
  apply hraw.ae_eq
  filter_upwards
      [logarithmicResolventRealOperator_coeFn lambda hlambda f,
       logarithmicResolventImaginaryOperator_coeFn lambda hlambda f]
      with x hreal himag
  change lambda.im • realPart x + lambda.re • imaginaryPart x =
    logarithmicCoordinate x • imaginaryPart x
  rw [hreal, himag]
  have hscalar :
      logarithmicCoordinate x *
          logarithmicResolventImaginaryCoefficient lambda x =
        lambda.im * logarithmicResolventRealCoefficient lambda x +
          lambda.re * logarithmicResolventImaginaryCoefficient lambda x := by
    linarith [logarithmicResolventCoefficient_imaginary_identity lambda x]
  simp only [smul_smul]
  rw [hscalar]
  module

/-- Applying logarithmic multiplication to the real resolvent component gives
the real part of the resolvent equation. -/
theorem logarithmicMultiplication_apply_resolventReal
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (f : NaimarkSpace) :
    logarithmicMultiplication
        (⟨logarithmicResolventRealOperator lambda hlambda f,
          logarithmicResolventRealOperator_mem_domain lambda hlambda f⟩ :
          logarithmicMultiplication.domain) =
      lambda.re • logarithmicResolventRealOperator lambda hlambda f -
        lambda.im • logarithmicResolventImaginaryOperator lambda hlambda f - f := by
  let realValue := logarithmicResolventRealOperator lambda hlambda f
  let imaginaryValue := logarithmicResolventImaginaryOperator lambda hlambda f
  let domainValue : logarithmicMultiplication.domain :=
    ⟨realValue, logarithmicResolventRealOperator_mem_domain lambda hlambda f⟩
  change logarithmicMultiplication domainValue =
    lambda.re • realValue - lambda.im • imaginaryValue - f
  apply Lp.ext
  filter_upwards
      [logarithmicMultiplication_coeFn domainValue,
       logarithmicResolventRealOperator_coeFn lambda hlambda f,
       logarithmicResolventImaginaryOperator_coeFn lambda hlambda f,
       Lp.coeFn_smul lambda.re realValue,
       Lp.coeFn_smul lambda.im imaginaryValue,
       Lp.coeFn_sub (lambda.re • realValue) (lambda.im • imaginaryValue),
       Lp.coeFn_sub
        (lambda.re • realValue - lambda.im • imaginaryValue) f]
      with x hdomain hreal himag hsmulReal hsmulImag hsub hsubf
  rw [hdomain, hsubf]
  simp only [Pi.sub_apply]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsmulReal, hsmulImag]
  simp only [Pi.smul_apply]
  change logarithmicCoordinate x • realValue x =
    lambda.re • realValue x - lambda.im • imaginaryValue x - f x
  rw [hreal, himag]
  have hscalar :
      logarithmicCoordinate x *
          logarithmicResolventRealCoefficient lambda x =
        lambda.re * logarithmicResolventRealCoefficient lambda x -
          lambda.im * logarithmicResolventImaginaryCoefficient lambda x - 1 := by
    linarith [logarithmicResolventCoefficient_real_identity hlambda x]
  simp only [smul_smul]
  rw [hscalar]
  module

/-- Applying logarithmic multiplication to the imaginary resolvent component
gives the imaginary part of the resolvent equation. -/
theorem logarithmicMultiplication_apply_resolventImaginary
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (f : NaimarkSpace) :
    logarithmicMultiplication
        (⟨logarithmicResolventImaginaryOperator lambda hlambda f,
          logarithmicResolventImaginaryOperator_mem_domain lambda hlambda f⟩ :
          logarithmicMultiplication.domain) =
      lambda.im • logarithmicResolventRealOperator lambda hlambda f +
        lambda.re • logarithmicResolventImaginaryOperator lambda hlambda f := by
  let realValue := logarithmicResolventRealOperator lambda hlambda f
  let imaginaryValue := logarithmicResolventImaginaryOperator lambda hlambda f
  let domainValue : logarithmicMultiplication.domain :=
    ⟨imaginaryValue,
      logarithmicResolventImaginaryOperator_mem_domain lambda hlambda f⟩
  change logarithmicMultiplication domainValue =
    lambda.im • realValue + lambda.re • imaginaryValue
  apply Lp.ext
  filter_upwards
      [logarithmicMultiplication_coeFn domainValue,
       logarithmicResolventRealOperator_coeFn lambda hlambda f,
       logarithmicResolventImaginaryOperator_coeFn lambda hlambda f,
       Lp.coeFn_smul lambda.im realValue,
       Lp.coeFn_smul lambda.re imaginaryValue,
       Lp.coeFn_add (lambda.im • realValue) (lambda.re • imaginaryValue)]
      with x hdomain hreal himag hsmulReal hsmulImag hadd
  rw [hdomain, hadd]
  simp only [Pi.add_apply]
  rw [hsmulReal, hsmulImag]
  simp only [Pi.smul_apply]
  change logarithmicCoordinate x • imaginaryValue x =
    lambda.im • realValue x + lambda.re • imaginaryValue x
  rw [hreal, himag]
  have hscalar :
      logarithmicCoordinate x *
          logarithmicResolventImaginaryCoefficient lambda x =
        lambda.im * logarithmicResolventRealCoefficient lambda x +
          lambda.re * logarithmicResolventImaginaryCoefficient lambda x := by
    linarith [logarithmicResolventCoefficient_imaginary_identity lambda x]
  simp only [smul_smul]
  rw [hscalar]
  module

/-! ## The realified resolvent equation -/

/-- Real block representing multiplication by the complex scalar `lambda` on
the ambient Naimark complexification. -/
def realifiedNaimarkScalar (lambda : ℂ) :
    RealifiedNaimarkComplexification →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedContinuousLinearBlock
    (lambda.re • ContinuousLinearMap.id ℝ NaimarkSpace)
    (lambda.im • ContinuousLinearMap.id ℝ NaimarkSpace)

@[simp] theorem realifiedNaimarkScalar_fst (lambda : ℂ)
    (f : RealifiedNaimarkComplexification) :
    (realifiedNaimarkScalar lambda f).fst =
      lambda.re • f.fst - lambda.im • f.snd := by
  simp [realifiedNaimarkScalar]

@[simp] theorem realifiedNaimarkScalar_snd (lambda : ℂ)
    (f : RealifiedNaimarkComplexification) :
    (realifiedNaimarkScalar lambda f).snd =
      lambda.im • f.fst + lambda.re • f.snd := by
  simp [realifiedNaimarkScalar]

/-- Coordinatewise maximal domain of realified logarithmic multiplication. -/
abbrev RealifiedLogarithmicDomain :=
  logarithmicMultiplication.domain × logarithmicMultiplication.domain

/-- Coordinatewise logarithmic multiplication on its realified maximal
domain. -/
def realifiedLogarithmicMultiplication :
    RealifiedLogarithmicDomain →ₗ[ℝ]
      RealifiedNaimarkComplexification where
  toFun f := WithLp.toLp 2
    (logarithmicMultiplication f.1, logarithmicMultiplication f.2)
  map_add' f g := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change logarithmicMultiplication (f.1 + g.1) =
        logarithmicMultiplication f.1 + logarithmicMultiplication g.1
      exact LinearPMap.map_add logarithmicMultiplication f.1 g.1
    · change logarithmicMultiplication (f.2 + g.2) =
        logarithmicMultiplication f.2 + logarithmicMultiplication g.2
      exact LinearPMap.map_add logarithmicMultiplication f.2 g.2
  map_smul' c f := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change logarithmicMultiplication (c • f.1) =
        c • logarithmicMultiplication f.1
      exact LinearPMap.map_smul logarithmicMultiplication c f.1
    · change logarithmicMultiplication (c • f.2) =
        c • logarithmicMultiplication f.2
      exact LinearPMap.map_smul logarithmicMultiplication c f.2

@[simp] theorem realifiedLogarithmicMultiplication_fst
    (f : RealifiedLogarithmicDomain) :
    (realifiedLogarithmicMultiplication f).fst =
      logarithmicMultiplication f.1 :=
  rfl

@[simp] theorem realifiedLogarithmicMultiplication_snd
    (f : RealifiedLogarithmicDomain) :
    (realifiedLogarithmicMultiplication f).snd =
      logarithmicMultiplication f.2 :=
  rfl

/-- Inclusion of the coordinatewise maximal domain into the realified ambient
Naimark space. -/
def realifiedLogarithmicDomainEmbedding :
    RealifiedLogarithmicDomain →ₗ[ℝ]
      RealifiedNaimarkComplexification where
  toFun f := WithLp.toLp 2 ((f.1 : NaimarkSpace), (f.2 : NaimarkSpace))
  map_add' f g := by
    apply WithLp.ofLp_injective 2
    rfl
  map_smul' c f := by
    apply WithLp.ofLp_injective 2
    rfl

@[simp] theorem realifiedLogarithmicDomainEmbedding_fst
    (f : RealifiedLogarithmicDomain) :
    (realifiedLogarithmicDomainEmbedding f).fst = (f.1 : NaimarkSpace) :=
  rfl

@[simp] theorem realifiedLogarithmicDomainEmbedding_snd
    (f : RealifiedLogarithmicDomain) :
    (realifiedLogarithmicDomainEmbedding f).snd = (f.2 : NaimarkSpace) :=
  rfl

/-- The closed realified operator `lambda-Y` on the coordinatewise maximal
domain. -/
def realifiedLambdaMinusLogarithmicMultiplication (lambda : ℂ) :
    RealifiedLogarithmicDomain →ₗ[ℝ]
      RealifiedNaimarkComplexification :=
  (realifiedNaimarkScalar lambda).toLinearMap.comp
      realifiedLogarithmicDomainEmbedding -
    realifiedLogarithmicMultiplication

@[simp] theorem realifiedLambdaMinusLogarithmicMultiplication_fst
    (lambda : ℂ) (f : RealifiedLogarithmicDomain) :
    (realifiedLambdaMinusLogarithmicMultiplication lambda f).fst =
      lambda.re • (f.1 : NaimarkSpace) -
        lambda.im • (f.2 : NaimarkSpace) -
          logarithmicMultiplication f.1 := by
  change
    (realifiedNaimarkScalar lambda
        (realifiedLogarithmicDomainEmbedding f)).fst -
      (realifiedLogarithmicMultiplication f).fst = _
  rw [realifiedNaimarkScalar_fst,
    realifiedLogarithmicDomainEmbedding_fst,
    realifiedLogarithmicDomainEmbedding_snd,
    realifiedLogarithmicMultiplication_fst]

@[simp] theorem realifiedLambdaMinusLogarithmicMultiplication_snd
    (lambda : ℂ) (f : RealifiedLogarithmicDomain) :
    (realifiedLambdaMinusLogarithmicMultiplication lambda f).snd =
      lambda.im • (f.1 : NaimarkSpace) +
        lambda.re • (f.2 : NaimarkSpace) -
          logarithmicMultiplication f.2 := by
  change
    (realifiedNaimarkScalar lambda
        (realifiedLogarithmicDomainEmbedding f)).snd -
      (realifiedLogarithmicMultiplication f).snd = _
  rw [realifiedNaimarkScalar_snd,
    realifiedLogarithmicDomainEmbedding_fst,
    realifiedLogarithmicDomainEmbedding_snd,
    realifiedLogarithmicMultiplication_snd]

/-- Off the real axis, the realified operator `lambda-Y` is injective on the
maximal logarithmic domain. -/
theorem realifiedLambdaMinusLogarithmicMultiplication_injective
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Function.Injective
      (realifiedLambdaMinusLogarithmicMultiplication lambda) := by
  intro f g hfg
  have hzero :
      realifiedLambdaMinusLogarithmicMultiplication lambda (f - g) = 0 := by
    simp only [map_sub, hfg, sub_self]
  have hfirst := congrArg WithLp.fst hzero
  have hsecond := congrArg WithLp.snd hzero
  simp only [realifiedLambdaMinusLogarithmicMultiplication_fst,
    realifiedLambdaMinusLogarithmicMultiplication_snd,
    WithLp.zero_fst, WithLp.zero_snd] at hfirst hsecond
  let x : logarithmicMultiplication.domain := (f - g).1
  let y : logarithmicMultiplication.domain := (f - g).2
  change lambda.re • (x : NaimarkSpace) -
      lambda.im • (y : NaimarkSpace) -
        logarithmicMultiplication x = 0 at hfirst
  change lambda.im • (x : NaimarkSpace) +
      lambda.re • (y : NaimarkSpace) -
        logarithmicMultiplication y = 0 at hsecond
  have hxy :
      inner ℝ (logarithmicMultiplication x) (y : NaimarkSpace) =
        inner ℝ (x : NaimarkSpace) (logarithmicMultiplication y) :=
    logarithmicMultiplication_isFormalAdjoint x y
  have hinnerFirst := congrArg
    (fun z : NaimarkSpace => inner ℝ z (y : NaimarkSpace)) hfirst
  have hinnerSecond := congrArg
    (fun z : NaimarkSpace => inner ℝ (x : NaimarkSpace) z) hsecond
  have hnormEquation :
      lambda.im *
        (‖(x : NaimarkSpace)‖ ^ 2 + ‖(y : NaimarkSpace)‖ ^ 2) = 0 := by
    simp only [inner_sub_left, inner_add_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, inner_zero_left, inner_zero_right]
      at hinnerFirst hinnerSecond
    rw [hxy] at hinnerFirst
    linarith
  have hsum :
      ‖(x : NaimarkSpace)‖ ^ 2 + ‖(y : NaimarkSpace)‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hnormEquation).resolve_left hlambda
  have hxnorm : ‖(x : NaimarkSpace)‖ = 0 := by
    nlinarith [sq_nonneg ‖(x : NaimarkSpace)‖,
      sq_nonneg ‖(y : NaimarkSpace)‖]
  have hynorm : ‖(y : NaimarkSpace)‖ = 0 := by
    nlinarith [sq_nonneg ‖(x : NaimarkSpace)‖,
      sq_nonneg ‖(y : NaimarkSpace)‖]
  have hx : x = 0 := by
    apply Subtype.ext
    exact norm_eq_zero.mp hxnorm
  have hy : y = 0 := by
    apply Subtype.ext
    exact norm_eq_zero.mp hynorm
  have hdiff : f - g = 0 := by
    apply Prod.ext
    · simpa [x] using hx
    · simpa [y] using hy
  exact sub_eq_zero.mp hdiff

/-- The ambient realified resolvent takes values in the coordinatewise
maximal logarithmic domain. -/
def logarithmicResolventDomainElement
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (h : RealifiedNaimarkComplexification) :
    RealifiedLogarithmicDomain :=
  (⟨(logarithmicResolventBlock lambda hlambda h).fst, by
      rw [logarithmicResolventBlock_fst]
      exact Submodule.sub_mem logarithmicMultiplication.domain
        (logarithmicResolventRealOperator_mem_domain lambda hlambda h.fst)
        (logarithmicResolventImaginaryOperator_mem_domain lambda hlambda h.snd)⟩,
   ⟨(logarithmicResolventBlock lambda hlambda h).snd, by
      rw [logarithmicResolventBlock_snd]
      exact Submodule.add_mem logarithmicMultiplication.domain
        (logarithmicResolventImaginaryOperator_mem_domain lambda hlambda h.fst)
        (logarithmicResolventRealOperator_mem_domain lambda hlambda h.snd)⟩)

@[simp] theorem logarithmicResolventDomainElement_fst_coe
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (h : RealifiedNaimarkComplexification) :
    ((logarithmicResolventDomainElement lambda hlambda h).1 : NaimarkSpace) =
      (logarithmicResolventBlock lambda hlambda h).fst :=
  rfl

@[simp] theorem logarithmicResolventDomainElement_snd_coe
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (h : RealifiedNaimarkComplexification) :
    ((logarithmicResolventDomainElement lambda hlambda h).2 : NaimarkSpace) =
      (logarithmicResolventBlock lambda hlambda h).snd :=
  rfl

/-- The ambient resolvent with its codomain restricted to the coordinatewise
maximal logarithmic domain. -/
def logarithmicResolventIntoDomain
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedNaimarkComplexification →ₗ[ℝ]
      RealifiedLogarithmicDomain where
  toFun := logarithmicResolventDomainElement lambda hlambda
  map_add' f g := by
    apply Prod.ext
    · apply Subtype.ext
      change (logarithmicResolventBlock lambda hlambda (f + g)).fst =
        (logarithmicResolventBlock lambda hlambda f).fst +
          (logarithmicResolventBlock lambda hlambda g).fst
      simp
    · apply Subtype.ext
      change (logarithmicResolventBlock lambda hlambda (f + g)).snd =
        (logarithmicResolventBlock lambda hlambda f).snd +
          (logarithmicResolventBlock lambda hlambda g).snd
      simp
  map_smul' c f := by
    apply Prod.ext
    · apply Subtype.ext
      change (logarithmicResolventBlock lambda hlambda (c • f)).fst =
        c • (logarithmicResolventBlock lambda hlambda f).fst
      simp
    · apply Subtype.ext
      change (logarithmicResolventBlock lambda hlambda (c • f)).snd =
        c • (logarithmicResolventBlock lambda hlambda f).snd
      simp

@[simp] theorem logarithmicResolventIntoDomain_apply
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (h : RealifiedNaimarkComplexification) :
    logarithmicResolventIntoDomain lambda hlambda h =
      logarithmicResolventDomainElement lambda hlambda h :=
  rfl

/-- Forgetting the domain witness recovers the original bounded ambient
resolvent value. -/
@[simp] theorem realifiedLogarithmicDomainEmbedding_resolventDomainElement
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (h : RealifiedNaimarkComplexification) :
    realifiedLogarithmicDomainEmbedding
        (logarithmicResolventDomainElement lambda hlambda h) =
      logarithmicResolventBlock lambda hlambda h := by
  apply WithLp.ofLp_injective 2
  rfl

/-- Exact domain-sensitive realified resolvent identity
`lambda R(lambda)h = Y R(lambda)h + h`. -/
theorem realified_logarithmic_resolvent_equation
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (h : RealifiedNaimarkComplexification) :
    realifiedNaimarkScalar lambda
        (logarithmicResolventBlock lambda hlambda h) =
      realifiedLogarithmicMultiplication
          (logarithmicResolventDomainElement lambda hlambda h) + h := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp only [WithLp.ofLp_fst, WithLp.add_fst]
    rw [realifiedNaimarkScalar_fst,
      realifiedLogarithmicMultiplication_fst]
    change lambda.re • (logarithmicResolventBlock lambda hlambda h).fst -
        lambda.im • (logarithmicResolventBlock lambda hlambda h).snd =
      logarithmicMultiplication
          (logarithmicResolventDomainElement lambda hlambda h).1 + h.fst
    rw [logarithmicResolventBlock_fst,
      logarithmicResolventBlock_snd]
    let realDomain : logarithmicMultiplication.domain :=
      ⟨logarithmicResolventRealOperator lambda hlambda h.fst,
        logarithmicResolventRealOperator_mem_domain lambda hlambda h.fst⟩
    let imaginaryDomain : logarithmicMultiplication.domain :=
      ⟨logarithmicResolventImaginaryOperator lambda hlambda h.snd,
        logarithmicResolventImaginaryOperator_mem_domain lambda hlambda h.snd⟩
    have hdomain :
        (logarithmicResolventDomainElement lambda hlambda h).1 =
          realDomain - imaginaryDomain := by
      apply Subtype.ext
      rw [logarithmicResolventDomainElement_fst_coe,
        logarithmicResolventBlock_fst]
      rfl
    have hmap :
        logarithmicMultiplication
            (logarithmicResolventDomainElement lambda hlambda h).1 =
          logarithmicMultiplication realDomain -
            logarithmicMultiplication imaginaryDomain := by
      rw [hdomain]
      exact LinearPMap.map_sub logarithmicMultiplication _ _
    rw [hmap]
    change lambda.re •
          (logarithmicResolventRealOperator lambda hlambda h.fst -
            logarithmicResolventImaginaryOperator lambda hlambda h.snd) -
        lambda.im •
          (logarithmicResolventImaginaryOperator lambda hlambda h.fst +
            logarithmicResolventRealOperator lambda hlambda h.snd) =
      logarithmicMultiplication realDomain -
        logarithmicMultiplication imaginaryDomain + h.fst
    rw [show logarithmicMultiplication realDomain =
          lambda.re • logarithmicResolventRealOperator lambda hlambda h.fst -
            lambda.im • logarithmicResolventImaginaryOperator lambda hlambda h.fst -
              h.fst from
      logarithmicMultiplication_apply_resolventReal lambda hlambda h.fst,
      show logarithmicMultiplication imaginaryDomain =
          lambda.im • logarithmicResolventRealOperator lambda hlambda h.snd +
            lambda.re • logarithmicResolventImaginaryOperator lambda hlambda h.snd from
        logarithmicMultiplication_apply_resolventImaginary lambda hlambda h.snd]
    module
  · simp only [WithLp.ofLp_snd, WithLp.add_snd]
    rw [realifiedNaimarkScalar_snd,
      realifiedLogarithmicMultiplication_snd]
    change lambda.im • (logarithmicResolventBlock lambda hlambda h).fst +
        lambda.re • (logarithmicResolventBlock lambda hlambda h).snd =
      logarithmicMultiplication
          (logarithmicResolventDomainElement lambda hlambda h).2 + h.snd
    rw [logarithmicResolventBlock_fst,
      logarithmicResolventBlock_snd]
    let imaginaryDomain : logarithmicMultiplication.domain :=
      ⟨logarithmicResolventImaginaryOperator lambda hlambda h.fst,
        logarithmicResolventImaginaryOperator_mem_domain lambda hlambda h.fst⟩
    let realDomain : logarithmicMultiplication.domain :=
      ⟨logarithmicResolventRealOperator lambda hlambda h.snd,
        logarithmicResolventRealOperator_mem_domain lambda hlambda h.snd⟩
    have hdomain :
        (logarithmicResolventDomainElement lambda hlambda h).2 =
          imaginaryDomain + realDomain := by
      apply Subtype.ext
      rw [logarithmicResolventDomainElement_snd_coe,
        logarithmicResolventBlock_snd]
      rfl
    have hmap :
        logarithmicMultiplication
            (logarithmicResolventDomainElement lambda hlambda h).2 =
          logarithmicMultiplication imaginaryDomain +
            logarithmicMultiplication realDomain := by
      rw [hdomain]
      exact LinearPMap.map_add logarithmicMultiplication _ _
    rw [hmap]
    change lambda.im •
          (logarithmicResolventRealOperator lambda hlambda h.fst -
            logarithmicResolventImaginaryOperator lambda hlambda h.snd) +
        lambda.re •
          (logarithmicResolventImaginaryOperator lambda hlambda h.fst +
            logarithmicResolventRealOperator lambda hlambda h.snd) =
      logarithmicMultiplication imaginaryDomain +
        logarithmicMultiplication realDomain + h.snd
    rw [show logarithmicMultiplication imaginaryDomain =
          lambda.im • logarithmicResolventRealOperator lambda hlambda h.fst +
            lambda.re • logarithmicResolventImaginaryOperator lambda hlambda h.fst from
      logarithmicMultiplication_apply_resolventImaginary lambda hlambda h.fst,
      show logarithmicMultiplication realDomain =
          lambda.re • logarithmicResolventRealOperator lambda hlambda h.snd -
            lambda.im • logarithmicResolventImaginaryOperator lambda hlambda h.snd -
              h.snd from
        logarithmicMultiplication_apply_resolventReal lambda hlambda h.snd]
    module

/-- The domain-valued resolvent is a right inverse of `lambda-Y`. -/
@[simp] theorem realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (h : RealifiedNaimarkComplexification) :
    realifiedLambdaMinusLogarithmicMultiplication lambda
        (logarithmicResolventIntoDomain lambda hlambda h) = h := by
  change realifiedNaimarkScalar lambda
        (realifiedLogarithmicDomainEmbedding
          (logarithmicResolventDomainElement lambda hlambda h)) -
      realifiedLogarithmicMultiplication
          (logarithmicResolventDomainElement lambda hlambda h) = h
  rw [realifiedLogarithmicDomainEmbedding_resolventDomainElement,
    realified_logarithmic_resolvent_equation]
  module

/-- Injectivity of `lambda-Y` upgrades the resolvent identity to a left
inverse on the full maximal domain. -/
@[simp] theorem logarithmicResolvent_apply_realifiedLambdaMinus
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (f : RealifiedLogarithmicDomain) :
    logarithmicResolventIntoDomain lambda hlambda
        (realifiedLambdaMinusLogarithmicMultiplication lambda f) = f := by
  apply realifiedLambdaMinusLogarithmicMultiplication_injective lambda hlambda
  rw [realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent]

/-- Off the real axis, `lambda-Y` is a linear bijection from its maximal
domain onto the realified ambient space. -/
theorem realifiedLambdaMinusLogarithmicMultiplication_bijective
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Function.Bijective
      (realifiedLambdaMinusLogarithmicMultiplication lambda) := by
  constructor
  · exact realifiedLambdaMinusLogarithmicMultiplication_injective lambda hlambda
  · intro h
    exact ⟨logarithmicResolventIntoDomain lambda hlambda h,
      realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent
        lambda hlambda h⟩

/-- The domain-valued resolvent is injective. -/
theorem logarithmicResolventIntoDomain_injective
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Function.Injective (logarithmicResolventIntoDomain lambda hlambda) := by
  intro h k hhk
  calc
    h = realifiedLambdaMinusLogarithmicMultiplication lambda
          (logarithmicResolventIntoDomain lambda hlambda h) :=
      (realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent
        lambda hlambda h).symm
    _ = realifiedLambdaMinusLogarithmicMultiplication lambda
          (logarithmicResolventIntoDomain lambda hlambda k) := by rw [hhk]
    _ = k := realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent
      lambda hlambda k

/-- The bounded ambient resolvent block is injective off the real axis. -/
theorem logarithmicResolventBlock_injective
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Function.Injective (logarithmicResolventBlock lambda hlambda) := by
  intro h k hhk
  apply logarithmicResolventIntoDomain_injective lambda hlambda
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg WithLp.fst hhk
  · apply Subtype.ext
    exact congrArg WithLp.snd hhk

end NativeCarrySpectralWeyl.Infinite
