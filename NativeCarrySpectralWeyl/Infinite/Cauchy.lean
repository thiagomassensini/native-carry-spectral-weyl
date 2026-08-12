import NativeCarrySpectralWeyl.Infinite.LogarithmicMultiplication
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The all-bases compressed Cauchy family

The all-bases camera Hilbert space and its explicit Naimark dilation are real.
Accordingly, this file constructs the canonical realification of the complex
resolvent before introducing any separate complexification of that Hilbert
space.  For `lambda = a + i b`, `b != 0`, and

`y(x) = 1 + log x`,

the two real multipliers are

`Re (lambda - y)⁻¹ = (a - y) / ((a - y)² + b²)`

and

`Im (lambda - y)⁻¹ = -b / ((a - y)² + b²)`.

Both are bounded by `|b|⁻¹`.  They therefore define bounded self-adjoint
operators on the Naimark `L²` space.  Compressing them through the all-bases
isometry `V` gives the two components of

`M_infinity(lambda) = V† (lambda - Y)⁻¹ V`.

This realizes the Cauchy family with the exact sign convention of the research
notes.  In particular, its imaginary component is nonpositive in the upper
half-plane and nonnegative in the lower half-plane.  The construction is a
real/imaginary-component representation; it does not claim that the real
camera Hilbert space has already been complexified.
-/

open scoped ENNReal MeasureTheory RealInnerProductSpace ComplexConjugate
open Set MeasureTheory

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

/-! ## A reusable bounded real multiplier on the Naimark space -/

/-- Data specifying a measurable bounded real scalar multiplier on the
all-bases Naimark space. -/
structure BoundedRealNaimarkMultiplier where
  coefficient : ℝ → ℝ
  bound : ℝ
  measurable_coefficient : Measurable coefficient
  bound_nonneg : 0 ≤ bound
  abs_coefficient_le : ∀ x, |coefficient x| ≤ bound

/-- Pointwise action of a bounded real multiplier on an `L²` representative. -/
def boundedRealNaimarkMultiplierFunction
    (multiplier : BoundedRealNaimarkMultiplier) (f : NaimarkSpace) (x : ℝ) :
    KolmogorovSpace :=
  multiplier.coefficient x • f x

/-- A bounded real multiplier has a strongly measurable pointwise action. -/
theorem boundedRealNaimarkMultiplierFunction_aestronglyMeasurable
    (multiplier : BoundedRealNaimarkMultiplier) (f : NaimarkSpace) :
    AEStronglyMeasurable (boundedRealNaimarkMultiplierFunction multiplier f)
      positiveLebesgueMeasure := by
  exact multiplier.measurable_coefficient.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable f)

/-- The pointwise action of a bounded real multiplier remains in `L²`. -/
theorem boundedRealNaimarkMultiplierFunction_memLp
    (multiplier : BoundedRealNaimarkMultiplier) (f : NaimarkSpace) :
    MemLp (boundedRealNaimarkMultiplierFunction multiplier f) 2
      positiveLebesgueMeasure := by
  apply (Lp.memLp f).of_le_mul
    (boundedRealNaimarkMultiplierFunction_aestronglyMeasurable multiplier f)
  filter_upwards with x
  rw [boundedRealNaimarkMultiplierFunction, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (multiplier.abs_coefficient_le x)
    (norm_nonneg (f x))

/-- Pointwise bounded multiplication respects addition almost everywhere. -/
theorem boundedRealNaimarkMultiplierFunction_add
    (multiplier : BoundedRealNaimarkMultiplier) (f g : NaimarkSpace) :
    boundedRealNaimarkMultiplierFunction multiplier (f + g) =ᵐ[
      positiveLebesgueMeasure]
      boundedRealNaimarkMultiplierFunction multiplier f +
        boundedRealNaimarkMultiplierFunction multiplier g := by
  filter_upwards [Lp.coeFn_add f g] with x hx
  simp only [Pi.add_apply, boundedRealNaimarkMultiplierFunction]
  rw [hx]
  exact smul_add _ _ _

/-- Pointwise bounded multiplication respects real scalar multiplication
almost everywhere. -/
theorem boundedRealNaimarkMultiplierFunction_smul
    (multiplier : BoundedRealNaimarkMultiplier) (c : ℝ)
    (f : NaimarkSpace) :
    boundedRealNaimarkMultiplierFunction multiplier (c • f) =ᵐ[
      positiveLebesgueMeasure]
      c • boundedRealNaimarkMultiplierFunction multiplier f := by
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp only [Pi.smul_apply, boundedRealNaimarkMultiplierFunction]
  rw [hx]
  simp [smul_smul, mul_comm]

/-- A bounded measurable real scalar multiplier as a linear endomorphism of
the Naimark space. -/
def boundedRealNaimarkMultiplierLinearMap
    (multiplier : BoundedRealNaimarkMultiplier) :
    NaimarkSpace →ₗ[ℝ] NaimarkSpace where
  toFun f := (boundedRealNaimarkMultiplierFunction_memLp multiplier f).toLp
    (boundedRealNaimarkMultiplierFunction multiplier f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr
      (boundedRealNaimarkMultiplierFunction_memLp multiplier (f + g))
      ((boundedRealNaimarkMultiplierFunction_memLp multiplier f).add
        (boundedRealNaimarkMultiplierFunction_memLp multiplier g))
      (boundedRealNaimarkMultiplierFunction_add multiplier f g)
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr
      (boundedRealNaimarkMultiplierFunction_memLp multiplier (c • f))
      ((boundedRealNaimarkMultiplierFunction_memLp multiplier f).const_smul c)
      (boundedRealNaimarkMultiplierFunction_smul multiplier c f)

/-- Almost-everywhere action of the bounded multiplier linear map. -/
theorem boundedRealNaimarkMultiplierLinearMap_coeFn
    (multiplier : BoundedRealNaimarkMultiplier) (f : NaimarkSpace) :
    ⇑(boundedRealNaimarkMultiplierLinearMap multiplier f) =ᵐ[
      positiveLebesgueMeasure]
      boundedRealNaimarkMultiplierFunction multiplier f :=
  (boundedRealNaimarkMultiplierFunction_memLp multiplier f).coeFn_toLp

/-- The `L²` norm of a bounded multiplier is controlled by its scalar bound. -/
theorem boundedRealNaimarkMultiplierLinearMap_norm_le
    (multiplier : BoundedRealNaimarkMultiplier) (f : NaimarkSpace) :
    ‖boundedRealNaimarkMultiplierLinearMap multiplier f‖ ≤
      multiplier.bound * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedRealNaimarkMultiplierLinearMap_coeFn multiplier f]
    with x hx
  rw [hx, boundedRealNaimarkMultiplierFunction, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (multiplier.abs_coefficient_le x)
    (norm_nonneg (f x))

/-- A bounded measurable real scalar multiplier as a continuous linear
endomorphism of the Naimark space. -/
def boundedRealNaimarkMultiplier
    (multiplier : BoundedRealNaimarkMultiplier) :
    NaimarkSpace →L[ℝ] NaimarkSpace :=
  (boundedRealNaimarkMultiplierLinearMap multiplier).mkContinuous
    multiplier.bound
    (boundedRealNaimarkMultiplierLinearMap_norm_le multiplier)

/-- Almost-everywhere action of the bundled continuous multiplier. -/
theorem boundedRealNaimarkMultiplier_coeFn
    (multiplier : BoundedRealNaimarkMultiplier) (f : NaimarkSpace) :
    ⇑(boundedRealNaimarkMultiplier multiplier f) =ᵐ[
      positiveLebesgueMeasure]
      boundedRealNaimarkMultiplierFunction multiplier f := by
  simpa only [boundedRealNaimarkMultiplier, LinearMap.mkContinuous_apply] using
    boundedRealNaimarkMultiplierLinearMap_coeFn multiplier f

/-- The operator norm of the bundled multiplier is at most its scalar bound. -/
theorem boundedRealNaimarkMultiplier_norm_le
    (multiplier : BoundedRealNaimarkMultiplier) :
    ‖boundedRealNaimarkMultiplier multiplier‖ ≤ multiplier.bound := by
  exact LinearMap.mkContinuous_norm_le _ multiplier.bound_nonneg
    (boundedRealNaimarkMultiplierLinearMap_norm_le multiplier)

/-- Every bounded real scalar multiplier is symmetric on the real Naimark
Hilbert space. -/
theorem boundedRealNaimarkMultiplier_isSymmetric
    (multiplier : BoundedRealNaimarkMultiplier) :
    (boundedRealNaimarkMultiplier multiplier :
      NaimarkSpace →ₗ[ℝ] NaimarkSpace).IsSymmetric := by
  intro f g
  change inner ℝ (boundedRealNaimarkMultiplier multiplier f) g =
    inner ℝ f (boundedRealNaimarkMultiplier multiplier g)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedRealNaimarkMultiplier_coeFn multiplier f,
    boundedRealNaimarkMultiplier_coeFn multiplier g] with x hfx hgx
  rw [hfx, hgx]
  simp [boundedRealNaimarkMultiplierFunction, real_inner_smul_left,
    real_inner_smul_right]

/-- Every bounded real scalar multiplier is self-adjoint. -/
theorem boundedRealNaimarkMultiplier_isSelfAdjoint
    (multiplier : BoundedRealNaimarkMultiplier) :
    IsSelfAdjoint (boundedRealNaimarkMultiplier multiplier) :=
  (boundedRealNaimarkMultiplier_isSymmetric multiplier).isSelfAdjoint

/-! ## Scalar logarithmic resolvent -/

/-- Positive denominator of the logarithmic resolvent away from the real
axis. -/
def logarithmicResolventDenominator (lambda : ℂ) (x : ℝ) : ℝ :=
  (lambda.re - logarithmicCoordinate x) ^ 2 + lambda.im ^ 2

/-- The logarithmic resolvent denominator is measurable. -/
theorem measurable_logarithmicResolventDenominator (lambda : ℂ) :
    Measurable (logarithmicResolventDenominator lambda) := by
  exact (measurable_const.sub measurable_logarithmicCoordinate).pow_const 2 |>.add
    (measurable_const.pow_const 2)

/-- Off the real axis, the logarithmic resolvent denominator is strictly
positive at every point. -/
theorem logarithmicResolventDenominator_pos {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (x : ℝ) :
    0 < logarithmicResolventDenominator lambda x := by
  rw [logarithmicResolventDenominator]
  nlinarith [sq_nonneg (lambda.re - logarithmicCoordinate x),
    sq_pos_of_ne_zero hlambda]

/-- Off the real axis, the logarithmic resolvent denominator never vanishes. -/
theorem logarithmicResolventDenominator_ne_zero {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (x : ℝ) :
    logarithmicResolventDenominator lambda x ≠ 0 :=
  (logarithmicResolventDenominator_pos hlambda x).ne'

/-- Real part of `(lambda - y(x))⁻¹`. -/
def logarithmicResolventRealCoefficient (lambda : ℂ) (x : ℝ) : ℝ :=
  (lambda.re - logarithmicCoordinate x) /
    logarithmicResolventDenominator lambda x

/-- Imaginary part of `(lambda - y(x))⁻¹`, with the anti-Herglotz sign
convention of the Weyl-camera notes. -/
def logarithmicResolventImaginaryCoefficient (lambda : ℂ) (x : ℝ) : ℝ :=
  -lambda.im / logarithmicResolventDenominator lambda x

/-- The real logarithmic resolvent coefficient is measurable. -/
theorem measurable_logarithmicResolventRealCoefficient (lambda : ℂ) :
    Measurable (logarithmicResolventRealCoefficient lambda) := by
  exact (measurable_const.sub measurable_logarithmicCoordinate).div
    (measurable_logarithmicResolventDenominator lambda)

/-- The imaginary logarithmic resolvent coefficient is measurable. -/
theorem measurable_logarithmicResolventImaginaryCoefficient (lambda : ℂ) :
    Measurable (logarithmicResolventImaginaryCoefficient lambda) := by
  exact measurable_const.div
    (measurable_logarithmicResolventDenominator lambda)

/-- The two real coefficients satisfy the real part of the inverse identity
`(lambda - y) * (lambda - y)⁻¹ = 1`. -/
theorem logarithmicResolventCoefficient_real_identity {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (x : ℝ) :
    (lambda.re - logarithmicCoordinate x) *
        logarithmicResolventRealCoefficient lambda x -
      lambda.im * logarithmicResolventImaginaryCoefficient lambda x = 1 := by
  rw [logarithmicResolventRealCoefficient,
    logarithmicResolventImaginaryCoefficient]
  calc
    (lambda.re - logarithmicCoordinate x) *
          ((lambda.re - logarithmicCoordinate x) /
            logarithmicResolventDenominator lambda x) -
        lambda.im *
          (-lambda.im / logarithmicResolventDenominator lambda x) =
        ((lambda.re - logarithmicCoordinate x) ^ 2 + lambda.im ^ 2) /
          logarithmicResolventDenominator lambda x := by ring
    _ = 1 := by
      rw [logarithmicResolventDenominator]
      exact div_self (logarithmicResolventDenominator_ne_zero hlambda x)

/-- The two real coefficients satisfy the imaginary part of the inverse
identity `(lambda - y) * (lambda - y)⁻¹ = 1`. -/
theorem logarithmicResolventCoefficient_imaginary_identity (lambda : ℂ)
    (x : ℝ) :
    lambda.im * logarithmicResolventRealCoefficient lambda x +
      (lambda.re - logarithmicCoordinate x) *
        logarithmicResolventImaginaryCoefficient lambda x = 0 := by
  rw [logarithmicResolventRealCoefficient,
    logarithmicResolventImaginaryCoefficient]
  ring

/-- The squared complex modulus of the two-component resolvent coefficient is
the reciprocal denominator. -/
theorem logarithmicResolventCoefficient_norm_sq {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (x : ℝ) :
    logarithmicResolventRealCoefficient lambda x ^ 2 +
        logarithmicResolventImaginaryCoefficient lambda x ^ 2 =
      (logarithmicResolventDenominator lambda x)⁻¹ := by
  rw [logarithmicResolventRealCoefficient,
    logarithmicResolventImaginaryCoefficient]
  let d := logarithmicResolventDenominator lambda x
  have hd : d ≠ 0 := logarithmicResolventDenominator_ne_zero hlambda x
  change ((lambda.re - logarithmicCoordinate x) / d) ^ 2 +
      (-lambda.im / d) ^ 2 = d⁻¹
  calc
    ((lambda.re - logarithmicCoordinate x) / d) ^ 2 +
        (-lambda.im / d) ^ 2 =
      ((lambda.re - logarithmicCoordinate x) ^ 2 + lambda.im ^ 2) /
        d ^ 2 := by ring
    _ = d / d ^ 2 := by rw [show
        (lambda.re - logarithmicCoordinate x) ^ 2 + lambda.im ^ 2 = d
      from rfl]
    _ = d⁻¹ := by field_simp

/-- The real resolvent coefficient is bounded by the sharp ambient resolvent
scale `|Im lambda|⁻¹`. -/
theorem abs_logarithmicResolventRealCoefficient_le {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (x : ℝ) :
    |logarithmicResolventRealCoefficient lambda x| ≤ |lambda.im|⁻¹ := by
  let u := lambda.re - logarithmicCoordinate x
  let b := lambda.im
  have hb : 0 < |b| := abs_pos.mpr hlambda
  have hd : 0 < u ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg u, sq_pos_of_ne_zero hlambda]
  rw [logarithmicResolventRealCoefficient,
    logarithmicResolventDenominator]
  change |u / (u ^ 2 + b ^ 2)| ≤ |b|⁻¹
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
  rw [inv_mul_eq_div, le_div_iff₀ hb]
  nlinarith [sq_nonneg (|u| - |b|), sq_abs u, sq_abs b,
    sq_nonneg u, sq_nonneg b]

/-- The imaginary resolvent coefficient is bounded by the sharp ambient
resolvent scale `|Im lambda|⁻¹`. -/
theorem abs_logarithmicResolventImaginaryCoefficient_le {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (x : ℝ) :
    |logarithmicResolventImaginaryCoefficient lambda x| ≤ |lambda.im|⁻¹ := by
  let b := lambda.im
  let u := lambda.re - logarithmicCoordinate x
  have hb : 0 < |b| := abs_pos.mpr hlambda
  have hd : 0 < u ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg u, sq_pos_of_ne_zero hlambda]
  rw [logarithmicResolventImaginaryCoefficient,
    logarithmicResolventDenominator]
  change |-b / (u ^ 2 + b ^ 2)| ≤ |b|⁻¹
  rw [abs_div, abs_neg, abs_of_pos hd, div_le_iff₀ hd]
  rw [inv_mul_eq_div, le_div_iff₀ hb]
  nlinarith [sq_abs b, sq_nonneg u]

/-- Complex conjugation fixes the real resolvent coefficient. -/
theorem logarithmicResolventRealCoefficient_conj (lambda : ℂ) (x : ℝ) :
    logarithmicResolventRealCoefficient (conj lambda) x =
      logarithmicResolventRealCoefficient lambda x := by
  simp [logarithmicResolventRealCoefficient,
    logarithmicResolventDenominator]

/-- Complex conjugation reverses the imaginary resolvent coefficient. -/
theorem logarithmicResolventImaginaryCoefficient_conj (lambda : ℂ) (x : ℝ) :
    logarithmicResolventImaginaryCoefficient (conj lambda) x =
      -logarithmicResolventImaginaryCoefficient lambda x := by
  simp [logarithmicResolventImaginaryCoefficient,
    logarithmicResolventDenominator]
  ring

/-! ## Bounded resolvent multipliers -/

/-- Bounded multiplier data for the real part of the logarithmic resolvent. -/
def logarithmicResolventRealMultiplier (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) : BoundedRealNaimarkMultiplier where
  coefficient := logarithmicResolventRealCoefficient lambda
  bound := |lambda.im|⁻¹
  measurable_coefficient :=
    measurable_logarithmicResolventRealCoefficient lambda
  bound_nonneg := inv_nonneg.mpr (abs_nonneg lambda.im)
  abs_coefficient_le := abs_logarithmicResolventRealCoefficient_le hlambda

/-- Bounded multiplier data for the imaginary part of the logarithmic
resolvent. -/
def logarithmicResolventImaginaryMultiplier (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) : BoundedRealNaimarkMultiplier where
  coefficient := logarithmicResolventImaginaryCoefficient lambda
  bound := |lambda.im|⁻¹
  measurable_coefficient :=
    measurable_logarithmicResolventImaginaryCoefficient lambda
  bound_nonneg := inv_nonneg.mpr (abs_nonneg lambda.im)
  abs_coefficient_le := abs_logarithmicResolventImaginaryCoefficient_le hlambda

/-- Real component of `(lambda - Y)⁻¹` on the Naimark space. -/
def logarithmicResolventRealOperator (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) : NaimarkSpace →L[ℝ] NaimarkSpace :=
  boundedRealNaimarkMultiplier
    (logarithmicResolventRealMultiplier lambda hlambda)

/-- Imaginary component of `(lambda - Y)⁻¹` on the Naimark space. -/
def logarithmicResolventImaginaryOperator (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) : NaimarkSpace →L[ℝ] NaimarkSpace :=
  boundedRealNaimarkMultiplier
    (logarithmicResolventImaginaryMultiplier lambda hlambda)

/-- Almost-everywhere action of the real resolvent component. -/
theorem logarithmicResolventRealOperator_coeFn (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (f : NaimarkSpace) :
    ⇑(logarithmicResolventRealOperator lambda hlambda f) =ᵐ[
      positiveLebesgueMeasure]
      fun x => logarithmicResolventRealCoefficient lambda x • f x := by
  exact boundedRealNaimarkMultiplier_coeFn
    (logarithmicResolventRealMultiplier lambda hlambda) f

/-- Almost-everywhere action of the imaginary resolvent component. -/
theorem logarithmicResolventImaginaryOperator_coeFn (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (f : NaimarkSpace) :
    ⇑(logarithmicResolventImaginaryOperator lambda hlambda f) =ᵐ[
      positiveLebesgueMeasure]
      fun x => logarithmicResolventImaginaryCoefficient lambda x • f x := by
  exact boundedRealNaimarkMultiplier_coeFn
    (logarithmicResolventImaginaryMultiplier lambda hlambda) f

/-- Operator-norm resolvent bound for the real component. -/
theorem logarithmicResolventRealOperator_norm_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    ‖logarithmicResolventRealOperator lambda hlambda‖ ≤ |lambda.im|⁻¹ :=
  boundedRealNaimarkMultiplier_norm_le
    (logarithmicResolventRealMultiplier lambda hlambda)

/-- Operator-norm resolvent bound for the imaginary component. -/
theorem logarithmicResolventImaginaryOperator_norm_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    ‖logarithmicResolventImaginaryOperator lambda hlambda‖ ≤ |lambda.im|⁻¹ :=
  boundedRealNaimarkMultiplier_norm_le
    (logarithmicResolventImaginaryMultiplier lambda hlambda)

/-- The real resolvent component is self-adjoint. -/
theorem logarithmicResolventRealOperator_isSelfAdjoint (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    IsSelfAdjoint (logarithmicResolventRealOperator lambda hlambda) :=
  boundedRealNaimarkMultiplier_isSelfAdjoint
    (logarithmicResolventRealMultiplier lambda hlambda)

/-- The imaginary resolvent component is self-adjoint. -/
theorem logarithmicResolventImaginaryOperator_isSelfAdjoint (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    IsSelfAdjoint (logarithmicResolventImaginaryOperator lambda hlambda) :=
  boundedRealNaimarkMultiplier_isSelfAdjoint
    (logarithmicResolventImaginaryMultiplier lambda hlambda)

/-- Conjugating the spectral parameter fixes the real resolvent operator. -/
theorem logarithmicResolventRealOperator_conj (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    logarithmicResolventRealOperator (conj lambda)
        (by simpa using hlambda) =
      logarithmicResolventRealOperator lambda hlambda := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [logarithmicResolventRealOperator_coeFn (conj lambda)
      (by simpa using hlambda) f,
    logarithmicResolventRealOperator_coeFn lambda hlambda f] with x hconj hbase
  rw [hconj, hbase, logarithmicResolventRealCoefficient_conj]

/-- Conjugating the spectral parameter reverses the imaginary resolvent
operator. -/
theorem logarithmicResolventImaginaryOperator_conj (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    logarithmicResolventImaginaryOperator (conj lambda)
        (by simpa using hlambda) =
      -logarithmicResolventImaginaryOperator lambda hlambda := by
  apply ContinuousLinearMap.ext
  intro f
  rw [neg_apply]
  apply Lp.ext
  filter_upwards [logarithmicResolventImaginaryOperator_coeFn (conj lambda)
      (by simpa using hlambda) f,
    logarithmicResolventImaginaryOperator_coeFn lambda hlambda f,
    Lp.coeFn_neg (logarithmicResolventImaginaryOperator lambda hlambda f)]
      with x hconj hbase hneg
  rw [hconj, hneg, Pi.neg_apply, hbase,
    logarithmicResolventImaginaryCoefficient_conj]
  simp

/-- In the upper half-plane the imaginary resolvent component has a
nonpositive quadratic form. -/
theorem logarithmicResolventImaginaryOperator_inner_nonpos {lambda : ℂ}
    (hlambda : 0 < lambda.im) (f : NaimarkSpace) :
    inner ℝ f (logarithmicResolventImaginaryOperator lambda
      hlambda.ne' f) ≤ 0 := by
  rw [L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [logarithmicResolventImaginaryOperator_coeFn lambda
    hlambda.ne' f] with x hx
  rw [hx, real_inner_smul_right]
  exact mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlambda.le)
      (logarithmicResolventDenominator_pos hlambda.ne' x).le)
    real_inner_self_nonneg

/-- In the upper half-plane the imaginary resolvent component has a strictly
negative quadratic form on every nonzero Naimark vector. -/
theorem logarithmicResolventImaginaryOperator_inner_neg {lambda : ℂ}
    (hlambda : 0 < lambda.im) {f : NaimarkSpace} (hf : f ≠ 0) :
    inner ℝ f (logarithmicResolventImaginaryOperator lambda
      hlambda.ne' f) < 0 := by
  apply lt_of_le_of_ne
    (logarithmicResolventImaginaryOperator_inner_nonpos hlambda f)
  intro hinner
  let operator := logarithmicResolventImaginaryOperator lambda hlambda.ne'
  have hnonneg : 0 ≤ᵐ[positiveLebesgueMeasure]
      fun x => -inner ℝ (f x) (operator f x) := by
    filter_upwards [logarithmicResolventImaginaryOperator_coeFn lambda
      hlambda.ne' f] with x hx
    rw [show operator f x =
      logarithmicResolventImaginaryCoefficient lambda x • f x from hx,
      real_inner_smul_right]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlambda.le)
        (logarithmicResolventDenominator_pos hlambda.ne' x).le)
      real_inner_self_nonneg)
  have hintegrable : Integrable
      (fun x => -inner ℝ (f x) (operator f x)) positiveLebesgueMeasure :=
    (L2.integrable_inner f (operator f)).neg
  have hintegral :
      ∫ x, -inner ℝ (f x) (operator f x) ∂positiveLebesgueMeasure = 0 := by
    rw [integral_neg, ← L2.inner_def]
    change -inner ℝ f
      (logarithmicResolventImaginaryOperator lambda hlambda.ne' f) = 0
    rw [hinner, neg_zero]
  have haezero :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hintegrable).mp hintegral
  apply hf
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [haezero,
    logarithmicResolventImaginaryOperator_coeFn lambda hlambda.ne' f]
      with x hzero hx
  rw [show operator f x =
    logarithmicResolventImaginaryCoefficient lambda x • f x from hx,
    real_inner_smul_right] at hzero
  have hcoefficient : logarithmicResolventImaginaryCoefficient lambda x ≠ 0 := by
    rw [logarithmicResolventImaginaryCoefficient]
    exact div_ne_zero (neg_ne_zero.mpr hlambda.ne')
      (logarithmicResolventDenominator_ne_zero hlambda.ne' x)
  have hself : inner ℝ (f x) (f x) = 0 :=
    (mul_eq_zero.mp (neg_eq_zero.mp hzero)).resolve_left hcoefficient
  exact (inner_self_eq_zero.mp hself)

/-- In the lower half-plane the imaginary resolvent component has a
nonnegative quadratic form. -/
theorem logarithmicResolventImaginaryOperator_inner_nonneg {lambda : ℂ}
    (hlambda : lambda.im < 0) (f : NaimarkSpace) :
    0 ≤ inner ℝ f (logarithmicResolventImaginaryOperator lambda
      hlambda.ne f) := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [logarithmicResolventImaginaryOperator_coeFn lambda
    hlambda.ne f] with x hx
  rw [hx, real_inner_smul_right]
  exact mul_nonneg
    (div_nonneg (neg_nonneg.mpr hlambda.le)
      (logarithmicResolventDenominator_pos hlambda.ne x).le)
    real_inner_self_nonneg

/-- In the lower half-plane the imaginary resolvent component has a strictly
positive quadratic form on every nonzero Naimark vector. -/
theorem logarithmicResolventImaginaryOperator_inner_pos {lambda : ℂ}
    (hlambda : lambda.im < 0) {f : NaimarkSpace} (hf : f ≠ 0) :
    0 < inner ℝ f (logarithmicResolventImaginaryOperator lambda
      hlambda.ne f) := by
  have hconj : 0 < (conj lambda).im := by simpa using neg_pos.mpr hlambda
  have hstrict := logarithmicResolventImaginaryOperator_inner_neg hconj hf
  rw [logarithmicResolventImaginaryOperator_conj lambda hlambda.ne] at hstrict
  simpa using neg_pos.mpr hstrict

/-! ## Compression to the all-bases camera Hilbert space -/

/-- Adjoint of the explicit all-bases Naimark isometry. -/
def naimarkAdjoint : NaimarkSpace →L[ℝ] CameraHilbert :=
  naimarkIsometry.toContinuousLinearMap.adjoint

/-- The adjoint of the Naimark isometry is a contraction. -/
theorem naimarkAdjoint_norm_le_one : ‖naimarkAdjoint‖ ≤ 1 := by
  rw [naimarkAdjoint, LinearIsometryEquiv.norm_map]
  exact naimarkIsometry.norm_toContinuousLinearMap_le

/-- Real component of the compressed all-bases Cauchy transform. -/
def allBasesCauchyRealPart (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    CameraHilbert →L[ℝ] CameraHilbert :=
  naimarkAdjoint ∘L logarithmicResolventRealOperator lambda hlambda ∘L
    naimarkIsometry.toContinuousLinearMap

/-- Imaginary component of the compressed all-bases Cauchy transform. -/
def allBasesCauchyImaginaryPart (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    CameraHilbert →L[ℝ] CameraHilbert :=
  naimarkAdjoint ∘L logarithmicResolventImaginaryOperator lambda hlambda ∘L
    naimarkIsometry.toContinuousLinearMap

/-- The compressed real component has the expected Naimark inner-product
formula. -/
theorem inner_allBasesCauchyRealPart (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (u v : CameraHilbert) :
    inner ℝ u (allBasesCauchyRealPart lambda hlambda v) =
      inner ℝ (naimarkIsometry u)
        (logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry v)) := by
  simpa [allBasesCauchyRealPart, naimarkAdjoint,
    ContinuousLinearMap.comp_apply] using
    naimarkIsometry.toContinuousLinearMap.adjoint_inner_right u
      (logarithmicResolventRealOperator lambda hlambda
        (naimarkIsometry v))

/-- The compressed imaginary component has the expected Naimark inner-product
formula. -/
theorem inner_allBasesCauchyImaginaryPart (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (u v : CameraHilbert) :
    inner ℝ u (allBasesCauchyImaginaryPart lambda hlambda v) =
      inner ℝ (naimarkIsometry u)
        (logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry v)) := by
  simpa [allBasesCauchyImaginaryPart, naimarkAdjoint,
    ContinuousLinearMap.comp_apply] using
    naimarkIsometry.toContinuousLinearMap.adjoint_inner_right u
      (logarithmicResolventImaginaryOperator lambda hlambda
        (naimarkIsometry v))

/-- The real component of the all-bases Cauchy transform is self-adjoint. -/
theorem allBasesCauchyRealPart_isSelfAdjoint (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    IsSelfAdjoint (allBasesCauchyRealPart lambda hlambda) := by
  exact (logarithmicResolventRealOperator_isSelfAdjoint lambda hlambda).adjoint_conj
    naimarkIsometry.toContinuousLinearMap

/-- The imaginary component of the all-bases Cauchy transform is
self-adjoint. -/
theorem allBasesCauchyImaginaryPart_isSelfAdjoint (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    IsSelfAdjoint (allBasesCauchyImaginaryPart lambda hlambda) := by
  exact
    (logarithmicResolventImaginaryOperator_isSelfAdjoint lambda hlambda).adjoint_conj
      naimarkIsometry.toContinuousLinearMap

/-- Conjugating the spectral parameter fixes the real part of the compressed
Cauchy family. -/
theorem allBasesCauchyRealPart_conj (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    allBasesCauchyRealPart (conj lambda) (by simpa using hlambda) =
      allBasesCauchyRealPart lambda hlambda := by
  unfold allBasesCauchyRealPart
  rw [logarithmicResolventRealOperator_conj lambda hlambda]

/-- Conjugating the spectral parameter reverses the imaginary part of the
compressed Cauchy family. -/
theorem allBasesCauchyImaginaryPart_conj (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    allBasesCauchyImaginaryPart (conj lambda) (by simpa using hlambda) =
      -allBasesCauchyImaginaryPart lambda hlambda := by
  unfold allBasesCauchyImaginaryPart
  rw [logarithmicResolventImaginaryOperator_conj lambda hlambda]
  apply ContinuousLinearMap.ext
  intro u
  simp [naimarkAdjoint, ContinuousLinearMap.comp_apply]

/-- Compression through the Naimark isometry preserves the real-component
resolvent norm bound. -/
theorem allBasesCauchyRealPart_norm_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    ‖allBasesCauchyRealPart lambda hlambda‖ ≤ |lambda.im|⁻¹ := by
  calc
    ‖allBasesCauchyRealPart lambda hlambda‖ ≤
        ‖naimarkAdjoint‖ *
          (‖logarithmicResolventRealOperator lambda hlambda‖ *
            ‖naimarkIsometry.toContinuousLinearMap‖) := by
      rw [allBasesCauchyRealPart]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖logarithmicResolventRealOperator lambda hlambda‖ := by
      calc
        ‖naimarkAdjoint‖ *
              (‖logarithmicResolventRealOperator lambda hlambda‖ *
                ‖naimarkIsometry.toContinuousLinearMap‖) ≤
            1 * (‖logarithmicResolventRealOperator lambda hlambda‖ *
              ‖naimarkIsometry.toContinuousLinearMap‖) :=
          mul_le_mul_of_nonneg_right naimarkAdjoint_norm_le_one
            (mul_nonneg
              (norm_nonneg
                (logarithmicResolventRealOperator lambda hlambda))
              (norm_nonneg naimarkIsometry.toContinuousLinearMap))
        _ ≤ 1 * (‖logarithmicResolventRealOperator lambda hlambda‖ * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              naimarkIsometry.norm_toContinuousLinearMap_le
              (norm_nonneg
                (logarithmicResolventRealOperator lambda hlambda)))
            zero_le_one
        _ = ‖logarithmicResolventRealOperator lambda hlambda‖ := by ring
    _ ≤ |lambda.im|⁻¹ :=
      logarithmicResolventRealOperator_norm_le lambda hlambda

/-- Compression through the Naimark isometry preserves the
imaginary-component resolvent norm bound. -/
theorem allBasesCauchyImaginaryPart_norm_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    ‖allBasesCauchyImaginaryPart lambda hlambda‖ ≤ |lambda.im|⁻¹ := by
  calc
    ‖allBasesCauchyImaginaryPart lambda hlambda‖ ≤
        ‖naimarkAdjoint‖ *
          (‖logarithmicResolventImaginaryOperator lambda hlambda‖ *
            ‖naimarkIsometry.toContinuousLinearMap‖) := by
      rw [allBasesCauchyImaginaryPart]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖logarithmicResolventImaginaryOperator lambda hlambda‖ := by
      calc
        ‖naimarkAdjoint‖ *
              (‖logarithmicResolventImaginaryOperator lambda hlambda‖ *
                ‖naimarkIsometry.toContinuousLinearMap‖) ≤
            1 * (‖logarithmicResolventImaginaryOperator lambda hlambda‖ *
              ‖naimarkIsometry.toContinuousLinearMap‖) :=
          mul_le_mul_of_nonneg_right naimarkAdjoint_norm_le_one
            (mul_nonneg
              (norm_nonneg
                (logarithmicResolventImaginaryOperator lambda hlambda))
              (norm_nonneg naimarkIsometry.toContinuousLinearMap))
        _ ≤ 1 * (‖logarithmicResolventImaginaryOperator lambda hlambda‖ * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              naimarkIsometry.norm_toContinuousLinearMap_le
              (norm_nonneg
                (logarithmicResolventImaginaryOperator lambda hlambda)))
            zero_le_one
        _ = ‖logarithmicResolventImaginaryOperator lambda hlambda‖ := by ring
    _ ≤ |lambda.im|⁻¹ :=
      logarithmicResolventImaginaryOperator_norm_le lambda hlambda

/-- The compressed Cauchy family has the anti-Herglotz sign in the upper
half-plane. -/
theorem allBasesCauchyImaginaryPart_inner_nonpos {lambda : ℂ}
    (hlambda : 0 < lambda.im) (u : CameraHilbert) :
    inner ℝ u (allBasesCauchyImaginaryPart lambda hlambda.ne' u) ≤ 0 := by
  rw [inner_allBasesCauchyImaginaryPart]
  exact logarithmicResolventImaginaryOperator_inner_nonpos hlambda
    (naimarkIsometry u)

/-- The all-bases Cauchy family has strict anti-Herglotz sign in the upper
half-plane on every nonzero camera vector. -/
theorem allBasesCauchyImaginaryPart_inner_neg {lambda : ℂ}
    (hlambda : 0 < lambda.im) {u : CameraHilbert} (hu : u ≠ 0) :
    inner ℝ u (allBasesCauchyImaginaryPart lambda hlambda.ne' u) < 0 := by
  rw [inner_allBasesCauchyImaginaryPart]
  exact logarithmicResolventImaginaryOperator_inner_neg hlambda
    (by simpa using naimarkIsometry.injective.ne hu)

/-- The compressed Cauchy family has the reversed sign in the lower
half-plane. -/
theorem allBasesCauchyImaginaryPart_inner_nonneg {lambda : ℂ}
    (hlambda : lambda.im < 0) (u : CameraHilbert) :
    0 ≤ inner ℝ u (allBasesCauchyImaginaryPart lambda hlambda.ne u) := by
  rw [inner_allBasesCauchyImaginaryPart]
  exact logarithmicResolventImaginaryOperator_inner_nonneg hlambda
    (naimarkIsometry u)

/-- The all-bases Cauchy family has strict positive imaginary sign in the
lower half-plane on every nonzero camera vector. -/
theorem allBasesCauchyImaginaryPart_inner_pos {lambda : ℂ}
    (hlambda : lambda.im < 0) {u : CameraHilbert} (hu : u ≠ 0) :
    0 < inner ℝ u (allBasesCauchyImaginaryPart lambda hlambda.ne u) := by
  rw [inner_allBasesCauchyImaginaryPart]
  exact logarithmicResolventImaginaryOperator_inner_pos hlambda
    (by simpa using naimarkIsometry.injective.ne hu)

/-- Away from the real axis, the imaginary component of the compressed
Cauchy family is injective.  This is the operator consequence of its strict
quadratic-form sign. -/
theorem allBasesCauchyImaginaryPart_injective (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    Function.Injective (allBasesCauchyImaginaryPart lambda hlambda) := by
  intro u v huv
  have hkernel : allBasesCauchyImaginaryPart lambda hlambda (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hsub : u - v = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hlambda with hlower | hupper
    · have hstrict :=
        allBasesCauchyImaginaryPart_inner_pos hlower hne
      rw [hkernel, inner_zero_right] at hstrict
      exact (lt_irrefl 0 hstrict)
    · have hstrict :=
        allBasesCauchyImaginaryPart_inner_neg hupper hne
      rw [hkernel, inner_zero_right] at hstrict
      exact (lt_irrefl 0 hstrict)
  exact sub_eq_zero.mp hsub

/-- Away from the real axis, the imaginary component of the compressed
Cauchy family has dense range.  Self-adjointness turns injectivity into
density of the range. -/
theorem allBasesCauchyImaginaryPart_denseRange (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    Dense (LinearMap.range
      (allBasesCauchyImaginaryPart lambda hlambda :
        CameraHilbert →ₗ[ℝ] CameraHilbert) : Set CameraHilbert) := by
  have hsymm : (allBasesCauchyImaginaryPart lambda hlambda :
      CameraHilbert →ₗ[ℝ] CameraHilbert).IsSymmetric :=
    (allBasesCauchyImaginaryPart_isSelfAdjoint lambda hlambda).isSymmetric
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  rw [← (LinearMap.range
    (allBasesCauchyImaginaryPart lambda hlambda :
      CameraHilbert →ₗ[ℝ] CameraHilbert)).orthogonal_orthogonal_eq_closure]
  rw [hsymm.orthogonal_range,
    LinearMap.ker_eq_bot.mpr
      (allBasesCauchyImaginaryPart_injective lambda hlambda),
    Submodule.bot_orthogonal_eq_top]

/-- The two real continuous operators that canonically represent the complex
all-bases Cauchy transform on the current real camera Hilbert space. -/
structure RealifiedAllBasesCauchyOperator where
  realPart : CameraHilbert →L[ℝ] CameraHilbert
  imaginaryPart : CameraHilbert →L[ℝ] CameraHilbert

/-- Canonical real/imaginary-component representation of
`V† (lambda - Y)⁻¹ V`. -/
def allBasesCauchyOperator (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedAllBasesCauchyOperator where
  realPart := allBasesCauchyRealPart lambda hlambda
  imaginaryPart := allBasesCauchyImaginaryPart lambda hlambda

end NativeCarrySpectralWeyl.Infinite
