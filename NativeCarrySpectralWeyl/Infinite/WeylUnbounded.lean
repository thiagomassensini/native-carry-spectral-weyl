import NativeCarrySpectralWeyl.Infinite.WeylInverse

/-!
# Quantitative camera sequence for the all-bases Weyl inverse

This file supplies the missing quantitative endpoint of the infinite-camera
construction.  The logarithmic coordinate on the normalized camera interval
`(0, ell]` has mean `log ell` and variance exactly one.  Resolvent identities
then force the complete Cauchy block to send a sequence of unit camera vectors
to zero as the camera slope tends to infinity.  Consequently its densely
defined inverse cannot satisfy a global norm bound on its domain.
-/

open scoped ENNReal MeasureTheory RealInnerProductSpace ComplexConjugate
open Filter Set MeasureTheory intervalIntegral Topology

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

open NativeCarrySpectralWeyl.Camera

/-- The logarithmic coordinate on `(0, b]`, centered at its exact mean
`log b`, has unnormalized variance `b`. -/
theorem integral_logarithmicCoordinate_sub_log_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in 0..b, (logarithmicCoordinate x - Real.log b) ^ 2 = b := by
  have htwo :=
    NativeCarrySpectralWeyl.Finite.intervalIntegrable_centeredLogSq_zero hb
  have hone :=
    NativeCarrySpectralWeyl.Finite.intervalIntegrable_centeredLog_zero
      (b := b)
  have htwo' : IntervalIntegrable
      (fun x : ℝ => logarithmicCoordinate x ^ 2) volume 0 b := by
    change IntervalIntegrable (fun x : ℝ => (1 + Real.log x) ^ 2)
      volume 0 b
    exact htwo
  have hone' : IntervalIntegrable logarithmicCoordinate volume 0 b := by
    change IntervalIntegrable (fun x : ℝ => 1 + Real.log x) volume 0 b
    exact hone
  have hconst : IntervalIntegrable (fun _ : ℝ => Real.log b ^ 2)
      volume 0 b := intervalIntegrable_const
  calc
    ∫ x in 0..b, (logarithmicCoordinate x - Real.log b) ^ 2 =
        ∫ x in 0..b,
          logarithmicCoordinate x ^ 2 -
            (2 * Real.log b) * logarithmicCoordinate x +
              Real.log b ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [logarithmicCoordinate]
        ring
    _ = (∫ x in 0..b, logarithmicCoordinate x ^ 2) -
          (2 * Real.log b) *
            (∫ x in 0..b, logarithmicCoordinate x) +
          ∫ _x in 0..b, Real.log b ^ 2 := by
        rw [intervalIntegral.integral_add
            (htwo'.sub (hone'.const_mul _)) hconst,
          intervalIntegral.integral_sub htwo' (hone'.const_mul _),
          intervalIntegral.integral_const_mul]
    _ = b := by
        simp only [logarithmicCoordinate]
        rw [NativeCarrySpectralWeyl.Finite.integral_centeredLogSq_zero hb,
          NativeCarrySpectralWeyl.Finite.integral_centeredLog_zero hb,
          intervalIntegral.integral_const]
        ring

/-! ## Exact unit variance on one camera interval -/

/-- The camera step vector after subtracting its exact logarithmic mean. -/
def centeredNaimarkCameraVector (camera : CameraIndex) : NaimarkSpace :=
  logarithmicMultiplication
      ⟨naimarkCameraVector camera,
        naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩ -
    Real.log (cameraSlope (cameraLabel camera) : ℝ) •
      naimarkCameraVector camera

/-- Pointwise formula for the centered camera step vector. -/
theorem centeredNaimarkCameraVector_coeFn (camera : CameraIndex) :
    ⇑(centeredNaimarkCameraVector camera) =ᵐ[positiveLebesgueMeasure]
      fun x =>
        (logarithmicCoordinate x -
            Real.log (cameraSlope (cameraLabel camera) : ℝ)) •
          (cameraInterval camera).indicator
            (fun _ => kolmogorovVector camera) x := by
  filter_upwards [logarithmicMultiplication_coeFn
      ⟨naimarkCameraVector camera,
        naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩,
    naimarkCameraVector_coeFn camera,
    Lp.coeFn_sub
      (logarithmicMultiplication
        ⟨naimarkCameraVector camera,
          naimarkCameraVector_mem_logarithmicMultiplicationDomain camera⟩)
      (Real.log (cameraSlope (cameraLabel camera) : ℝ) •
        naimarkCameraVector camera),
    Lp.coeFn_smul
      (Real.log (cameraSlope (cameraLabel camera) : ℝ))
      (naimarkCameraVector camera)] with x hmul hcamera hsub hsmul
  rw [centeredNaimarkCameraVector, hsub, Pi.sub_apply, hmul,
    logarithmicWeightedFunction, hsmul, Pi.smul_apply, hcamera]
  rw [sub_smul]

/-- Scalar form of the exact camera-interval variance identity under the
positive-half-line measure. -/
theorem integral_indicator_camera_centeredCoordinate_sq
    (camera : CameraIndex) :
    ∫ x,
        (cameraInterval camera).indicator
          (fun x =>
            (logarithmicCoordinate x -
              Real.log (cameraSlope (cameraLabel camera) : ℝ)) ^ 2) x
      ∂positiveLebesgueMeasure =
      (cameraSlope (cameraLabel camera) : ℝ) := by
  rw [MeasureTheory.integral_indicator (cameraInterval_measurable camera)]
  have hrestrict :
      positiveLebesgueMeasure.restrict (cameraInterval camera) =
        volume.restrict (cameraInterval camera) := by
    rw [positiveLebesgueMeasure,
      Measure.restrict_restrict_of_subset
        (cameraInterval_subset_positive camera)]
  rw [hrestrict, cameraInterval]
  rw [← intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ cameraSlope (cameraLabel camera) by positivity)]
  exact integral_logarithmicCoordinate_sub_log_sq
    (show (0 : ℝ) < cameraSlope (cameraLabel camera) by
      exact_mod_cast cameraSlope_pos camera)

/-- Centering at `log ell` preserves the squared norm of a camera step
vector: this is the exact unit-variance identity from the atlas notes. -/
theorem norm_centeredNaimarkCameraVector_sq (camera : CameraIndex) :
    ‖centeredNaimarkCameraVector camera‖ ^ 2 =
      ‖naimarkCameraVector camera‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ),
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ)]
  calc
    inner ℝ (centeredNaimarkCameraVector camera)
        (centeredNaimarkCameraVector camera) =
      ∫ x,
        inner ℝ (kolmogorovVector camera) (kolmogorovVector camera) *
          (cameraInterval camera).indicator
            (fun x =>
              (logarithmicCoordinate x -
                Real.log (cameraSlope (cameraLabel camera) : ℝ)) ^ 2) x
        ∂positiveLebesgueMeasure := by
      rw [L2.inner_def]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [centeredNaimarkCameraVector_coeFn camera] with x hx
      rw [hx]
      by_cases hinterval : x ∈ cameraInterval camera
      · simp only [Set.indicator_of_mem hinterval, real_inner_smul_left,
          real_inner_smul_right]
        ring
      · simp [Set.indicator_of_notMem hinterval]
    _ = inner ℝ (kolmogorovVector camera) (kolmogorovVector camera) *
        (cameraSlope (cameraLabel camera) : ℝ) := by
      rw [MeasureTheory.integral_const_mul,
        integral_indicator_camera_centeredCoordinate_sq]
    _ = gramKernel camera camera := by
      rw [inner_kolmogorovVector]
      simp [gramKernel, mul_comm]
    _ = inner ℝ (naimarkCameraVector camera)
        (naimarkCameraVector camera) := by
      rw [inner_naimarkCameraVector]

/-- Exact (unsquared) unit-variance norm identity. -/
theorem norm_centeredNaimarkCameraVector (camera : CameraIndex) :
    ‖centeredNaimarkCameraVector camera‖ =
      ‖naimarkCameraVector camera‖ := by
  have hsq := norm_centeredNaimarkCameraVector_sq camera
  nlinarith [norm_nonneg (centeredNaimarkCameraVector camera),
    norm_nonneg (naimarkCameraVector camera)]

/-! ## Quantitative resolvent estimate -/

/-- The scalar denominator of the resolvent at a real center `mu`. -/
def centeredResolventDenominator (lambda : ℂ) (mu : ℝ) : ℝ :=
  (lambda.re - mu) ^ 2 + lambda.im ^ 2

/-- Real component of `(lambda - mu)⁻¹`. -/
def centeredResolventRealCoefficient (lambda : ℂ) (mu : ℝ) : ℝ :=
  (lambda.re - mu) / centeredResolventDenominator lambda mu

/-- Imaginary component of `(lambda - mu)⁻¹`. -/
def centeredResolventImaginaryCoefficient (lambda : ℂ) (mu : ℝ) : ℝ :=
  -lambda.im / centeredResolventDenominator lambda mu

/-- The centered scalar denominator is positive off the real axis. -/
theorem centeredResolventDenominator_pos {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (mu : ℝ) :
    0 < centeredResolventDenominator lambda mu := by
  rw [centeredResolventDenominator]
  nlinarith [sq_nonneg (lambda.re - mu), sq_pos_of_ne_zero hlambda]

/-- Real-coordinate resolvent shift identity. -/
theorem logarithmicResolventRealCoefficient_shift {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (mu x : ℝ) :
    logarithmicResolventRealCoefficient lambda x =
      centeredResolventRealCoefficient lambda mu *
          (1 + (logarithmicCoordinate x - mu) *
            logarithmicResolventRealCoefficient lambda x) -
        centeredResolventImaginaryCoefficient lambda mu *
          ((logarithmicCoordinate x - mu) *
            logarithmicResolventImaginaryCoefficient lambda x) := by
  rw [logarithmicResolventRealCoefficient,
    logarithmicResolventImaginaryCoefficient,
    centeredResolventRealCoefficient,
    centeredResolventImaginaryCoefficient]
  have hx := logarithmicResolventDenominator_ne_zero hlambda x
  have hmu := (centeredResolventDenominator_pos hlambda mu).ne'
  field_simp
  rw [logarithmicResolventDenominator, centeredResolventDenominator]
  ring

/-- Imaginary-coordinate resolvent shift identity. -/
theorem logarithmicResolventImaginaryCoefficient_shift {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (mu x : ℝ) :
    logarithmicResolventImaginaryCoefficient lambda x =
      centeredResolventImaginaryCoefficient lambda mu *
          (1 + (logarithmicCoordinate x - mu) *
            logarithmicResolventRealCoefficient lambda x) +
        centeredResolventRealCoefficient lambda mu *
          ((logarithmicCoordinate x - mu) *
            logarithmicResolventImaginaryCoefficient lambda x) := by
  rw [logarithmicResolventRealCoefficient,
    logarithmicResolventImaginaryCoefficient,
    centeredResolventRealCoefficient,
    centeredResolventImaginaryCoefficient]
  have hx := logarithmicResolventDenominator_ne_zero hlambda x
  have hmu := (centeredResolventDenominator_pos hlambda mu).ne'
  field_simp
  rw [logarithmicResolventDenominator, centeredResolventDenominator]
  ring

/-- Operator form of the real-coordinate resolvent shift identity. -/
theorem logarithmicResolventRealOperator_shift {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (mu : ℝ) (f g : NaimarkSpace)
    (hg : ⇑g =ᵐ[positiveLebesgueMeasure]
      fun x => (logarithmicCoordinate x - mu) • f x) :
    logarithmicResolventRealOperator lambda hlambda f =
      centeredResolventRealCoefficient lambda mu •
          (f + logarithmicResolventRealOperator lambda hlambda g) -
        centeredResolventImaginaryCoefficient lambda mu •
          logarithmicResolventImaginaryOperator lambda hlambda g := by
  apply Lp.ext
  filter_upwards [logarithmicResolventRealOperator_coeFn lambda hlambda f,
    logarithmicResolventRealOperator_coeFn lambda hlambda g,
    logarithmicResolventImaginaryOperator_coeFn lambda hlambda g,
    hg,
    Lp.coeFn_add f (logarithmicResolventRealOperator lambda hlambda g),
    Lp.coeFn_smul (centeredResolventRealCoefficient lambda mu)
      (f + logarithmicResolventRealOperator lambda hlambda g),
    Lp.coeFn_smul (centeredResolventImaginaryCoefficient lambda mu)
      (logarithmicResolventImaginaryOperator lambda hlambda g),
    Lp.coeFn_sub
      (centeredResolventRealCoefficient lambda mu •
        (f + logarithmicResolventRealOperator lambda hlambda g))
      (centeredResolventImaginaryCoefficient lambda mu •
        logarithmicResolventImaginaryOperator lambda hlambda g)]
      with x hleft hreal himag hgx hadd hsmulReal hsmulImag hsub
  rw [hleft, hsub, Pi.sub_apply, hsmulReal, Pi.smul_apply, hadd,
    Pi.add_apply, hreal, hsmulImag, Pi.smul_apply, himag, hgx]
  have hscalar := logarithmicResolventRealCoefficient_shift hlambda mu x
  match_scalars
  linear_combination hscalar

/-- Operator form of the imaginary-coordinate resolvent shift identity. -/
theorem logarithmicResolventImaginaryOperator_shift {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (mu : ℝ) (f g : NaimarkSpace)
    (hg : ⇑g =ᵐ[positiveLebesgueMeasure]
      fun x => (logarithmicCoordinate x - mu) • f x) :
    logarithmicResolventImaginaryOperator lambda hlambda f =
      centeredResolventImaginaryCoefficient lambda mu •
          (f + logarithmicResolventRealOperator lambda hlambda g) +
        centeredResolventRealCoefficient lambda mu •
          logarithmicResolventImaginaryOperator lambda hlambda g := by
  apply Lp.ext
  filter_upwards [logarithmicResolventImaginaryOperator_coeFn lambda hlambda f,
    logarithmicResolventRealOperator_coeFn lambda hlambda g,
    logarithmicResolventImaginaryOperator_coeFn lambda hlambda g,
    hg,
    Lp.coeFn_add f (logarithmicResolventRealOperator lambda hlambda g),
    Lp.coeFn_smul (centeredResolventImaginaryCoefficient lambda mu)
      (f + logarithmicResolventRealOperator lambda hlambda g),
    Lp.coeFn_smul (centeredResolventRealCoefficient lambda mu)
      (logarithmicResolventImaginaryOperator lambda hlambda g),
    Lp.coeFn_add
      (centeredResolventImaginaryCoefficient lambda mu •
        (f + logarithmicResolventRealOperator lambda hlambda g))
      (centeredResolventRealCoefficient lambda mu •
        logarithmicResolventImaginaryOperator lambda hlambda g)]
      with x hleft hreal himag hgx hadd hsmulImag hsmulReal hout
  rw [hleft, hout, Pi.add_apply, hsmulImag, Pi.smul_apply, hadd,
    Pi.add_apply, hreal, hsmulReal, Pi.smul_apply, himag, hgx]
  have hscalar := logarithmicResolventImaginaryCoefficient_shift hlambda mu x
  match_scalars
  linear_combination hscalar

/-- Application-level ambient resolvent bound for the real component. -/
theorem norm_logarithmicResolventRealOperator_apply_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (f : NaimarkSpace) :
    ‖logarithmicResolventRealOperator lambda hlambda f‖ ≤
      |lambda.im|⁻¹ * ‖f‖ := by
  calc
    ‖logarithmicResolventRealOperator lambda hlambda f‖ ≤
        ‖logarithmicResolventRealOperator lambda hlambda‖ * ‖f‖ :=
      (logarithmicResolventRealOperator lambda hlambda).le_opNorm f
    _ ≤ |lambda.im|⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (logarithmicResolventRealOperator_norm_le lambda hlambda)
        (norm_nonneg f)

/-- Application-level ambient resolvent bound for the imaginary component. -/
theorem norm_logarithmicResolventImaginaryOperator_apply_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (f : NaimarkSpace) :
    ‖logarithmicResolventImaginaryOperator lambda hlambda f‖ ≤
      |lambda.im|⁻¹ * ‖f‖ := by
  calc
    ‖logarithmicResolventImaginaryOperator lambda hlambda f‖ ≤
        ‖logarithmicResolventImaginaryOperator lambda hlambda‖ * ‖f‖ :=
      (logarithmicResolventImaginaryOperator lambda hlambda).le_opNorm f
    _ ≤ |lambda.im|⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (logarithmicResolventImaginaryOperator_norm_le lambda hlambda)
        (norm_nonneg f)

/-- Quantitative norm estimate obtained from the real resolvent shift
identity. -/
theorem norm_logarithmicResolventRealOperator_le_shift {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (mu : ℝ) (f g : NaimarkSpace)
    (hg : ⇑g =ᵐ[positiveLebesgueMeasure]
      fun x => (logarithmicCoordinate x - mu) • f x) :
    ‖logarithmicResolventRealOperator lambda hlambda f‖ ≤
      |centeredResolventRealCoefficient lambda mu| * ‖f‖ +
        (|centeredResolventRealCoefficient lambda mu| +
            |centeredResolventImaginaryCoefficient lambda mu|) *
          |lambda.im|⁻¹ * ‖g‖ := by
  rw [logarithmicResolventRealOperator_shift hlambda mu f g hg]
  calc
    ‖centeredResolventRealCoefficient lambda mu •
          (f + logarithmicResolventRealOperator lambda hlambda g) -
        centeredResolventImaginaryCoefficient lambda mu •
          logarithmicResolventImaginaryOperator lambda hlambda g‖ ≤
      ‖centeredResolventRealCoefficient lambda mu •
          (f + logarithmicResolventRealOperator lambda hlambda g)‖ +
        ‖centeredResolventImaginaryCoefficient lambda mu •
          logarithmicResolventImaginaryOperator lambda hlambda g‖ :=
      norm_sub_le _ _
    _ = |centeredResolventRealCoefficient lambda mu| *
          ‖f + logarithmicResolventRealOperator lambda hlambda g‖ +
        |centeredResolventImaginaryCoefficient lambda mu| *
          ‖logarithmicResolventImaginaryOperator lambda hlambda g‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ |centeredResolventRealCoefficient lambda mu| *
          (‖f‖ + ‖logarithmicResolventRealOperator lambda hlambda g‖) +
        |centeredResolventImaginaryCoefficient lambda mu| *
          ‖logarithmicResolventImaginaryOperator lambda hlambda g‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ |centeredResolventRealCoefficient lambda mu| *
          (‖f‖ + |lambda.im|⁻¹ * ‖g‖) +
        |centeredResolventImaginaryCoefficient lambda mu| *
          (|lambda.im|⁻¹ * ‖g‖) := by
      gcongr
      · exact norm_logarithmicResolventRealOperator_apply_le lambda hlambda g
      · exact norm_logarithmicResolventImaginaryOperator_apply_le lambda hlambda g
    _ = |centeredResolventRealCoefficient lambda mu| * ‖f‖ +
        (|centeredResolventRealCoefficient lambda mu| +
            |centeredResolventImaginaryCoefficient lambda mu|) *
          |lambda.im|⁻¹ * ‖g‖ := by ring

/-- Quantitative norm estimate obtained from the imaginary resolvent shift
identity. -/
theorem norm_logarithmicResolventImaginaryOperator_le_shift {lambda : ℂ}
    (hlambda : lambda.im ≠ 0) (mu : ℝ) (f g : NaimarkSpace)
    (hg : ⇑g =ᵐ[positiveLebesgueMeasure]
      fun x => (logarithmicCoordinate x - mu) • f x) :
    ‖logarithmicResolventImaginaryOperator lambda hlambda f‖ ≤
      |centeredResolventImaginaryCoefficient lambda mu| * ‖f‖ +
        (|centeredResolventRealCoefficient lambda mu| +
            |centeredResolventImaginaryCoefficient lambda mu|) *
          |lambda.im|⁻¹ * ‖g‖ := by
  rw [logarithmicResolventImaginaryOperator_shift hlambda mu f g hg]
  calc
    ‖centeredResolventImaginaryCoefficient lambda mu •
          (f + logarithmicResolventRealOperator lambda hlambda g) +
        centeredResolventRealCoefficient lambda mu •
          logarithmicResolventImaginaryOperator lambda hlambda g‖ ≤
      ‖centeredResolventImaginaryCoefficient lambda mu •
          (f + logarithmicResolventRealOperator lambda hlambda g)‖ +
        ‖centeredResolventRealCoefficient lambda mu •
          logarithmicResolventImaginaryOperator lambda hlambda g‖ :=
      norm_add_le _ _
    _ = |centeredResolventImaginaryCoefficient lambda mu| *
          ‖f + logarithmicResolventRealOperator lambda hlambda g‖ +
        |centeredResolventRealCoefficient lambda mu| *
          ‖logarithmicResolventImaginaryOperator lambda hlambda g‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ |centeredResolventImaginaryCoefficient lambda mu| *
          (‖f‖ + ‖logarithmicResolventRealOperator lambda hlambda g‖) +
        |centeredResolventRealCoefficient lambda mu| *
          ‖logarithmicResolventImaginaryOperator lambda hlambda g‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ |centeredResolventImaginaryCoefficient lambda mu| *
          (‖f‖ + |lambda.im|⁻¹ * ‖g‖) +
        |centeredResolventRealCoefficient lambda mu| *
          (|lambda.im|⁻¹ * ‖g‖) := by
      gcongr
      · exact norm_logarithmicResolventRealOperator_apply_le lambda hlambda g
      · exact norm_logarithmicResolventImaginaryOperator_apply_le lambda hlambda g
    _ = |centeredResolventImaginaryCoefficient lambda mu| * ‖f‖ +
        (|centeredResolventRealCoefficient lambda mu| +
            |centeredResolventImaginaryCoefficient lambda mu|) *
          |lambda.im|⁻¹ * ‖g‖ := by ring

/-! ## Camera-level quantitative bound -/

/-- The centered camera vector is pointwise `(y - log ell)` times the
uncentered camera vector. -/
theorem centeredNaimarkCameraVector_coeFn_mul (camera : CameraIndex) :
    ⇑(centeredNaimarkCameraVector camera) =ᵐ[positiveLebesgueMeasure]
      fun x =>
        (logarithmicCoordinate x -
            Real.log (cameraSlope (cameraLabel camera) : ℝ)) •
          (naimarkCameraVector camera) x := by
  filter_upwards [centeredNaimarkCameraVector_coeFn camera,
    naimarkCameraVector_coeFn camera] with x hcentered hcamera
  rw [hcentered, hcamera]

/-- Compression by the Naimark isometry does not increase the norm of the
ambient real resolvent component. -/
theorem norm_allBasesCauchyRealPart_apply_le_ambient (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (u : CameraHilbert) :
    ‖allBasesCauchyRealPart lambda hlambda u‖ ≤
      ‖logarithmicResolventRealOperator lambda hlambda
        (naimarkIsometry u)‖ := by
  rw [allBasesCauchyRealPart]
  simp only [ContinuousLinearMap.comp_apply]
  calc
    ‖naimarkAdjoint
        (logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry u))‖ ≤
      ‖naimarkAdjoint‖ *
        ‖logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry u)‖ :=
      naimarkAdjoint.le_opNorm _
    _ ≤ 1 *
        ‖logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry u)‖ :=
      mul_le_mul_of_nonneg_right naimarkAdjoint_norm_le_one (norm_nonneg _)
    _ = ‖logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry u)‖ := one_mul _

/-- Compression by the Naimark isometry does not increase the norm of the
ambient imaginary resolvent component. -/
theorem norm_allBasesCauchyImaginaryPart_apply_le_ambient (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (u : CameraHilbert) :
    ‖allBasesCauchyImaginaryPart lambda hlambda u‖ ≤
      ‖logarithmicResolventImaginaryOperator lambda hlambda
        (naimarkIsometry u)‖ := by
  rw [allBasesCauchyImaginaryPart]
  simp only [ContinuousLinearMap.comp_apply]
  calc
    ‖naimarkAdjoint
        (logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry u))‖ ≤
      ‖naimarkAdjoint‖ *
        ‖logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry u)‖ :=
      naimarkAdjoint.le_opNorm _
    _ ≤ 1 *
        ‖logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry u)‖ :=
      mul_le_mul_of_nonneg_right naimarkAdjoint_norm_le_one (norm_nonneg _)
    _ = ‖logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry u)‖ := one_mul _

/-- Sum of the moduli of the real and imaginary centered scalar resolvent
coefficients. -/
def centeredResolventCoefficientSum (lambda : ℂ) (mu : ℝ) : ℝ :=
  |centeredResolventRealCoefficient lambda mu| +
    |centeredResolventImaginaryCoefficient lambda mu|

/-- Explicit camera-sequence bound for the complete realified Cauchy block. -/
def cameraCauchyQuantitativeBound (lambda : ℂ) (mu : ℝ) : ℝ :=
  centeredResolventCoefficientSum lambda mu *
    (1 + 2 * |lambda.im|⁻¹)

/-- The real compressed component on one camera satisfies the centered
quantitative estimate. -/
theorem norm_allBasesCauchyRealPart_cameraVector_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (camera : CameraIndex) :
    ‖allBasesCauchyRealPart lambda hlambda (cameraVector camera)‖ ≤
      (|centeredResolventRealCoefficient lambda
          (Real.log (cameraSlope (cameraLabel camera) : ℝ))| +
        centeredResolventCoefficientSum lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
          |lambda.im|⁻¹) * ‖cameraVector camera‖ := by
  calc
    ‖allBasesCauchyRealPart lambda hlambda (cameraVector camera)‖ ≤
        ‖logarithmicResolventRealOperator lambda hlambda
          (naimarkIsometry (cameraVector camera))‖ :=
      norm_allBasesCauchyRealPart_apply_le_ambient lambda hlambda _
    _ = ‖logarithmicResolventRealOperator lambda hlambda
          (naimarkCameraVector camera)‖ := by rw [naimarkIsometry_cameraVector]
    _ ≤ |centeredResolventRealCoefficient lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ))| *
          ‖naimarkCameraVector camera‖ +
        centeredResolventCoefficientSum lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
          |lambda.im|⁻¹ * ‖centeredNaimarkCameraVector camera‖ := by
      exact norm_logarithmicResolventRealOperator_le_shift hlambda _ _ _
        (centeredNaimarkCameraVector_coeFn_mul camera)
    _ = (|centeredResolventRealCoefficient lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ))| +
          centeredResolventCoefficientSum lambda
              (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
            |lambda.im|⁻¹) * ‖cameraVector camera‖ := by
      rw [norm_centeredNaimarkCameraVector,
        ← naimarkIsometry_cameraVector,
        naimarkIsometry.norm_map]
      ring

/-- The imaginary compressed component on one camera satisfies the centered
quantitative estimate. -/
theorem norm_allBasesCauchyImaginaryPart_cameraVector_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (camera : CameraIndex) :
    ‖allBasesCauchyImaginaryPart lambda hlambda (cameraVector camera)‖ ≤
      (|centeredResolventImaginaryCoefficient lambda
          (Real.log (cameraSlope (cameraLabel camera) : ℝ))| +
        centeredResolventCoefficientSum lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
          |lambda.im|⁻¹) * ‖cameraVector camera‖ := by
  calc
    ‖allBasesCauchyImaginaryPart lambda hlambda (cameraVector camera)‖ ≤
        ‖logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkIsometry (cameraVector camera))‖ :=
      norm_allBasesCauchyImaginaryPart_apply_le_ambient lambda hlambda _
    _ = ‖logarithmicResolventImaginaryOperator lambda hlambda
          (naimarkCameraVector camera)‖ := by rw [naimarkIsometry_cameraVector]
    _ ≤ |centeredResolventImaginaryCoefficient lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ))| *
          ‖naimarkCameraVector camera‖ +
        centeredResolventCoefficientSum lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
          |lambda.im|⁻¹ * ‖centeredNaimarkCameraVector camera‖ := by
      exact norm_logarithmicResolventImaginaryOperator_le_shift hlambda _ _ _
        (centeredNaimarkCameraVector_coeFn_mul camera)
    _ = (|centeredResolventImaginaryCoefficient lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ))| +
          centeredResolventCoefficientSum lambda
              (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
            |lambda.im|⁻¹) * ‖cameraVector camera‖ := by
      rw [norm_centeredNaimarkCameraVector,
        ← naimarkIsometry_cameraVector,
        naimarkIsometry.norm_map]
      ring

/-- Canonical embedding of a real camera vector into the first coordinate of
the realified complexification. -/
def realifiedCameraEmbedding (u : CameraHilbert) :
    RealifiedCameraComplexification :=
  WithLp.toLp 2 (u, 0)

@[simp] theorem realifiedCameraEmbedding_fst (u : CameraHilbert) :
    (realifiedCameraEmbedding u).fst = u := rfl

@[simp] theorem realifiedCameraEmbedding_snd (u : CameraHilbert) :
    (realifiedCameraEmbedding u).snd = 0 := rfl

/-- The first-coordinate embedding is isometric. -/
@[simp] theorem norm_realifiedCameraEmbedding (u : CameraHilbert) :
    ‖realifiedCameraEmbedding u‖ = ‖u‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp

/-- The `L²` product norm is bounded by the sum of its coordinate norms. -/
theorem norm_realifiedCameraComplexification_le_add
    (z : RealifiedCameraComplexification) :
    ‖z‖ ≤ ‖z.fst‖ + ‖z.snd‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  have hsqrt :
      Real.sqrt (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2) ^ 2 =
        ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2),
    norm_nonneg z.fst, norm_nonneg z.snd,
    mul_nonneg (norm_nonneg z.fst) (norm_nonneg z.snd)]

/-- Complete quantitative estimate on a canonical camera vector embedded in
the realified complexification. -/
theorem norm_allBasesCauchyBlock_realifiedCameraEmbedding_le (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) (camera : CameraIndex) :
    ‖allBasesCauchyBlock lambda hlambda
        (realifiedCameraEmbedding (cameraVector camera))‖ ≤
      cameraCauchyQuantitativeBound lambda
          (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
        ‖cameraVector camera‖ := by
  calc
    ‖allBasesCauchyBlock lambda hlambda
        (realifiedCameraEmbedding (cameraVector camera))‖ ≤
      ‖(allBasesCauchyBlock lambda hlambda
          (realifiedCameraEmbedding (cameraVector camera))).fst‖ +
        ‖(allBasesCauchyBlock lambda hlambda
          (realifiedCameraEmbedding (cameraVector camera))).snd‖ :=
      norm_realifiedCameraComplexification_le_add _
    _ = ‖allBasesCauchyRealPart lambda hlambda (cameraVector camera)‖ +
        ‖allBasesCauchyImaginaryPart lambda hlambda
          (cameraVector camera)‖ := by simp
    _ ≤
        (|centeredResolventRealCoefficient lambda
              (Real.log (cameraSlope (cameraLabel camera) : ℝ))| +
            centeredResolventCoefficientSum lambda
                (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
              |lambda.im|⁻¹) * ‖cameraVector camera‖ +
          (|centeredResolventImaginaryCoefficient lambda
              (Real.log (cameraSlope (cameraLabel camera) : ℝ))| +
            centeredResolventCoefficientSum lambda
                (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
              |lambda.im|⁻¹) * ‖cameraVector camera‖ :=
      add_le_add
        (norm_allBasesCauchyRealPart_cameraVector_le lambda hlambda camera)
        (norm_allBasesCauchyImaginaryPart_cameraVector_le lambda hlambda camera)
    _ = cameraCauchyQuantitativeBound lambda
          (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
        ‖cameraVector camera‖ := by
      simp only [cameraCauchyQuantitativeBound,
        centeredResolventCoefficientSum]
      ring

/-! ## Escape to infinite camera slope -/

/-- The centered real scalar resolvent coefficient vanishes as its real
center escapes to `+∞`. -/
theorem tendsto_centeredResolventRealCoefficient_atTop (lambda : ℂ) :
    Tendsto (centeredResolventRealCoefficient lambda) atTop (nhds 0) := by
  let u : ℝ → ℝ := fun mu => mu - lambda.re
  have hu : Tendsto u atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b + lambda.re)] with mu hmu
    dsimp only [u]
    linarith
  have huInv : Tendsto (fun mu => (u mu)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hu
  have hden : Tendsto
      (fun mu => 1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2)
      atTop (nhds 1) := by
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.mul (huInv.pow 2)) using 1
    all_goals ring
  have hquot : Tendsto
      (fun mu => -(u mu)⁻¹ /
        (1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2))
      atTop (nhds 0) := by
    change Tendsto
      ((fun mu => -(u mu)⁻¹) /
        (fun mu => 1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2))
      atTop (nhds 0)
    simpa using huInv.neg.div hden (by norm_num)
  apply hquot.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))] with mu hmu
  have hu0 : u mu ≠ 0 := hmu.ne'
  have hbase : (lambda.re - mu) ^ 2 + lambda.im ^ 2 ≠ 0 := by
    have hdiff : lambda.re - mu ≠ 0 := by
      dsimp only [u] at hu0
      linarith
    nlinarith [sq_pos_of_ne_zero hdiff, sq_nonneg lambda.im]
  have hone : 1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2 ≠ 0 := by
    positivity
  rw [centeredResolventRealCoefficient, centeredResolventDenominator]
  change -(u mu)⁻¹ / (1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2) =
    (lambda.re - mu) / ((lambda.re - mu) ^ 2 + lambda.im ^ 2)
  field_simp [hu0, hbase, hone]
  simp only [u]
  ring

/-- The centered imaginary scalar resolvent coefficient vanishes as its real
center escapes to `+∞`. -/
theorem tendsto_centeredResolventImaginaryCoefficient_atTop (lambda : ℂ) :
    Tendsto (centeredResolventImaginaryCoefficient lambda) atTop (nhds 0) := by
  let u : ℝ → ℝ := fun mu => mu - lambda.re
  have hu : Tendsto u atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b + lambda.re)] with mu hmu
    dsimp only [u]
    linarith
  have huInv : Tendsto (fun mu => (u mu)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hu
  have hden : Tendsto
      (fun mu => 1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2)
      atTop (nhds 1) := by
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.mul (huInv.pow 2)) using 1
    all_goals ring
  have hquot : Tendsto
      (fun mu => (-lambda.im * (u mu)⁻¹ ^ 2) /
        (1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2))
      atTop (nhds 0) := by
    have hnum : Tendsto (fun mu => -lambda.im * (u mu)⁻¹ ^ 2)
        atTop (nhds 0) := by
      convert tendsto_const_nhds.mul (huInv.pow 2) using 1
      all_goals ring
    change Tendsto
      ((fun mu => -lambda.im * (u mu)⁻¹ ^ 2) /
        (fun mu => 1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2))
      atTop (nhds 0)
    simpa using hnum.div hden (by norm_num)
  apply hquot.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))] with mu hmu
  have hu0 : u mu ≠ 0 := hmu.ne'
  have hbase : (lambda.re - mu) ^ 2 + lambda.im ^ 2 ≠ 0 := by
    have hdiff : lambda.re - mu ≠ 0 := by
      dsimp only [u] at hu0
      linarith
    nlinarith [sq_pos_of_ne_zero hdiff, sq_nonneg lambda.im]
  have hone : 1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2 ≠ 0 := by
    positivity
  rw [centeredResolventImaginaryCoefficient, centeredResolventDenominator]
  change (-lambda.im * (u mu)⁻¹ ^ 2) /
      (1 + lambda.im ^ 2 * (u mu)⁻¹ ^ 2) =
    -lambda.im / ((lambda.re - mu) ^ 2 + lambda.im ^ 2)
  field_simp [hu0, hbase, hone]
  simp only [u]
  ring

/-- The complete scalar coefficient sum vanishes at infinite center. -/
theorem tendsto_centeredResolventCoefficientSum_atTop (lambda : ℂ) :
    Tendsto (centeredResolventCoefficientSum lambda) atTop (nhds 0) := by
  change Tendsto (fun mu =>
    |centeredResolventRealCoefficient lambda mu| +
      |centeredResolventImaginaryCoefficient lambda mu|) atTop (nhds 0)
  simpa only [abs_zero, zero_add] using
    (tendsto_centeredResolventRealCoefficient_atTop lambda).abs.add
      (tendsto_centeredResolventImaginaryCoefficient_atTop lambda).abs

/-- The explicit complete-block quantitative bound vanishes at infinite
center for every fixed nonreal spectral parameter. -/
theorem tendsto_cameraCauchyQuantitativeBound_atTop (lambda : ℂ) :
    Tendsto (cameraCauchyQuantitativeBound lambda) atTop (nhds 0) := by
  change Tendsto (fun mu => centeredResolventCoefficientSum lambda mu *
    (1 + 2 * |lambda.im|⁻¹)) atTop (nhds 0)
  simpa only [zero_mul] using
    (tendsto_centeredResolventCoefficientSum_atTop lambda).mul_const
      (1 + 2 * |lambda.im|⁻¹)

/-- An explicit sequence of supported camera labels whose slopes tend to
infinity. -/
def escapingCamera (n : ℕ) : CameraIndex :=
  ⟨n + 3, by omega⟩

@[simp] theorem escapingCamera_label (n : ℕ) :
    cameraLabel (escapingCamera n) = n + 3 := rfl

@[simp] theorem escapingCamera_slope (n : ℕ) :
    cameraSlope (cameraLabel (escapingCamera n)) = n + 3 := by
  rw [escapingCamera_label, cameraSlope_of_ne_two]
  omega

/-- The logarithmic centers of the escaping camera sequence tend to
infinity. -/
theorem tendsto_escapingCamera_logSlope :
    Tendsto
      (fun n => Real.log
        (cameraSlope (cameraLabel (escapingCamera n)) : ℝ))
      atTop atTop := by
  simp only [escapingCamera_slope]
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3))

/-- Along the explicit escaping-camera sequence, the complete quantitative
bound tends to zero. -/
theorem tendsto_cameraCauchyQuantitativeBound_escapingCamera (lambda : ℂ) :
    Tendsto
      (fun n => cameraCauchyQuantitativeBound lambda
        (Real.log
          (cameraSlope (cameraLabel (escapingCamera n)) : ℝ)))
      atTop (nhds 0) :=
  (tendsto_cameraCauchyQuantitativeBound_atTop lambda).comp
    tendsto_escapingCamera_logSlope

/-! ## The quantitative unit sequence -/

/-- Every canonical camera vector is nonzero. -/
theorem cameraVector_ne_zero (camera : CameraIndex) :
    cameraVector camera ≠ 0 := by
  intro hcamera
  have hsingle : Finsupp.single camera (1 : ℝ) = 0 := by
    apply cameraEmbedding.injective
    simpa only [cameraVector, map_zero] using hcamera
  have hvalue := DFunLike.congr_fun hsingle camera
  have hone : (1 : ℝ) = 0 := by
    simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hvalue
  exact one_ne_zero hone

/-- The normalized realified vector supported on one canonical camera. -/
def normalizedRealifiedCameraVector (camera : CameraIndex) :
    RealifiedCameraComplexification :=
  ‖cameraVector camera‖⁻¹ • realifiedCameraEmbedding (cameraVector camera)

/-- Every normalized realified camera vector has norm one. -/
@[simp] theorem norm_normalizedRealifiedCameraVector (camera : CameraIndex) :
    ‖normalizedRealifiedCameraVector camera‖ = 1 := by
  have hnorm : ‖cameraVector camera‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (cameraVector_ne_zero camera)
  rw [normalizedRealifiedCameraVector, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg _), norm_realifiedCameraEmbedding,
    inv_mul_cancel₀ hnorm]

/-- After camera normalization, the complete Cauchy image is bounded directly
by the explicit scalar quantitative bound. -/
theorem norm_allBasesCauchyBlock_normalizedRealifiedCameraVector_le
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (camera : CameraIndex) :
    ‖allBasesCauchyBlock lambda hlambda
        (normalizedRealifiedCameraVector camera)‖ ≤
      cameraCauchyQuantitativeBound lambda
        (Real.log (cameraSlope (cameraLabel camera) : ℝ)) := by
  have hnorm : ‖cameraVector camera‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (cameraVector_ne_zero camera)
  rw [normalizedRealifiedCameraVector, map_smul, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖cameraVector camera‖⁻¹ *
        ‖allBasesCauchyBlock lambda hlambda
          (realifiedCameraEmbedding (cameraVector camera))‖ ≤
      ‖cameraVector camera‖⁻¹ *
        (cameraCauchyQuantitativeBound lambda
            (Real.log (cameraSlope (cameraLabel camera) : ℝ)) *
          ‖cameraVector camera‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_allBasesCauchyBlock_realifiedCameraEmbedding_le
          lambda hlambda camera) (inv_nonneg.mpr (norm_nonneg _))
    _ = cameraCauchyQuantitativeBound lambda
        (Real.log (cameraSlope (cameraLabel camera) : ℝ)) := by
      field_simp

/-- The explicit unit-vector sequence escaping through camera labels
`3, 4, 5, ...`. -/
def quantitativeCameraSequence (n : ℕ) :
    RealifiedCameraComplexification :=
  normalizedRealifiedCameraVector (escapingCamera n)

/-- Every vector in the quantitative camera sequence is a unit vector. -/
@[simp] theorem norm_quantitativeCameraSequence (n : ℕ) :
    ‖quantitativeCameraSequence n‖ = 1 := by
  exact norm_normalizedRealifiedCameraVector (escapingCamera n)

/-- Pointwise quantitative estimate for the explicit unit sequence. -/
theorem norm_allBasesCauchyBlock_quantitativeCameraSequence_le
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (n : ℕ) :
    ‖allBasesCauchyBlock lambda hlambda (quantitativeCameraSequence n)‖ ≤
      cameraCauchyQuantitativeBound lambda
        (Real.log
          (cameraSlope (cameraLabel (escapingCamera n)) : ℝ)) :=
  norm_allBasesCauchyBlock_normalizedRealifiedCameraVector_le
    lambda hlambda (escapingCamera n)

/-- The complete Cauchy block sends the explicit sequence of unit camera
vectors to zero in norm. -/
theorem tendsto_norm_allBasesCauchyBlock_quantitativeCameraSequence
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Tendsto
      (fun n => ‖allBasesCauchyBlock lambda hlambda
        (quantitativeCameraSequence n)‖)
      atTop (nhds 0) := by
  exact squeeze_zero
    (fun _ => norm_nonneg _)
    (norm_allBasesCauchyBlock_quantitativeCameraSequence_le lambda hlambda)
    (tendsto_cameraCauchyQuantitativeBound_escapingCamera lambda)

/-- Vector-valued form of the same small-image sequence. -/
theorem tendsto_allBasesCauchyBlock_quantitativeCameraSequence
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    Tendsto
      (fun n => allBasesCauchyBlock lambda hlambda
        (quantitativeCameraSequence n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact tendsto_norm_allBasesCauchyBlock_quantitativeCameraSequence
    lambda hlambda

/-! ## Failure of bounded invertibility -/

/-- The complete Cauchy block is not bounded below by any positive constant:
the explicit unit sequence has images converging to zero. -/
theorem allBasesCauchyBlock_not_boundedBelow (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ z : RealifiedCameraComplexification,
        c * ‖z‖ ≤ ‖allBasesCauchyBlock lambda hlambda z‖ := by
  rintro ⟨c, hc, hbound⟩
  have hevent : ∀ᶠ n in atTop,
      ‖allBasesCauchyBlock lambda hlambda
        (quantitativeCameraSequence n)‖ < c :=
    (tendsto_order.1
      (tendsto_norm_allBasesCauchyBlock_quantitativeCameraSequence
        lambda hlambda)).2 c hc
  rcases hevent.exists with ⟨n, hn⟩
  have hlower := hbound (quantitativeCameraSequence n)
  rw [norm_quantitativeCameraSequence, mul_one] at hlower
  exact (not_lt_of_ge hlower) hn

/-- The densely defined Weyl inverse admits no global norm bound on its
domain.  This is the precise unboundedness statement for the `LinearPMap`
constructed in `WeylInverse.lean`. -/
theorem allBasesWeylInverse_not_normBounded (lambda : ℂ)
    (hlambda : lambda.im ≠ 0) :
    ¬ ∃ C : ℝ,
      ∀ z : (allBasesWeylInverse lambda hlambda).domain,
        ‖allBasesWeylInverse lambda hlambda z‖ ≤ C * ‖z‖ := by
  rintro ⟨C, hbound⟩
  let rangeSequence : ℕ →
      (allBasesWeylInverse lambda hlambda).domain :=
    fun n => allBasesCauchyRangeElement lambda hlambda
      (quantitativeCameraSequence n)
  have hrangeNorm : Tendsto (fun n => ‖rangeSequence n‖)
      atTop (nhds 0) := by
    change Tendsto
      (fun n => ‖allBasesCauchyBlock lambda hlambda
        (quantitativeCameraSequence n)‖) atTop (nhds 0)
    exact tendsto_norm_allBasesCauchyBlock_quantitativeCameraSequence
      lambda hlambda
  have hscaled : Tendsto (fun n => C * ‖rangeSequence n‖)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrangeNorm
  have hevent : ∀ᶠ n in atTop, C * ‖rangeSequence n‖ < 1 :=
    (tendsto_order.1 hscaled).2 1 zero_lt_one
  rcases hevent.exists with ⟨n, hn⟩
  have hinverseBound := hbound (rangeSequence n)
  change
    ‖allBasesWeylInverse lambda hlambda
        (allBasesCauchyRangeElement lambda hlambda
          (quantitativeCameraSequence n))‖ ≤
      C * ‖rangeSequence n‖ at hinverseBound
  rw [allBasesWeylInverse_apply_cauchyRangeElement,
    norm_quantitativeCameraSequence] at hinverseBound
  exact (not_lt_of_ge hinverseBound) hn

end NativeCarrySpectralWeyl.Infinite
