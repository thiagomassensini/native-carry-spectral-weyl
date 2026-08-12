import NativeCarrySpectralWeyl.Boundary.GreenCameraCoupling

/-!
# Angular evaluation of the Green-to-camera coupling

This file evaluates the external Green-to-camera interface along a supplied
state-valued angular family.  The angular parameter `t : ℝ` belongs only to
that family.  The nonreal parameters `lambda` and `z0` belong only to the
gamma/Cauchy/Weyl probes.

For every `t` and every nonreal spectral probe, coherent external synthesis
recovers the supplied camera readout, the gamma vector solves the exact defect
equation, and the closed partial Weyl inverse sends its induced Cauchy trace
back to the same angular readout.  Comparing two arbitrary probes therefore
proves probe independence of the recovered output without identifying either
probe with `t`.

The angular family and the bounded state readout remain explicit data.  No
unitary-orbit law, rigged-state realization, or research-specific boundedness
result is inferred here.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace NativeCarrySpectralWeyl.Boundary

open NativeCarrySpectralWeyl.Infinite
open GreenFrame.Concrete

variable {H E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- A Green-camera coupling together with a supplied state-valued angular
family.  The field `stateOrbit` is intentionally only a function of `t`; no
group law or continuity is silently postulated. -/
structure AngularGreenCameraCoupling
    (T : H →L[ℂ] HilbertSum E B)
    extends GreenCameraCoupling T where
  stateOrbit : ℝ → H

namespace AngularGreenCameraCoupling

variable {T : H →L[ℂ] HilbertSum E B}

/-- The Green state at angular parameter `t`. -/
def angularState (system : AngularGreenCameraCoupling T) (t : ℝ) : H :=
  system.stateOrbit t

/-- The camera value obtained by applying the fixed bounded state readout to
the angular state. -/
def angularReadout (system : AngularGreenCameraCoupling T) (t : ℝ) :
    RealifiedCameraComplexification :=
  system.stateReadout (system.angularState t)

/-- Coherent normalized external data associated with the angular state. -/
def angularExternalData (system : AngularGreenCameraCoupling T) (t : ℝ) : E :=
  normalizedExternal T (system.angularState t)

/-- The independent normalized bulk component along the angular family. -/
def angularBulk (system : AngularGreenCameraCoupling T) (t : ℝ) : B :=
  normalizedBulk T (system.angularState t)

/-- Coherent external synthesis recovers the angular camera readout exactly. -/
@[simp] theorem externalPort_angularExternalData
    (system : AngularGreenCameraCoupling T) (t : ℝ) :
    system.externalPort (system.angularExternalData t) =
      system.angularReadout t := by
  exact system.toGreenCameraCoupling.externalPort_normalizedExternal
    (system.angularState t)

/-- The static Poisson component recovers the normalized angular bulk and
remains separate from the spectral gamma/Weyl family. -/
@[simp] theorem staticPoisson_angularExternalData
    (system : AngularGreenCameraCoupling T) (t : ℝ) :
    system.staticPoisson (system.angularExternalData t) =
      system.angularBulk t := by
  exact system.toGreenCameraCoupling.staticPoisson_normalizedExternal
    (system.angularState t)

/-- Joint coherent evaluation recovers camera readout and bulk at the same
angular parameter. -/
@[simp] theorem externalOutput_angularExternalData
    (system : AngularGreenCameraCoupling T) (t : ℝ) :
    system.externalOutput (system.angularExternalData t) =
      (system.angularReadout t, system.angularBulk t) := by
  exact system.toGreenCameraCoupling.externalOutput_normalizedExternal
    (system.angularState t)

/-- Spectral gamma probe of the coherent angular external datum.  The
arguments `t` and `lambda` have distinct types and roles. -/
def angularGammaSource (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedNaimarkComplexification :=
  system.externalGammaSource lambda hlambda
    (system.angularExternalData t)

/-- Angular gamma evaluation is the source gamma map applied to the fixed
angular readout. -/
@[simp] theorem angularGammaSource_eq_carryGammaSource
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    system.angularGammaSource t lambda hlambda =
      carryGammaSource lambda hlambda (system.angularReadout t) := by
  exact system.toGreenCameraCoupling.externalGammaSource_normalizedExternal
    lambda hlambda (system.angularState t)

/-- The injective gamma probe vanishes exactly when the angular camera
readout vanishes. -/
theorem angularGammaSource_eq_zero_iff
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    system.angularGammaSource t lambda hlambda = 0 ↔
      system.angularReadout t = 0 := by
  rw [angularGammaSource_eq_carryGammaSource]
  constructor
  · intro hzero
    apply carryGammaSource_injective lambda hlambda
    simpa using hzero
  · intro hzero
    simp [hzero]

/-- Maximal-domain representative of the angular gamma vector. -/
def angularGammaIntoDomain (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedLogarithmicDomain :=
  system.externalGammaIntoDomain lambda hlambda
    (system.angularExternalData t)

/-- The angular gamma vector satisfies the exact realified source defect
equation on the maximal logarithmic domain. -/
theorem angularGammaSource_defect_equation
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    realifiedNaimarkScalar lambda
        (system.angularGammaSource t lambda hlambda) =
      realifiedLogarithmicMultiplication
          (system.angularGammaIntoDomain t lambda hlambda) +
        realifiedNaimarkPort (system.angularReadout t) := by
  simpa only [angularGammaSource, angularGammaIntoDomain,
    externalPort_angularExternalData] using
      system.toGreenCameraCoupling.externalGammaSource_defect_equation
        lambda hlambda (system.angularExternalData t)

/-- The angular maximal-domain representative is the unique solution of its
source defect equation. -/
theorem angularGammaIntoDomain_unique
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (f : RealifiedLogarithmicDomain)
    (hdefect :
      realifiedNaimarkScalar lambda
          (realifiedLogarithmicDomainEmbedding f) =
        realifiedLogarithmicMultiplication f +
          realifiedNaimarkPort (system.angularReadout t)) :
    f = system.angularGammaIntoDomain t lambda hlambda := by
  apply system.toGreenCameraCoupling.externalGammaIntoDomain_unique
    lambda hlambda (system.angularExternalData t) f
  simpa only [externalPort_angularExternalData] using hdefect

/-- Cauchy trace of the coherent angular datum, carrying membership in the
exact dense domain of the closed Weyl inverse in its type. -/
def angularCauchyTrace (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    (carryBoundaryWeylFamily lambda hlambda).domain :=
  system.externalCauchyTrace lambda hlambda
    (system.angularExternalData t)

/-- The underlying angular Cauchy trace is the complete all-bases Cauchy
block applied to the angular readout. -/
@[simp] theorem coe_angularCauchyTrace
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    (system.angularCauchyTrace t lambda hlambda :
      RealifiedCameraComplexification) =
      allBasesCauchyBlock lambda hlambda (system.angularReadout t) := by
  change allBasesCauchyBlock lambda hlambda
      (system.externalPort (system.angularExternalData t)) =
    allBasesCauchyBlock lambda hlambda (system.angularReadout t)
  rw [externalPort_angularExternalData]

/-- Trace-parametrized gamma evaluation agrees with direct source
parametrization of the angular readout. -/
theorem carryGammaField_angularCauchyTrace
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    carryGammaField lambda hlambda
        (system.angularCauchyTrace t lambda hlambda) =
      system.angularGammaSource t lambda hlambda := by
  exact system.toGreenCameraCoupling.carryGammaField_externalCauchyTrace
    lambda hlambda (system.angularExternalData t)

/-- Weyl evaluation of the angular Cauchy trace. -/
def angularWeylOutput (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    RealifiedCameraComplexification :=
  carryBoundaryWeylFamily lambda hlambda
    (system.angularCauchyTrace t lambda hlambda)

/-- Angular evaluation theorem: for every angular time and every independent
nonreal spectral parameter, the closed Weyl inverse recovers the same fixed
camera readout. -/
@[simp] theorem angularWeylOutput_eq_readout
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    system.angularWeylOutput t lambda hlambda =
      system.angularReadout t := by
  simpa only [angularWeylOutput, angularCauchyTrace,
    externalPort_angularExternalData] using
    system.toGreenCameraCoupling.carryBoundaryWeylFamily_externalCauchyTrace
      lambda hlambda (system.angularExternalData t)

/-- Weyl visibility at an arbitrary nonreal probe vanishes exactly at a zero
of the angular camera readout. -/
@[simp] theorem angularWeylOutput_eq_zero_iff
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    system.angularWeylOutput t lambda hlambda = 0 ↔
      system.angularReadout t = 0 := by
  rw [angularWeylOutput_eq_readout]

/-- Boundary values of the angular gamma state: its first value is the
induced Cauchy trace, while its second value is both the Weyl output and the
original angular readout. -/
theorem angularGammaSource_boundary_values
    (system : AngularGreenCameraCoupling T)
    (t : ℝ) (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    (realifiedNaimarkAdjoint
        (system.angularGammaSource t lambda hlambda),
      system.angularReadout t) =
    ((system.angularCauchyTrace t lambda hlambda :
        RealifiedCameraComplexification),
      system.angularWeylOutput t lambda hlambda) := by
  simpa only [angularGammaSource, angularCauchyTrace, angularWeylOutput,
    externalPort_angularExternalData] using
      system.toGreenCameraCoupling.externalGammaSource_boundary_values
        lambda hlambda (system.angularExternalData t)

/-- Explicit probe independence.  The auxiliary anchor `z0` and the Weyl
parameter `lambda` may be any two nonreal complex numbers; after each probe's
own Cauchy trace is evaluated by its own Weyl family, both recover the same
angular readout at `t`.  No equality among `t`, `z0`, and `lambda` is used. -/
theorem angularWeylOutput_probe_independent
    (system : AngularGreenCameraCoupling T) (t : ℝ)
    (z0 lambda : ℂ) (hz0 : z0.im ≠ 0) (hlambda : lambda.im ≠ 0) :
    system.angularWeylOutput t z0 hz0 =
      system.angularWeylOutput t lambda hlambda := by
  rw [angularWeylOutput_eq_readout, angularWeylOutput_eq_readout]

/-- Probe-independent zero test written with two arbitrary spectral
parameters. -/
theorem angularWeylOutput_zero_probe_independent
    (system : AngularGreenCameraCoupling T) (t : ℝ)
    (z0 lambda : ℂ) (hz0 : z0.im ≠ 0) (hlambda : lambda.im ≠ 0) :
    system.angularWeylOutput t z0 hz0 = 0 ↔
      system.angularWeylOutput t lambda hlambda = 0 := by
  rw [angularWeylOutput_eq_zero_iff, angularWeylOutput_eq_zero_iff]

end AngularGreenCameraCoupling

end NativeCarrySpectralWeyl.Boundary
