import GreenFrame.Concrete.Analysis.AmbientPoisson
import GreenFrame.Concrete.Analysis.ConcreteSplitBounds
import NativeCarrySpectralWeyl.Boundary.GammaField

/-!
# External Green-to-camera coupling

This file connects the normalized external sector of a complex Green frame to
the realified all-bases camera boundary space.  The connection is deliberately
stated through one explicit analytic datum:

`stateReadout : H ->L[Real] RealifiedCameraComplexification`.

The present theory does not manufacture this bounded readout from the static
Green frame.  Once it is supplied, however, the lower frame bound gives the
canonical ambient external synthesis.  Composing the readout with that
synthesis produces an external camera port.  On coherent external data this
port recovers the original state readout exactly, while the independent static
Poisson component recovers the normalized Green bulk.

The second half transports the external camera port through the already
constructed source gamma field.  Every external datum produces the unique
maximal-domain defect solution, its Cauchy trace lies in the exact dense domain
of the Weyl inverse, and the boundary law recovers the original camera source.

The static Poisson operator and the spectral gamma/Weyl family remain distinct
components throughout.  In particular, no equality between them and no
canonical Green-to-camera readout is inferred.
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

/-- Explicit analytic interface between a normalized complex Green split and
the realified all-bases camera space.  The split bounds are proof data; the
bounded state readout is the only new mathematical hypothesis. -/
structure GreenCameraCoupling
    (T : H →L[ℂ] HilbertSum E B) where
  bounds : SplitComplexFrameBounds T
  stateReadout : H →L[ℝ] RealifiedCameraComplexification

namespace GreenCameraCoupling

variable {T : H →L[ℂ] HilbertSum E B}

/-- The camera port on arbitrary external Green data, obtained by first using
the canonical ambient synthesis and then applying the supplied state readout. -/
def externalPort (coupling : GreenCameraCoupling T) :
    E →L[ℝ] RealifiedCameraComplexification :=
  coupling.stateReadout ∘L
    (ambientExternalSynthesis T).restrictScalars ℝ

@[simp] theorem externalPort_apply (coupling : GreenCameraCoupling T)
    (e : E) :
    coupling.externalPort e =
      coupling.stateReadout (ambientExternalSynthesis T e) :=
  rfl

/-- On a coherent external coefficient vector, the induced camera port is
exactly the original state readout. -/
@[simp] theorem externalPort_normalizedExternal
    (coupling : GreenCameraCoupling T) (x : H) :
    coupling.externalPort (normalizedExternal T x) =
      coupling.stateReadout x := by
  change coupling.stateReadout
      ((ambientExternalSynthesis T ∘L normalizedExternal T) x) =
    coupling.stateReadout x
  rw [ambientExternalSynthesis_comp_external coupling.bounds]
  rfl

/-- Operator-level form of coherent external reconstruction. -/
theorem externalPort_comp_normalizedExternal
    (coupling : GreenCameraCoupling T) :
    coupling.externalPort ∘L
        (normalizedExternal T).restrictScalars ℝ =
      coupling.stateReadout := by
  ext x
  exact externalPort_normalizedExternal coupling x

/-- The static Green Poisson component, viewed on the underlying real Hilbert
spaces.  This is separate from the spectral gamma field below. -/
def staticPoisson (_coupling : GreenCameraCoupling T) : E →L[ℝ] B :=
  (ambientPoisson T).restrictScalars ℝ

@[simp] theorem staticPoisson_apply (coupling : GreenCameraCoupling T)
    (e : E) :
    coupling.staticPoisson e = ambientPoisson T e :=
  rfl

/-- The realified static Poisson component retains the exact Green
intertwining law. -/
@[simp] theorem staticPoisson_normalizedExternal
    (coupling : GreenCameraCoupling T) (x : H) :
    coupling.staticPoisson (normalizedExternal T x) =
      normalizedBulk T x := by
  change (ambientPoisson T ∘L normalizedExternal T) x = normalizedBulk T x
  rw [ambientPoisson_intertwining coupling.bounds]

/-- Operator-level form of the static Green Poisson intertwining after
restriction from complex to real scalars. -/
theorem staticPoisson_comp_normalizedExternal
    (coupling : GreenCameraCoupling T) :
    coupling.staticPoisson ∘L
        (normalizedExternal T).restrictScalars ℝ =
      (normalizedBulk T).restrictScalars ℝ := by
  ext x
  exact staticPoisson_normalizedExternal coupling x

/-- Joint camera/bulk output associated with one external Green datum. -/
def externalOutput (coupling : GreenCameraCoupling T) :
    E →L[ℝ] (RealifiedCameraComplexification × B) :=
  coupling.externalPort.prod coupling.staticPoisson

@[simp] theorem externalOutput_apply (coupling : GreenCameraCoupling T)
    (e : E) :
    coupling.externalOutput e =
      (coupling.externalPort e, coupling.staticPoisson e) :=
  rfl

/-- Coherent external data simultaneously recover the camera readout and the
normalized Green bulk. -/
@[simp] theorem externalOutput_normalizedExternal
    (coupling : GreenCameraCoupling T) (x : H) :
    coupling.externalOutput (normalizedExternal T x) =
      (coupling.stateReadout x, normalizedBulk T x) := by
  apply Prod.ext
  · exact externalPort_normalizedExternal coupling x
  · exact staticPoisson_normalizedExternal coupling x

/-- The joint output intertwining as an equality of bounded real-linear
maps. -/
theorem externalOutput_comp_normalizedExternal
    (coupling : GreenCameraCoupling T) :
    coupling.externalOutput ∘L
        (normalizedExternal T).restrictScalars ℝ =
      coupling.stateReadout.prod
        ((normalizedBulk T).restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro x
  exact externalOutput_normalizedExternal coupling x

/-! ## Spectral transport of the external camera port -/

/-- Source-parametrized carry gamma map pulled back to the external Green
space through the explicit camera port. -/
def externalGammaSource (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    E →L[ℝ] RealifiedNaimarkComplexification :=
  carryGammaSource lambda hlambda ∘L coupling.externalPort

@[simp] theorem externalGammaSource_apply
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    coupling.externalGammaSource lambda hlambda e =
      carryGammaSource lambda hlambda (coupling.externalPort e) :=
  rfl

/-- On coherent external data, spectral transport is gamma applied directly
to the state readout. -/
@[simp] theorem externalGammaSource_normalizedExternal
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (x : H) :
    coupling.externalGammaSource lambda hlambda
        (normalizedExternal T x) =
      carryGammaSource lambda hlambda (coupling.stateReadout x) := by
  rw [externalGammaSource_apply,
    externalPort_normalizedExternal]

/-- Operator-level coherent-state gamma transport. -/
theorem externalGammaSource_comp_normalizedExternal
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    coupling.externalGammaSource lambda hlambda ∘L
        (normalizedExternal T).restrictScalars ℝ =
      carryGammaSource lambda hlambda ∘L coupling.stateReadout := by
  ext x
  exact externalGammaSource_normalizedExternal coupling lambda hlambda x

/-- Domain-valued form of the pulled-back gamma map. -/
def externalGammaIntoDomain (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    E →ₗ[ℝ] RealifiedLogarithmicDomain :=
  (carryGammaIntoDomain lambda hlambda).comp
    coupling.externalPort.toLinearMap

/-- Defect-state pair generated from arbitrary external Green data. -/
def externalDefectState (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    E →ₗ[ℝ]
      (RealifiedNaimarkComplexification ×
        RealifiedNaimarkComplexification) :=
  (carryDefectStateFromSource lambda hlambda).comp
    coupling.externalPort.toLinearMap

@[simp] theorem externalDefectState_apply
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    coupling.externalDefectState lambda hlambda e =
      (coupling.externalGammaSource lambda hlambda e,
        realifiedNaimarkScalar lambda
          (coupling.externalGammaSource lambda hlambda e)) :=
  rfl

/-- Every pulled-back external defect state belongs to the canonical carry
defect subspace. -/
theorem externalDefectState_mem_carryDefectSpace
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    coupling.externalDefectState lambda hlambda e ∈
      carryDefectSpace lambda hlambda := by
  change carryDefectStateFromSource lambda hlambda
      (coupling.externalPort e) ∈
    LinearMap.range (carryDefectStateFromSource lambda hlambda)
  exact LinearMap.mem_range_self _ _

/-- Spectral gamma transport loses exactly the information already lost by
the external camera port, and no more. -/
theorem externalGammaSource_eq_iff_externalPort_eq
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e₁ e₂ : E) :
    coupling.externalGammaSource lambda hlambda e₁ =
        coupling.externalGammaSource lambda hlambda e₂ ↔
      coupling.externalPort e₁ = coupling.externalPort e₂ := by
  constructor
  · intro h
    apply carryGammaSource_injective lambda hlambda
    simpa only [externalGammaSource_apply] using h
  · intro h
    simpa only [externalGammaSource_apply] using
      congrArg (carryGammaSource lambda hlambda) h

/-- Every externally generated gamma vector satisfies the exact realified
source defect equation on the maximal logarithmic domain. -/
theorem externalGammaSource_defect_equation
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    realifiedNaimarkScalar lambda
        (coupling.externalGammaSource lambda hlambda e) =
      realifiedLogarithmicMultiplication
          (coupling.externalGammaIntoDomain lambda hlambda e) +
        realifiedNaimarkPort (coupling.externalPort e) := by
  exact carryGammaSource_defect_equation lambda hlambda
    (coupling.externalPort e)

/-- The externally generated vector is the unique maximal-domain solution of
its defect equation. -/
theorem externalGammaIntoDomain_unique
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E)
    (f : RealifiedLogarithmicDomain)
    (hdefect :
      realifiedNaimarkScalar lambda
          (realifiedLogarithmicDomainEmbedding f) =
        realifiedLogarithmicMultiplication f +
          realifiedNaimarkPort (coupling.externalPort e)) :
    f = coupling.externalGammaIntoDomain lambda hlambda e := by
  exact carryGammaIntoDomain_unique lambda hlambda
    (coupling.externalPort e) f hdefect

/-- The Cauchy trace generated by an external Green datum, with membership in
the exact Weyl domain carried in its type. -/
def externalCauchyTrace (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    (carryBoundaryWeylFamily lambda hlambda).domain :=
  allBasesCauchyRangeElement lambda hlambda (coupling.externalPort e)

@[simp] theorem coe_externalCauchyTrace
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    (coupling.externalCauchyTrace lambda hlambda e :
      RealifiedCameraComplexification) =
      allBasesCauchyBlock lambda hlambda (coupling.externalPort e) :=
  rfl

/-- Pullback through the trace-parametrized gamma field gives the same defect
vector as direct source parametrization. -/
theorem carryGammaField_externalCauchyTrace
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    carryGammaField lambda hlambda
        (coupling.externalCauchyTrace lambda hlambda e) =
      coupling.externalGammaSource lambda hlambda e := by
  exact carryGammaField_apply_cauchyRangeElement lambda hlambda
    (coupling.externalPort e)

/-- Exact external Green-to-Weyl transport law: the closed partial Weyl
inverse sends the induced Cauchy trace back to the explicit camera port. -/
@[simp] theorem carryBoundaryWeylFamily_externalCauchyTrace
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    carryBoundaryWeylFamily lambda hlambda
        (coupling.externalCauchyTrace lambda hlambda e) =
      coupling.externalPort e := by
  exact allBasesWeylInverse_apply_cauchyRangeElement lambda hlambda
    (coupling.externalPort e)

/-- Boundary values of the external gamma state.  The first value is its
Cauchy trace and the second is both the Weyl value and the original camera
source. -/
theorem externalGammaSource_boundary_values
    (coupling : GreenCameraCoupling T)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) (e : E) :
    (realifiedNaimarkAdjoint
        (coupling.externalGammaSource lambda hlambda e),
      coupling.externalPort e) =
    ((coupling.externalCauchyTrace lambda hlambda e :
        RealifiedCameraComplexification),
      carryBoundaryWeylFamily lambda hlambda
        (coupling.externalCauchyTrace lambda hlambda e)) := by
  apply Prod.ext
  · change carryDefectGammaZero lambda hlambda
        (coupling.externalPort e) =
      allBasesCauchyBlock lambda hlambda (coupling.externalPort e)
    exact carryDefectGammaZero_apply lambda hlambda
      (coupling.externalPort e)
  · exact (coupling.carryBoundaryWeylFamily_externalCauchyTrace
      lambda hlambda e).symm

end GreenCameraCoupling

/-! ## Concrete Green-frame specialization -/

/-- Canonical coupling package for the concrete Green analysis operator.  A
bounded state readout remains the explicit input; the exact split bounds are
filled by the theorem already proved in `GreenFrame`. -/
def concreteGreenCameraCoupling
    (omega : GreenFrame.Concrete.AdmissibleInfinitePartition)
    (stateReadout : GreenFrame.Concrete.State →L[ℝ]
      RealifiedCameraComplexification) :
    GreenCameraCoupling
      (GreenFrame.Concrete.concreteAnalysisOperator omega) where
  bounds := GreenFrame.Concrete.concreteSplitFrameBounds omega
  stateReadout := stateReadout

namespace GreenCameraCoupling

@[simp] theorem concreteGreenCameraCoupling_stateReadout
    (omega : GreenFrame.Concrete.AdmissibleInfinitePartition)
    (stateReadout : GreenFrame.Concrete.State →L[ℝ]
      RealifiedCameraComplexification) :
    (concreteGreenCameraCoupling omega stateReadout).stateReadout =
      stateReadout :=
  rfl

/-- Concrete coherent-state camera-port law. -/
@[simp] theorem concreteGreenCamera_externalPort_normalizedExternal
    (omega : GreenFrame.Concrete.AdmissibleInfinitePartition)
    (stateReadout : GreenFrame.Concrete.State →L[ℝ]
      RealifiedCameraComplexification)
    (x : GreenFrame.Concrete.State) :
    (concreteGreenCameraCoupling omega stateReadout).externalPort
        (GreenFrame.Concrete.normalizedExternal
          (GreenFrame.Concrete.concreteAnalysisOperator omega) x) =
      stateReadout x := by
  exact GreenCameraCoupling.externalPort_normalizedExternal
    (concreteGreenCameraCoupling omega stateReadout) x

/-- Concrete coherent-state joint camera/bulk law. -/
@[simp] theorem concreteGreenCamera_externalOutput_normalizedExternal
    (omega : GreenFrame.Concrete.AdmissibleInfinitePartition)
    (stateReadout : GreenFrame.Concrete.State →L[ℝ]
      RealifiedCameraComplexification)
    (x : GreenFrame.Concrete.State) :
    (concreteGreenCameraCoupling omega stateReadout).externalOutput
        (GreenFrame.Concrete.normalizedExternal
          (GreenFrame.Concrete.concreteAnalysisOperator omega) x) =
      (stateReadout x,
        GreenFrame.Concrete.normalizedBulk
          (GreenFrame.Concrete.concreteAnalysisOperator omega) x) := by
  exact GreenCameraCoupling.externalOutput_normalizedExternal
    (concreteGreenCameraCoupling omega stateReadout) x

/-- Concrete coherent-state gamma transport law. -/
@[simp] theorem concreteGreenCamera_externalGammaSource_normalizedExternal
    (omega : GreenFrame.Concrete.AdmissibleInfinitePartition)
    (stateReadout : GreenFrame.Concrete.State →L[ℝ]
      RealifiedCameraComplexification)
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (x : GreenFrame.Concrete.State) :
    (concreteGreenCameraCoupling omega stateReadout).externalGammaSource
        lambda hlambda
        (GreenFrame.Concrete.normalizedExternal
          (GreenFrame.Concrete.concreteAnalysisOperator omega) x) =
      carryGammaSource lambda hlambda (stateReadout x) := by
  exact GreenCameraCoupling.externalGammaSource_normalizedExternal
    (concreteGreenCameraCoupling omega stateReadout) lambda hlambda x

end GreenCameraCoupling

end NativeCarrySpectralWeyl.Boundary
