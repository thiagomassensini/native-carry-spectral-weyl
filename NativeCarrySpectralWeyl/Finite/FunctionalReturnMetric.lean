import NativeCarrySpectralWeyl.Finite.ReturnMetric

/-!
# Functional return-metric cancellation

This file inserts an arbitrary spectral observable in one leg of the finite
defect probe.  The endpoint return metric still cancels exactly, without a
commutation or polynomial hypothesis.  Constant observables recover the
order-zero identities from `ReturnMetric`.
-/

open scoped Matrix

namespace NativeCarrySpectralWeyl.Finite

noncomputable section

variable {spectral endpoint bulk output : Type*}
variable [Fintype spectral] [Fintype endpoint] [Fintype bulk]
variable [DecidableEq spectral] [DecidableEq endpoint]

omit [Fintype endpoint] [DecidableEq endpoint] in
@[simp] theorem functionalSourceProbe_one
    (camera : Matrix output spectral ℂ)
    (resolvent : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ) :
    functionalSourceProbe camera 1 resolvent endpointMap =
      sourceProbe camera resolvent endpointMap := by
  simp [functionalSourceProbe, sourceProbe]

@[simp] theorem functionalReturnMetricCrossCovariance_one
    (camera : Matrix output spectral ℂ)
    (resolvent : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ) :
    functionalReturnMetricCrossCovariance camera 1 resolvent endpointMap poisson =
      returnMetricCovariance camera resolvent endpointMap poisson := by
  simp [functionalReturnMetricCrossCovariance, returnMetricCovariance]

@[simp] theorem directFunctionalResolventCovariance_one
    (camera : Matrix output spectral ℂ)
    (resolvent : Matrix spectral spectral ℂ) :
    directFunctionalResolventCovariance camera 1 resolvent =
      directResolventCovariance camera resolvent := by
  simp [directFunctionalResolventCovariance, directResolventCovariance]

/-- The exact finite functional identity from the defect-probe notes.  It is
valid for every spectral observable; no commutation or polynomial hypothesis
is needed for the algebraic cancellation. -/
theorem functionalReturnMetricCrossCovariance_eq_direct
    (camera : Matrix output spectral ℂ)
    (observable resolvent : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    functionalReturnMetricCrossCovariance camera observable resolvent
        endpointMap poisson =
      directFunctionalResolventCovariance camera observable resolvent := by
  have hmetric := endpointMap_conjTranspose_mul_returnMetric_mul_endpointMap
    endpointMap bulkMap poisson hpoisson hisometry
  have hprobeAdjoint :
      (sourceProbe camera resolvent endpointMap)ᴴ =
        endpointMap * resolventᴴ * cameraᴴ := by
    simp only [sourceProbe, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [functionalReturnMetricCrossCovariance,
    directFunctionalResolventCovariance, hprobeAdjoint]
  calc
    (camera * observable * resolvent * endpointMapᴴ) * returnMetric poisson *
        (endpointMap * resolventᴴ * cameraᴴ) =
      camera * observable * resolvent *
        (endpointMapᴴ * returnMetric poisson * endpointMap) *
          resolventᴴ * cameraᴴ := by
            simp only [Matrix.mul_assoc]
    _ = camera * observable * resolvent * resolventᴴ * cameraᴴ := by
      rw [hmetric]
      simp

end

end NativeCarrySpectralWeyl.Finite
