import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Exact return-metric cancellation

This file formalizes the finite-dimensional algebra behind the return-metric
defect covariance from the Weyl notes.  An endpoint block `E`, a bulk block
`B`, and a Poisson return `P` satisfy

`P E = B`,  `Eᴴ E + Bᴴ B = I`.

For the return metric `G_E = I + Pᴴ P`, these identities imply the exact
isometry `Eᴴ G_E E = I`.  Consequently every source probe

`S = C R Eᴴ`

has intrinsic covariance

`S G_E Sᴴ = C R Rᴴ Cᴴ`.

No limit, spectral asymptotic, or numerical premise is used here.
-/

open scoped Matrix

namespace NativeCarrySpectralWeyl.Finite

noncomputable section

variable {spectral endpoint bulk output : Type*}
variable [Fintype spectral] [Fintype endpoint] [Fintype bulk]
variable [DecidableEq spectral] [DecidableEq endpoint]

/-- Endpoint metric induced by the Poisson return to the bulk. -/
def returnMetric (poisson : Matrix bulk endpoint ℂ) : Matrix endpoint endpoint ℂ :=
  1 + poissonᴴ * poisson

/-- Source-parametrized defect readout `S = C R Eᴴ`. -/
def sourceProbe (camera : Matrix output spectral ℂ)
    (resolvent : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ) : Matrix output endpoint ℂ :=
  camera * resolvent * endpointMapᴴ

/-- Covariance intrinsic to the dual endpoint return metric. -/
def returnMetricCovariance (camera : Matrix output spectral ℂ)
    (resolvent : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ) : Matrix output output ℂ :=
  sourceProbe camera resolvent endpointMap * returnMetric poisson *
    (sourceProbe camera resolvent endpointMap)ᴴ

/-- Direct weighted camera covariance after the endpoint/bulk cancellation. -/
def directResolventCovariance (camera : Matrix output spectral ℂ)
    (resolvent : Matrix spectral spectral ℂ) : Matrix output output ℂ :=
  camera * resolvent * resolventᴴ * cameraᴴ

omit [Fintype spectral] in
/-- Exact Pythagorean conservation in the endpoint return metric. -/
theorem endpointMap_conjTranspose_mul_returnMetric_mul_endpointMap
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    endpointMapᴴ * returnMetric poisson * endpointMap = 1 := by
  rw [returnMetric]
  calc
    endpointMapᴴ * (1 + poissonᴴ * poisson) * endpointMap =
        endpointMapᴴ * endpointMap +
          (poisson * endpointMap)ᴴ * (poisson * endpointMap) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap := by rw [hpoisson]
    _ = 1 := hisometry

/-- The return-metric covariance of a source probe reduces exactly to the
direct diagonal-resolvent camera covariance. -/
theorem returnMetricCovariance_eq_directResolventCovariance
    (camera : Matrix output spectral ℂ)
    (resolvent : Matrix spectral spectral ℂ)
    (endpointMap : Matrix endpoint spectral ℂ)
    (bulkMap : Matrix bulk spectral ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    returnMetricCovariance camera resolvent endpointMap poisson =
      directResolventCovariance camera resolvent := by
  have hmetric := endpointMap_conjTranspose_mul_returnMetric_mul_endpointMap
    endpointMap bulkMap poisson hpoisson hisometry
  have hprobeAdjoint :
      (sourceProbe camera resolvent endpointMap)ᴴ =
        endpointMap * resolventᴴ * cameraᴴ := by
    simp only [sourceProbe, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [returnMetricCovariance, directResolventCovariance, hprobeAdjoint]
  calc
    (camera * resolvent * endpointMapᴴ) * returnMetric poisson *
        (endpointMap * resolventᴴ * cameraᴴ) =
      camera * resolvent *
        (endpointMapᴴ * returnMetric poisson * endpointMap) *
          resolventᴴ * cameraᴴ := by
            simp only [Matrix.mul_assoc]
    _ = camera * resolvent * resolventᴴ * cameraᴴ := by rw [hmetric]; simp

end

end NativeCarrySpectralWeyl.Finite
