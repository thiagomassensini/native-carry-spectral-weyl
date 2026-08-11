import NativeCarrySpectralWeyl.Limits.FiniteDefectCovariance
import NativeCarrySpectralWeyl.Finite.FunctionalReturnMetric
import NativeCarrySpectralWeyl.Limits.ResolventLogMean
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Exact finite functional defect covariance

This file formalizes the finite algebraic layer of the polynomial functional
limit notes.  A real spectral multiplier is inserted diagonally before the
finite resolvent.  Return-metric cancellation then identifies the resulting
functional cross covariance exactly with the complete literal coefficient
sum, including every finite seed and corrected even-camera endpoint.

The main specialization evaluates an arbitrary real polynomial at
`log(n+1) - μ_M(z)`, where `μ_M(z)` is the finite resolvent-weighted logarithmic
mean.  No asymptotic statement about `μ_M` is assumed here.
-/

open scoped BigOperators Matrix
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- Diagonal realization of a real multiplier on a finite spectral window. -/
def finiteRealDiagonalObservable (multiplier : ℕ → ℝ) (window : ℕ) :
    Matrix (Fin window) (Fin window) ℂ :=
  Matrix.diagonal fun n => (multiplier n.val : ℂ)

/-- Complete literal finite functional covariance for a scalar multiplier. -/
def finiteFunctionalCoefficientCovariance {index : Type*}
    (weight multiplier : ℕ → ℝ) (cutoff : ℕ) (camera : index → ℕ) :
    Matrix index index ℝ :=
  fun i j =>
    (∑ n ∈ Finset.range cutoff, weight n)⁻¹ *
      ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
        weight n * multiplier n * finiteCoefficientAt (camera i) cutoff n *
          finiteCoefficientAt (camera j) cutoff n

/-- Normalized direct functional covariance of the literal finite camera and
diagonal resolvent. -/
def normalizedFiniteFunctionalDirectCovariance
    {index : Type*} [Fintype index]
    (z : ℂ) (cutoff : ℕ) (camera : index → ℕ) (multiplier : ℕ → ℝ) :
    Matrix index index ℂ :=
  fun i j =>
    ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
      directFunctionalResolventCovariance
        (finiteCameraMatrix cutoff camera)
        (finiteRealDiagonalObservable multiplier
          (finiteFamilyWindow cutoff camera))
        (finiteResolventMatrix z (finiteFamilyWindow cutoff camera)) i j

/-- Exact equality between the normalized functional matrix product and the
complete literal finite coefficient formula. -/
theorem normalizedFiniteFunctionalDirectCovariance_eq_coefficients
    {index : Type*} [Fintype index] {camera : index → ℕ}
    (hcamera : ∀ i, 2 ≤ camera i) (z : ℂ) (cutoff : ℕ)
    (multiplier : ℕ → ℝ) :
    normalizedFiniteFunctionalDirectCovariance z cutoff camera multiplier =
      fun i j =>
        (finiteFunctionalCoefficientCovariance (resolventWeight z) multiplier
          cutoff camera i j : ℂ) := by
  ext i j
  rw [normalizedFiniteFunctionalDirectCovariance,
    directFunctionalResolventCovariance]
  calc
    ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
        (finiteCameraMatrix cutoff camera *
          finiteRealDiagonalObservable multiplier
            (finiteFamilyWindow cutoff camera) *
          finiteResolventMatrix z (finiteFamilyWindow cutoff camera) *
          (finiteResolventMatrix z (finiteFamilyWindow cutoff camera))ᴴ *
          (finiteCameraMatrix cutoff camera)ᴴ) i j =
      ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
        (finiteCameraMatrix cutoff camera *
          (finiteRealDiagonalObservable multiplier
              (finiteFamilyWindow cutoff camera) *
            (finiteResolventMatrix z (finiteFamilyWindow cutoff camera) *
              (finiteResolventMatrix z (finiteFamilyWindow cutoff camera))ᴴ)) *
          (finiteCameraMatrix cutoff camera)ᴴ) i j := by
            simp only [Matrix.mul_assoc]
    _ = ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
        (finiteCameraMatrix cutoff camera *
          (finiteRealDiagonalObservable multiplier
              (finiteFamilyWindow cutoff camera) *
            Matrix.diagonal (fun n : Fin (finiteFamilyWindow cutoff camera) =>
              (resolventWeight z n.val : ℂ))) *
          (finiteCameraMatrix cutoff camera)ᴴ) i j := by
            rw [finiteResolventMatrix_mul_conjTranspose]
    _ = ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
        (finiteCameraMatrix cutoff camera *
          Matrix.diagonal (fun n : Fin (finiteFamilyWindow cutoff camera) =>
            ((multiplier n.val * resolventWeight z n.val : ℝ) : ℂ)) *
          (finiteCameraMatrix cutoff camera)ᴴ) i j := by
            rw [finiteRealDiagonalObservable,
              Matrix.diagonal_mul_diagonal]
            norm_cast
    _ = _ := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
        finiteCameraMatrix, Complex.star_def, Complex.conj_ofReal]
      have hsum :
          (∑ n : Fin (finiteFamilyWindow cutoff camera),
              (finiteCoefficientAt (camera i) cutoff n.val : ℂ) *
                ((multiplier n.val * resolventWeight z n.val : ℝ) : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n.val : ℂ)) =
            ∑ n ∈ Finset.range
                (pairFiniteWindow (camera i) (camera j) cutoff),
              ((resolventWeight z n * multiplier n : ℝ) : ℂ) *
                (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n : ℂ) := by
        calc
          (∑ n : Fin (finiteFamilyWindow cutoff camera),
              (finiteCoefficientAt (camera i) cutoff n.val : ℂ) *
                ((multiplier n.val * resolventWeight z n.val : ℝ) : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n.val : ℂ)) =
            ∑ n ∈ Finset.range (finiteFamilyWindow cutoff camera),
              (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                ((multiplier n * resolventWeight z n : ℝ) : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n : ℂ) := by
                  simpa only using Fin.sum_univ_eq_sum_range
                    (fun n : ℕ =>
                      (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                        ((multiplier n * resolventWeight z n : ℝ) : ℂ) *
                        (finiteCoefficientAt (camera j) cutoff n : ℂ))
                    (finiteFamilyWindow cutoff camera)
          _ = ∑ n ∈ Finset.range (finiteFamilyWindow cutoff camera),
              ((resolventWeight z n * multiplier n : ℝ) : ℂ) *
                (finiteCoefficientAt (camera i) cutoff n : ℂ) *
                (finiteCoefficientAt (camera j) cutoff n : ℂ) := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  push_cast
                  ring
          _ = _ := sum_finiteFamilyWindow_eq_pairFiniteWindow hcamera cutoff
            (fun n => ((resolventWeight z n * multiplier n : ℝ) : ℂ)) i j
      rw [hsum]
      simp only [finiteFunctionalCoefficientCovariance, resolventMass]
      norm_cast

/-- Normalized return-metric cross covariance of a finite functional probe
against the unmodified source probe. -/
def normalizedFiniteFunctionalReturnMetricCrossCovariance
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    (z : ℂ) (cutoff : ℕ) (camera : index → ℕ) (multiplier : ℕ → ℝ)
    (endpointMap :
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : Matrix bulk endpoint ℂ) : Matrix index index ℂ :=
  fun i j =>
    ((resolventMass z cutoff : ℝ) : ℂ)⁻¹ *
      functionalReturnMetricCrossCovariance
        (finiteCameraMatrix cutoff camera)
        (finiteRealDiagonalObservable multiplier
          (finiteFamilyWindow cutoff camera))
        (finiteResolventMatrix z (finiteFamilyWindow cutoff camera))
        endpointMap poisson i j

/-- Exact finite functional defect-probe identity for every real spectral
multiplier. -/
theorem normalizedFiniteFunctionalReturnMetricCrossCovariance_eq_coefficients
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {camera : index → ℕ} (hcamera : ∀ i, 2 ≤ camera i)
    (z : ℂ) (cutoff : ℕ) (multiplier : ℕ → ℝ)
    (endpointMap :
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (bulkMap : Matrix bulk (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff camera
        multiplier endpointMap poisson =
      fun i j =>
        (finiteFunctionalCoefficientCovariance (resolventWeight z) multiplier
          cutoff camera i j : ℂ) := by
  ext i j
  simp only [normalizedFiniteFunctionalReturnMetricCrossCovariance]
  rw [functionalReturnMetricCrossCovariance_eq_direct
    (finiteCameraMatrix cutoff camera)
    (finiteRealDiagonalObservable multiplier
      (finiteFamilyWindow cutoff camera))
    (finiteResolventMatrix z (finiteFamilyWindow cutoff camera))
    endpointMap bulkMap poisson hpoisson hisometry]
  have hdirect :=
    normalizedFiniteFunctionalDirectCovariance_eq_coefficients
      hcamera z cutoff multiplier
  simpa only [normalizedFiniteFunctionalDirectCovariance] using
    congr_fun (congr_fun hdirect i) j

/-- Any analytic limit proved for the literal functional coefficient sums
transfers immediately to the direct finite matrix product. -/
theorem tendsto_normalizedFiniteFunctionalDirectCovariance_of_coefficients
    {index : Type*} [Fintype index] {camera : index → ℕ}
    (hcamera : ∀ i, 2 ≤ camera i) {z : ℂ}
    {multiplier : ℕ → ℕ → ℝ} {limit : Matrix index index ℂ}
    (hcoefficients : Tendsto (fun cutoff i j =>
      (finiteFunctionalCoefficientCovariance (resolventWeight z)
        (multiplier cutoff) cutoff camera i j : ℂ)) atTop (nhds limit)) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalDirectCovariance z cutoff camera
        (multiplier cutoff)) atTop (nhds limit) := by
  apply hcoefficients.congr'
  filter_upwards with cutoff
  have hexact := normalizedFiniteFunctionalDirectCovariance_eq_coefficients
    hcamera z cutoff (multiplier cutoff)
  exact hexact.symm

/-- The same coefficient-sum limit transfers to every compatible finite
return-metric colligation family. -/
theorem
    tendsto_normalizedFiniteFunctionalReturnMetricCrossCovariance_of_coefficients
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {camera : index → ℕ} (hcamera : ∀ i, 2 ≤ camera i) {z : ℂ}
    {multiplier : ℕ → ℕ → ℝ} {limit : Matrix index index ℂ}
    (endpointMap : ∀ cutoff,
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (bulkMap : ∀ cutoff,
      Matrix bulk (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : ℕ → Matrix bulk endpoint ℂ)
    (hpoisson : ∀ cutoff, poisson cutoff * endpointMap cutoff = bulkMap cutoff)
    (hisometry : ∀ cutoff,
      (endpointMap cutoff)ᴴ * endpointMap cutoff +
        (bulkMap cutoff)ᴴ * bulkMap cutoff = 1)
    (hcoefficients : Tendsto (fun cutoff i j =>
      (finiteFunctionalCoefficientCovariance (resolventWeight z)
        (multiplier cutoff) cutoff camera i j : ℂ)) atTop (nhds limit)) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff camera
        (multiplier cutoff) (endpointMap cutoff) (poisson cutoff))
      atTop (nhds limit) := by
  have hdirect :=
    tendsto_normalizedFiniteFunctionalDirectCovariance_of_coefficients
      hcamera hcoefficients
  apply hdirect.congr'
  filter_upwards with cutoff
  have hdirectExact :=
    normalizedFiniteFunctionalDirectCovariance_eq_coefficients
      hcamera z cutoff (multiplier cutoff)
  have hreturnExact :=
    normalizedFiniteFunctionalReturnMetricCrossCovariance_eq_coefficients
      hcamera z cutoff (multiplier cutoff) (endpointMap cutoff)
        (bulkMap cutoff) (poisson cutoff) (hpoisson cutoff) (hisometry cutoff)
  exact hdirectExact.trans hreturnExact.symm

/-- Multiplier obtained by evaluating a real polynomial at the centered
finite spectral coordinate `log(n+1) - μ_M(z)`. -/
def centeredPolynomialMultiplier (polynomial : Polynomial ℝ)
    (z : ℂ) (cutoff n : ℕ) : ℝ :=
  polynomial.eval (Real.log (n + 1) - resolventLogMean z cutoff)

/-- Literal finite covariance for an arbitrary centered real polynomial. -/
def finiteCenteredPolynomialCoefficientCovariance {index : Type*}
    (polynomial : Polynomial ℝ) (z : ℂ) (cutoff : ℕ)
    (camera : index → ℕ) : Matrix index index ℝ :=
  finiteFunctionalCoefficientCovariance (resolventWeight z)
    (centeredPolynomialMultiplier polynomial z cutoff) cutoff camera

/-- Exact finite return-metric functional identity specialized to every real
polynomial in the centered logarithmic spectral coordinate. -/
theorem normalizedFiniteCenteredPolynomialReturnMetricCrossCovariance_eq
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {camera : index → ℕ} (hcamera : ∀ i, 2 ≤ camera i)
    (polynomial : Polynomial ℝ) (z : ℂ) (cutoff : ℕ)
    (endpointMap :
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (bulkMap : Matrix bulk (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : Matrix bulk endpoint ℂ)
    (hpoisson : poisson * endpointMap = bulkMap)
    (hisometry : endpointMapᴴ * endpointMap + bulkMapᴴ * bulkMap = 1) :
    normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff camera
        (centeredPolynomialMultiplier polynomial z cutoff) endpointMap poisson =
      fun i j =>
        (finiteCenteredPolynomialCoefficientCovariance polynomial z cutoff
          camera i j : ℂ) := by
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    normalizedFiniteFunctionalReturnMetricCrossCovariance_eq_coefficients
      hcamera z cutoff (centeredPolynomialMultiplier polynomial z cutoff)
        endpointMap bulkMap poisson hpoisson hisometry

/-- The constant functional multiplier recovers the order-zero finite
covariance from the previous milestone. -/
theorem finiteFunctionalCoefficientCovariance_one
    {index : Type*} (weight : ℕ → ℝ) (cutoff : ℕ) (camera : index → ℕ) :
    finiteFunctionalCoefficientCovariance weight (fun _ => 1) cutoff camera =
      finiteCoefficientCovariance weight cutoff camera := by
  ext i j
  simp only [finiteFunctionalCoefficientCovariance,
    finiteCoefficientCovariance, mul_one]

@[simp] theorem centeredPolynomialMultiplier_one (z : ℂ) (cutoff n : ℕ) :
    centeredPolynomialMultiplier (1 : Polynomial ℝ) z cutoff n = 1 := by
  simp [centeredPolynomialMultiplier]

/-- The constant polynomial recovers exactly the literal finite covariance
from the order-zero limit. -/
theorem finiteCenteredPolynomialCoefficientCovariance_one
    {index : Type*} (z : ℂ) (cutoff : ℕ) (camera : index → ℕ) :
    finiteCenteredPolynomialCoefficientCovariance (1 : Polynomial ℝ) z cutoff
        camera =
      finiteCoefficientCovariance (resolventWeight z) cutoff camera := by
  have hmult : centeredPolynomialMultiplier (1 : Polynomial ℝ) z cutoff =
      fun _ => 1 := by
    funext n
    exact centeredPolynomialMultiplier_one z cutoff n
  rw [finiteCenteredPolynomialCoefficientCovariance, hmult]
  exact finiteFunctionalCoefficientCovariance_one
    (index := index) (resolventWeight z) cutoff camera

end

end NativeCarrySpectralWeyl.Limits
