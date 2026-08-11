import NativeCarrySpectralWeyl.Limits.EighthFunctionalCovariance
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Tactic

/-!
# General functional-moment hierarchy

This file packages the polynomial recurrence recorded in the research notes,

`P₀(t) = 1`, `Pₖ(t) = (1 + t)ᵏ - k Pₖ₋₁(t)`,

into a single Lean definition.  It proves that `Pₖ` is monic of degree `k`,
constructs the corresponding shared-slope camera moment

`Mₖ(i,j) = G(i,j) Pₖ(log(ell(i,j)))`,

and identifies the first eight instances with the concrete moment weights and
matrices already used by the analytic covariance proofs.
-/

open scoped Matrix

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Polynomial hierarchy from the functional-limit recurrence
`P₀(t) = 1` and `Pₖ(t) = (1+t)ᵏ - kPₖ₋₁(t)`. -/
def functionalMomentPolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | degree + 1 =>
      (Polynomial.X + 1) ^ (degree + 1) -
        Polynomial.C ((degree + 1 : ℕ) : ℝ) *
          functionalMomentPolynomial degree

@[simp] theorem functionalMomentPolynomial_zero :
    functionalMomentPolynomial 0 = 1 :=
  rfl

theorem functionalMomentPolynomial_succ (degree : ℕ) :
    functionalMomentPolynomial (degree + 1) =
      (Polynomial.X + 1) ^ (degree + 1) -
        Polynomial.C ((degree + 1 : ℕ) : ℝ) *
          functionalMomentPolynomial degree :=
  rfl

/-- Every polynomial in the hierarchy is monic of exactly the indexed degree. -/
theorem functionalMomentPolynomial_isMonicOfDegree (degree : ℕ) :
    Polynomial.IsMonicOfDegree (functionalMomentPolynomial degree) degree := by
  induction degree with
  | zero =>
      rw [functionalMomentPolynomial_zero]
      exact Polynomial.isMonicOfDegree_zero_iff.mpr rfl
  | succ degree ih =>
      rw [functionalMomentPolynomial_succ]
      have hlead : Polynomial.IsMonicOfDegree
          ((Polynomial.X + 1 : Polynomial ℝ) ^ (degree + 1)) (degree + 1) := by
        simpa using
          (Polynomial.isMonicOfDegree_X_add_one (1 : ℝ)).pow (degree + 1)
      have hlower : (Polynomial.C ((degree + 1 : ℕ) : ℝ) *
          functionalMomentPolynomial degree).natDegree < degree + 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans_lt (by
          rw [ih.natDegree_eq]
          exact Nat.lt_succ_self degree)
      exact hlead.sub hlower

/-- In particular, `Pₖ` is monic. -/
theorem functionalMomentPolynomial_monic (degree : ℕ) :
    (functionalMomentPolynomial degree).Monic :=
  (functionalMomentPolynomial_isMonicOfDegree degree).monic

/-- In particular, `Pₖ` has natural degree exactly `k`. -/
theorem functionalMomentPolynomial_natDegree (degree : ℕ) :
    (functionalMomentPolynomial degree).natDegree = degree :=
  (functionalMomentPolynomial_isMonicOfDegree degree).natDegree_eq

@[simp] theorem functionalMomentPolynomial_one :
    functionalMomentPolynomial 1 = Polynomial.X := by
  norm_num [functionalMomentPolynomial]

@[simp] theorem functionalMomentPolynomial_two :
    functionalMomentPolynomial 2 = Polynomial.X ^ 2 + 1 := by
  rw [functionalMomentPolynomial_succ, functionalMomentPolynomial_one]
  norm_num [Polynomial.C_ofNat]
  ring

@[simp] theorem functionalMomentPolynomial_three :
    functionalMomentPolynomial 3 =
      Polynomial.X ^ 3 + 3 * Polynomial.X - 2 := by
  rw [functionalMomentPolynomial_succ, functionalMomentPolynomial_two]
  norm_num [Polynomial.C_ofNat]
  ring

@[simp] theorem functionalMomentPolynomial_four :
    functionalMomentPolynomial 4 =
      Polynomial.X ^ 4 + 6 * Polynomial.X ^ 2 - 8 * Polynomial.X + 9 := by
  rw [functionalMomentPolynomial_succ, functionalMomentPolynomial_three]
  norm_num [Polynomial.C_ofNat]
  ring

@[simp] theorem functionalMomentPolynomial_five :
    functionalMomentPolynomial 5 =
      Polynomial.X ^ 5 + 10 * Polynomial.X ^ 3 -
        20 * Polynomial.X ^ 2 + 45 * Polynomial.X - 44 := by
  rw [functionalMomentPolynomial_succ, functionalMomentPolynomial_four]
  norm_num [Polynomial.C_ofNat]
  ring

@[simp] theorem functionalMomentPolynomial_six :
    functionalMomentPolynomial 6 =
      Polynomial.X ^ 6 + 15 * Polynomial.X ^ 4 -
        40 * Polynomial.X ^ 3 + 135 * Polynomial.X ^ 2 -
          264 * Polynomial.X + 265 := by
  rw [functionalMomentPolynomial_succ, functionalMomentPolynomial_five]
  norm_num [Polynomial.C_ofNat]
  ring

@[simp] theorem functionalMomentPolynomial_seven :
    functionalMomentPolynomial 7 =
      Polynomial.X ^ 7 + 21 * Polynomial.X ^ 5 -
        70 * Polynomial.X ^ 4 + 315 * Polynomial.X ^ 3 -
          924 * Polynomial.X ^ 2 + 1855 * Polynomial.X - 1854 := by
  rw [functionalMomentPolynomial_succ, functionalMomentPolynomial_six]
  norm_num [Polynomial.C_ofNat]
  ring

@[simp] theorem functionalMomentPolynomial_eight :
    functionalMomentPolynomial 8 =
      Polynomial.X ^ 8 + 28 * Polynomial.X ^ 6 -
        112 * Polynomial.X ^ 5 + 630 * Polynomial.X ^ 4 -
          2464 * Polynomial.X ^ 3 + 7420 * Polynomial.X ^ 2 -
            14832 * Polynomial.X + 14833 := by
  rw [functionalMomentPolynomial_succ, functionalMomentPolynomial_seven]
  norm_num [Polynomial.C_ofNat]
  ring

/-- Degree-`k` centered functional-moment weight at a spectral slope. -/
def functionalMomentWeight (degree slope : ℕ) : ℝ :=
  (functionalMomentPolynomial degree).eval (Real.log slope)

/-- Pointwise recurrence for the general shared-slope moment weight. -/
theorem functionalMomentWeight_succ (degree slope : ℕ) :
    functionalMomentWeight (degree + 1) slope =
      (1 + Real.log slope) ^ (degree + 1) -
        (degree + 1) * functionalMomentWeight degree slope := by
  rw [functionalMomentWeight, functionalMomentPolynomial_succ,
    functionalMomentWeight]
  simp
  ring

/-- General centered functional camera moment of degree `k`. -/
def functionalMomentMatrix {ι : Type*} (degree period : ℕ)
    (camera : ι → ℕ) : Matrix ι ι ℝ :=
  weightedMomentMatrix period camera (functionalMomentWeight degree)

/-- Entry formula `Mₖ(i,j) = G(i,j) Pₖ(log(ell(i,j)))`. -/
theorem functionalMomentMatrix_apply {ι : Type*} (degree period : ℕ)
    (camera : ι → ℕ) (i j : ι) :
    functionalMomentMatrix degree period camera i j =
      periodicGramMatrix period camera i j *
        (functionalMomentPolynomial degree).eval
          (Real.log (slopeOverlap camera i j)) := by
  rfl

/-- Every finite general functional-moment matrix is Hermitian. -/
theorem functionalMomentMatrix_isHermitian {ι : Type*} [Fintype ι]
    (degree period : ℕ) (camera : ι → ℕ) :
    (functionalMomentMatrix degree period camera).IsHermitian :=
  weightedMomentMatrix_isHermitian period camera (functionalMomentWeight degree)

/-- Every finite general functional-moment matrix is self-adjoint. -/
theorem functionalMomentMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    (degree period : ℕ) (camera : ι → ℕ) :
    IsSelfAdjoint (functionalMomentMatrix degree period camera) :=
  (functionalMomentMatrix_isHermitian degree period camera).isSelfAdjoint

/-- The degree-zero member of the hierarchy is the periodic Gram matrix. -/
@[simp] theorem functionalMomentMatrix_zero {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 0 period camera = periodicGramMatrix period camera := by
  ext i j
  simp [functionalMomentMatrix_apply]

@[simp] theorem functionalMomentWeight_one :
    functionalMomentWeight 1 = firstMomentWeight := by
  funext slope
  simp [functionalMomentWeight, firstMomentWeight]

@[simp] theorem functionalMomentWeight_two :
    functionalMomentWeight 2 = secondCenteredMomentWeight := by
  funext slope
  simp [functionalMomentWeight, secondCenteredMomentWeight]
  ring

@[simp] theorem functionalMomentWeight_three :
    functionalMomentWeight 3 = thirdCenteredMomentWeight := by
  funext slope
  simp [functionalMomentWeight, thirdCenteredMomentWeight]

@[simp] theorem functionalMomentWeight_four :
    functionalMomentWeight 4 = fourthCenteredMomentWeight := by
  funext slope
  simp [functionalMomentWeight, fourthCenteredMomentWeight]

@[simp] theorem functionalMomentWeight_five :
    functionalMomentWeight 5 = fifthCenteredMomentWeight := by
  funext slope
  simp [functionalMomentWeight, fifthCenteredMomentWeight]

@[simp] theorem functionalMomentWeight_six :
    functionalMomentWeight 6 = sixthCenteredMomentWeight := by
  funext slope
  simp [functionalMomentWeight, sixthCenteredMomentWeight]

@[simp] theorem functionalMomentWeight_seven :
    functionalMomentWeight 7 = seventhCenteredMomentWeight := by
  funext slope
  simp [functionalMomentWeight, seventhCenteredMomentWeight]

@[simp] theorem functionalMomentWeight_eight :
    functionalMomentWeight 8 = eighthCenteredMomentWeight := by
  funext slope
  simp [functionalMomentWeight, eighthCenteredMomentWeight]

@[simp] theorem functionalMomentMatrix_one {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 1 period camera = firstMomentMatrix period camera := by
  simp [functionalMomentMatrix, firstMomentMatrix]

@[simp] theorem functionalMomentMatrix_two {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 2 period camera =
      secondCenteredMomentMatrix period camera := by
  simp [functionalMomentMatrix, secondCenteredMomentMatrix]

@[simp] theorem functionalMomentMatrix_three {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 3 period camera =
      thirdCenteredMomentMatrix period camera := by
  simp [functionalMomentMatrix, thirdCenteredMomentMatrix]

@[simp] theorem functionalMomentMatrix_four {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 4 period camera =
      fourthCenteredMomentMatrix period camera := by
  simp [functionalMomentMatrix, fourthCenteredMomentMatrix]

@[simp] theorem functionalMomentMatrix_five {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 5 period camera =
      fifthCenteredMomentMatrix period camera := by
  simp [functionalMomentMatrix, fifthCenteredMomentMatrix]

@[simp] theorem functionalMomentMatrix_six {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 6 period camera =
      sixthCenteredMomentMatrix period camera := by
  simp [functionalMomentMatrix, sixthCenteredMomentMatrix]

@[simp] theorem functionalMomentMatrix_seven {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 7 period camera =
      seventhCenteredMomentMatrix period camera := by
  simp [functionalMomentMatrix, seventhCenteredMomentMatrix]

@[simp] theorem functionalMomentMatrix_eight {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) :
    functionalMomentMatrix 8 period camera =
      eighthCenteredMomentMatrix period camera := by
  simp [functionalMomentMatrix, eighthCenteredMomentMatrix]

/-- Literal degree-`k` functional-moment matrix for cameras `2, ..., 7`. -/
def sixCameraFunctionalMoment (degree : ℕ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![6 * functionalMomentWeight degree 4, 0,
       10 * functionalMomentWeight degree 4, 0,
       (16 / 3) * functionalMomentWeight degree 4, 0;
     0, 6 * functionalMomentWeight degree 3, 0, 0,
       6 * functionalMomentWeight degree 3, 0;
     10 * functionalMomentWeight degree 4, 0,
       22 * functionalMomentWeight degree 4, 0,
       (16 / 3) * functionalMomentWeight degree 4, 0;
     0, 0, 0, 20 * functionalMomentWeight degree 5, 0, 0;
     (16 / 3) * functionalMomentWeight degree 4,
       6 * functionalMomentWeight degree 3,
       (16 / 3) * functionalMomentWeight degree 4, 0,
       44 * functionalMomentWeight degree 6, 0;
     0, 0, 0, 0, 0, 42 * functionalMomentWeight degree 7]

/-- Exact all-degree functional-moment formula for cameras `2, ..., 7`. -/
theorem sixCameraFunctionalMoment_eq (degree : ℕ) :
    functionalMomentMatrix degree 420 sixCamera =
      sixCameraFunctionalMoment degree := by
  rw [functionalMomentMatrix, weightedMomentMatrix, sixCameraGram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraFunctionalMoment, slopeWeightMatrix, slopeOverlap,
      sixCamera, sixCameraGram, sixCameraGramRat, cameraSlope]

/-- The literal six-camera functional moment is self-adjoint in every degree. -/
theorem sixCameraFunctionalMoment_isSelfAdjoint (degree : ℕ) :
    IsSelfAdjoint (sixCameraFunctionalMoment degree) := by
  rw [← sixCameraFunctionalMoment_eq degree]
  exact functionalMomentMatrix_isSelfAdjoint degree 420 sixCamera

end

end NativeCarrySpectralWeyl.Limits
