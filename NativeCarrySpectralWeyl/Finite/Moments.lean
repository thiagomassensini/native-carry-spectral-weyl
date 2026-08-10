import NativeCarrySpectralWeyl.Finite.Gram

/-!
# First and second finite camera moments

This file formalizes the two centered logarithmic moment matrices from the
finite-camera research notes.  If

`ell(i,j) = min(cameraSlope(camera i), cameraSlope(camera j))`,

then the first and second centered moments are

`H(i,j) = G(i,j) * log(ell(i,j))`

and

`J(i,j) = G(i,j) * (1 + log(ell(i,j)) ^ 2)`.

Both are instances of a general slope-weighted moment matrix.  Every real
slope weight gives a Hermitian, equivalently self-adjoint, matrix because the
weight kernel is symmetric and the periodic Gram matrix is Hermitian.  The
literal matrices for cameras `2, ..., 7` are then recovered from the exact
period-`420` Gram theorem.

This module does not introduce `G⁻¹/²`, the whitened logarithmic operator or
the variance Schur complement; those belong to the subsequent whitening
layer.
-/

open scoped BigOperators Matrix

noncomputable section

namespace NativeCarrySpectralWeyl.Finite

open NativeCarrySpectralWeyl.Camera

/-- Minimum spectral slope shared by two cameras in an indexed package. -/
def slopeOverlap {ι : Type*} (camera : ι → ℕ) (i j : ι) : ℕ :=
  min (cameraSlope (camera i)) (cameraSlope (camera j))

/-- Symmetric matrix obtained by evaluating a real weight at each shared
slope. -/
def slopeWeightMatrix {ι : Type*} (weight : ℕ → ℝ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  fun i j => weight (slopeOverlap camera i j)

/-- Every real shared-slope weight matrix is Hermitian. -/
theorem slopeWeightMatrix_isHermitian {ι : Type*}
    (weight : ℕ → ℝ) (camera : ι → ℕ) :
    (slopeWeightMatrix weight camera).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp [slopeWeightMatrix, slopeOverlap, min_comm]

/-- General finite camera moment obtained by weighting the periodic Gram at
the shared slope. -/
def weightedMomentMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ)
    (weight : ℕ → ℝ) : Matrix ι ι ℝ :=
  periodicGramMatrix period camera ⊙ slopeWeightMatrix weight camera

/-- Entry formula for a general weighted camera moment. -/
theorem weightedMomentMatrix_apply {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) (weight : ℕ → ℝ) (i j : ι) :
    weightedMomentMatrix period camera weight i j =
      periodicGramMatrix period camera i j * weight (slopeOverlap camera i j) := by
  rfl

/-- Every finite real weighted camera moment is Hermitian. -/
theorem weightedMomentMatrix_isHermitian {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) (weight : ℕ → ℝ) :
    (weightedMomentMatrix period camera weight).IsHermitian := by
  exact (periodicGramMatrix_posSemidef period camera).isHermitian.hadamard
    (slopeWeightMatrix_isHermitian weight camera)

/-- Every finite real weighted camera moment is self-adjoint as an element of
the real matrix star algebra. -/
theorem weightedMomentMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) (weight : ℕ → ℝ) :
    IsSelfAdjoint (weightedMomentMatrix period camera weight) :=
  (weightedMomentMatrix_isHermitian period camera weight).isSelfAdjoint

/-- First centered logarithmic moment weight. -/
def firstMomentWeight (slope : ℕ) : ℝ :=
  Real.log slope

/-- Second centered logarithmic moment weight. -/
def secondCenteredMomentWeight (slope : ℕ) : ℝ :=
  1 + (Real.log slope) ^ 2

/-- First centered logarithmic camera moment `H`. -/
def firstMomentMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  weightedMomentMatrix period camera firstMomentWeight

/-- Second centered logarithmic camera moment `J`. -/
def secondCenteredMomentMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  weightedMomentMatrix period camera secondCenteredMomentWeight

/-- Source formula `H(i,j) = G(i,j) * log(ell(i,j))`. -/
theorem firstMomentMatrix_apply {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    firstMomentMatrix period camera i j =
      periodicGramMatrix period camera i j *
        Real.log (slopeOverlap camera i j) := by
  rfl

/-- Source formula `J(i,j) = G(i,j) * (1 + log(ell(i,j))²)`. -/
theorem secondCenteredMomentMatrix_apply {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    secondCenteredMomentMatrix period camera i j =
      periodicGramMatrix period camera i j *
        (1 + Real.log (slopeOverlap camera i j) ^ 2) := by
  rfl

/-- The first centered logarithmic camera moment is Hermitian. -/
theorem firstMomentMatrix_isHermitian {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (firstMomentMatrix period camera).IsHermitian :=
  weightedMomentMatrix_isHermitian period camera firstMomentWeight

/-- The first centered logarithmic camera moment is self-adjoint. -/
theorem firstMomentMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    IsSelfAdjoint (firstMomentMatrix period camera) :=
  (firstMomentMatrix_isHermitian period camera).isSelfAdjoint

/-- The second centered logarithmic camera moment is Hermitian. -/
theorem secondCenteredMomentMatrix_isHermitian {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (secondCenteredMomentMatrix period camera).IsHermitian :=
  weightedMomentMatrix_isHermitian period camera secondCenteredMomentWeight

/-- The second centered logarithmic camera moment is self-adjoint. -/
theorem secondCenteredMomentMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    IsSelfAdjoint (secondCenteredMomentMatrix period camera) :=
  (secondCenteredMomentMatrix_isHermitian period camera).isSelfAdjoint

/-- Literal first moment for cameras `2, ..., 7`. -/
def sixCameraFirstMoment : Matrix (Fin 6) (Fin 6) ℝ :=
  !![6 * Real.log 4, 0, 10 * Real.log 4, 0, (16 / 3) * Real.log 4, 0;
     0, 6 * Real.log 3, 0, 0, 6 * Real.log 3, 0;
     10 * Real.log 4, 0, 22 * Real.log 4, 0, (16 / 3) * Real.log 4, 0;
     0, 0, 0, 20 * Real.log 5, 0, 0;
     (16 / 3) * Real.log 4, 6 * Real.log 3, (16 / 3) * Real.log 4, 0,
       44 * Real.log 6, 0;
     0, 0, 0, 0, 0, 42 * Real.log 7]

/-- Literal second centered moment for cameras `2, ..., 7`. -/
def sixCameraSecondCenteredMoment : Matrix (Fin 6) (Fin 6) ℝ :=
  !![6 * (1 + Real.log 4 ^ 2), 0, 10 * (1 + Real.log 4 ^ 2), 0,
       (16 / 3) * (1 + Real.log 4 ^ 2), 0;
     0, 6 * (1 + Real.log 3 ^ 2), 0, 0, 6 * (1 + Real.log 3 ^ 2), 0;
     10 * (1 + Real.log 4 ^ 2), 0, 22 * (1 + Real.log 4 ^ 2), 0,
       (16 / 3) * (1 + Real.log 4 ^ 2), 0;
     0, 0, 0, 20 * (1 + Real.log 5 ^ 2), 0, 0;
     (16 / 3) * (1 + Real.log 4 ^ 2), 6 * (1 + Real.log 3 ^ 2),
       (16 / 3) * (1 + Real.log 4 ^ 2), 0, 44 * (1 + Real.log 6 ^ 2), 0;
     0, 0, 0, 0, 0, 42 * (1 + Real.log 7 ^ 2)]

/-- Exact recovery of the documented first-moment matrix for cameras
`2, ..., 7`. -/
theorem sixCameraFirstMoment_eq :
    firstMomentMatrix 420 sixCamera = sixCameraFirstMoment := by
  rw [firstMomentMatrix, weightedMomentMatrix, sixCameraGram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraFirstMoment, slopeWeightMatrix, firstMomentWeight,
      slopeOverlap, sixCamera, sixCameraGram, sixCameraGramRat, cameraSlope]

/-- Exact recovery of the documented second centered moment for cameras
`2, ..., 7`. -/
theorem sixCameraSecondCenteredMoment_eq :
    secondCenteredMomentMatrix 420 sixCamera =
      sixCameraSecondCenteredMoment := by
  rw [secondCenteredMomentMatrix, weightedMomentMatrix, sixCameraGram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraSecondCenteredMoment, slopeWeightMatrix,
      secondCenteredMomentWeight, slopeOverlap, sixCamera, sixCameraGram,
      sixCameraGramRat, cameraSlope]

/-- The exact six-camera first moment is self-adjoint. -/
theorem sixCameraFirstMoment_isSelfAdjoint :
    IsSelfAdjoint sixCameraFirstMoment := by
  rw [← sixCameraFirstMoment_eq]
  exact firstMomentMatrix_isSelfAdjoint 420 sixCamera

/-- The exact six-camera second centered moment is self-adjoint. -/
theorem sixCameraSecondCenteredMoment_isSelfAdjoint :
    IsSelfAdjoint sixCameraSecondCenteredMoment := by
  rw [← sixCameraSecondCenteredMoment_eq]
  exact secondCenteredMomentMatrix_isSelfAdjoint 420 sixCamera

end NativeCarrySpectralWeyl.Finite
