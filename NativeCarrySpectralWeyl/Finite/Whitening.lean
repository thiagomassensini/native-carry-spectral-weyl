import NativeCarrySpectralWeyl.Finite.Moments
import Mathlib.Analysis.Matrix.Order

/-!
# Finite camera whitening and the variance Schur complement

This file formalizes the algebraic whitening layer from the finite-camera
research notes.  For a positive-definite Gram matrix `G`, its canonical
positive inverse square root is

`R = (CFC.sqrt G)⁻¹ = CFC.sqrt G⁻¹`.

It satisfies both `R * R = G⁻¹` and the normalization identity
`R * G * R = 1`.  A matrix `A` is whitened by the congruence
`R * A * R`.  In particular,

`L = R * H * R`, `M₂ = R * J * R`, and `V = M₂ - L²`.

The variance is proved to be exactly the whitening of the Schur complement

`J - H * G⁻¹ * H`.

Consequently it is positive semidefinite whenever that Schur complement is,
or equivalently whenever the Hermitian moment block matrix
`[[G, H], [H, J]]` is positive semidefinite.  The canonical operators for the
exact period-`420` camera package `2, ..., 7` are then instantiated and proved
self-adjoint.  Proving positivity of that concrete moment block from its
continuous step-measure realization belongs to the subsequent POVM layer.
-/

open scoped BigOperators Matrix MatrixOrder

noncomputable section

namespace NativeCarrySpectralWeyl.Finite

/-- Canonical positive inverse square root of a finite real matrix.  The
positive-definite hypothesis is carried by the theorems rather than the
definition so that this remains an ordinary matrix-valued construction. -/
def positiveInverseSqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (CFC.sqrt G)⁻¹

/-- For a positive-definite matrix, the inverse of its positive square root is
the positive square root of its inverse. -/
theorem positiveInverseSqrt_eq_sqrt_inv {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    positiveInverseSqrt G = CFC.sqrt G⁻¹ := by
  exact hG.posSemidef.inv_sqrt

/-- The canonical inverse square root of a positive-definite matrix is itself
positive definite. -/
theorem positiveInverseSqrt_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    (positiveInverseSqrt G).PosDef := by
  exact (Matrix.isStrictlyPositive_iff_posDef.mp
    (hG.isStrictlyPositive.sqrt G)).inv

/-- Positive semidefiniteness of the canonical inverse square root. -/
theorem positiveInverseSqrt_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    (positiveInverseSqrt G).PosSemidef :=
  (positiveInverseSqrt_posDef hG).posSemidef

/-- Hermitianity of the canonical inverse square root. -/
theorem positiveInverseSqrt_isHermitian {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    (positiveInverseSqrt G).IsHermitian :=
  (positiveInverseSqrt_posDef hG).isHermitian

/-- Self-adjointness of the canonical inverse square root. -/
theorem positiveInverseSqrt_isSelfAdjoint {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    IsSelfAdjoint (positiveInverseSqrt G) :=
  (positiveInverseSqrt_isHermitian hG).isSelfAdjoint

/-- Squaring the canonical inverse square root gives the matrix inverse. -/
theorem positiveInverseSqrt_mul_self {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    positiveInverseSqrt G * positiveInverseSqrt G = G⁻¹ := by
  rw [positiveInverseSqrt, hG.posSemidef.inv_sqrt]
  exact CFC.sqrt_mul_sqrt_self G⁻¹ hG.inv.posSemidef.nonneg

/-- The positive inverse square root whitens the Gram matrix to the identity. -/
theorem positiveInverseSqrt_whitens {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    positiveInverseSqrt G * G * positiveInverseSqrt G = 1 := by
  unfold positiveInverseSqrt
  nth_rewrite 2 [← CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  letI := (hG.isStrictlyPositive.sqrt G).isUnit.invertible
  calc
    (CFC.sqrt G)⁻¹ * (CFC.sqrt G * CFC.sqrt G) * (CFC.sqrt G)⁻¹ =
        ((CFC.sqrt G)⁻¹ * CFC.sqrt G) *
          (CFC.sqrt G * (CFC.sqrt G)⁻¹) := by noncomm_ring
    _ = 1 := by
      rw [Matrix.inv_mul_of_invertible, Matrix.mul_inv_of_invertible,
        Matrix.one_mul]

/-- Congruence whitening of a finite moment matrix by `G⁻¹/²`. -/
def whitenedMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  positiveInverseSqrt G * A * positiveInverseSqrt G

/-- Whitening preserves Hermitianity when the Gram matrix is positive
definite. -/
theorem whitenedMatrix_isHermitian {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G A : Matrix ι ι ℝ} (hG : G.PosDef)
    (hA : A.IsHermitian) : (whitenedMatrix G A).IsHermitian := by
  have hR := positiveInverseSqrt_isHermitian hG
  have h := Matrix.isHermitian_mul_mul_conjTranspose
    (positiveInverseSqrt G) hA
  rw [hR.eq] at h
  exact h

/-- Whitening preserves positive semidefiniteness. -/
theorem whitenedMatrix_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G A : Matrix ι ι ℝ} (hG : G.PosDef)
    (hA : A.PosSemidef) : (whitenedMatrix G A).PosSemidef := by
  have hR := positiveInverseSqrt_isHermitian hG
  have h := hA.mul_mul_conjTranspose_same (positiveInverseSqrt G)
  rw [hR.eq] at h
  exact h

/-- Whitening preserves self-adjointness of Hermitian matrices. -/
theorem whitenedMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G A : Matrix ι ι ℝ} (hG : G.PosDef)
    (hA : A.IsHermitian) : IsSelfAdjoint (whitenedMatrix G A) :=
  (whitenedMatrix_isHermitian hG hA).isSelfAdjoint

/-- Whitening a positive-definite Gram matrix gives the identity matrix. -/
theorem whitenedGram_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : G.PosDef) :
    whitenedMatrix G G = 1 :=
  positiveInverseSqrt_whitens hG

/-- Whitened first centered logarithmic moment `L = G⁻¹/² H G⁻¹/²`. -/
def whitenedFirstMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  whitenedMatrix G H

/-- Whitened second centered logarithmic moment
`M₂ = G⁻¹/² J G⁻¹/²`. -/
def whitenedSecondMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G J : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  whitenedMatrix G J

/-- The whitened first moment is self-adjoint. -/
theorem whitenedFirstMoment_isSelfAdjoint {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G H : Matrix ι ι ℝ} (hG : G.PosDef)
    (hH : H.IsHermitian) : IsSelfAdjoint (whitenedFirstMoment G H) :=
  whitenedMatrix_isSelfAdjoint hG hH

/-- The whitened second moment is self-adjoint. -/
theorem whitenedSecondMoment_isSelfAdjoint {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G J : Matrix ι ι ℝ} (hG : G.PosDef)
    (hJ : J.IsHermitian) : IsSelfAdjoint (whitenedSecondMoment G J) :=
  whitenedMatrix_isSelfAdjoint hG hJ

/-- Finite camera variance `V = M₂ - L²`. -/
def varianceOperator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H J : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  whitenedSecondMoment G J -
    whitenedFirstMoment G H * whitenedFirstMoment G H

/-- Unwhitened Schur complement controlling the variance. -/
def momentSchurComplement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H J : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  J - H * G⁻¹ * H

/-- Hermitian two-by-two moment block `[[G,H],[H,J]]`. -/
def momentBlockMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H J : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks G H H J

/-- For positive-definite `G` and Hermitian `H`, positivity of the full moment
block is equivalent to positivity of its Schur complement. -/
theorem momentBlockMatrix_posSemidef_iff_schur {ι : Type*}
    [Fintype ι] [DecidableEq ι] {G H J : Matrix ι ι ℝ}
    (hG : G.PosDef) (hH : H.IsHermitian) :
    (momentBlockMatrix G H J).PosSemidef ↔
      (momentSchurComplement G H J).PosSemidef := by
  letI := hG.isUnit.invertible
  have h := Matrix.PosDef.fromBlocks₁₁ H J hG
  rw [hH.eq] at h
  exact h

/-- Exact algebraic identity
`V = G⁻¹/² (J - H G⁻¹ H) G⁻¹/²`. -/
theorem varianceOperator_eq_whitened_schur {ι : Type*}
    [Fintype ι] [DecidableEq ι] {G H J : Matrix ι ι ℝ} (hG : G.PosDef) :
    varianceOperator G H J = whitenedMatrix G (momentSchurComplement G H J) := by
  have hRR := positiveInverseSqrt_mul_self hG
  unfold varianceOperator whitenedSecondMoment whitenedFirstMoment
    whitenedMatrix momentSchurComplement
  calc
    positiveInverseSqrt G * J * positiveInverseSqrt G -
        (positiveInverseSqrt G * H * positiveInverseSqrt G) *
          (positiveInverseSqrt G * H * positiveInverseSqrt G) =
      positiveInverseSqrt G * J * positiveInverseSqrt G -
        positiveInverseSqrt G * H *
          (positiveInverseSqrt G * positiveInverseSqrt G) * H *
            positiveInverseSqrt G := by noncomm_ring
    _ = positiveInverseSqrt G * J * positiveInverseSqrt G -
        positiveInverseSqrt G * H * G⁻¹ * H * positiveInverseSqrt G := by
      rw [hRR]
    _ = positiveInverseSqrt G * (J - H * G⁻¹ * H) *
        positiveInverseSqrt G := by noncomm_ring

/-- A positive Schur complement gives a positive-semidefinite variance. -/
theorem varianceOperator_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G H J : Matrix ι ι ℝ} (hG : G.PosDef)
    (hSchur : (momentSchurComplement G H J).PosSemidef) :
    (varianceOperator G H J).PosSemidef := by
  rw [varianceOperator_eq_whitened_schur hG]
  exact whitenedMatrix_posSemidef hG hSchur

/-- A positive-semidefinite moment block gives a positive-semidefinite
variance through the Schur-complement equivalence. -/
theorem varianceOperator_posSemidef_of_block {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G H J : Matrix ι ι ℝ} (hG : G.PosDef)
    (hH : H.IsHermitian) (hBlock : (momentBlockMatrix G H J).PosSemidef) :
    (varianceOperator G H J).PosSemidef := by
  exact varianceOperator_posSemidef hG
    ((momentBlockMatrix_posSemidef_iff_schur hG hH).mp hBlock)

/-- The variance is self-adjoint independently of its positivity proof. -/
theorem varianceOperator_isSelfAdjoint {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G H J : Matrix ι ι ℝ} (hG : G.PosDef)
    (hH : H.IsHermitian) (hJ : J.IsHermitian) :
    IsSelfAdjoint (varianceOperator G H J) := by
  exact (whitenedSecondMoment_isSelfAdjoint hG hJ).sub
    (by simpa [pow_two] using (whitenedFirstMoment_isSelfAdjoint hG hH).pow 2)

/-- Canonical positive inverse square root for the exact six-camera Gram
matrix. -/
def sixCameraInverseSqrt : Matrix (Fin 6) (Fin 6) ℝ :=
  positiveInverseSqrt sixCameraGram

/-- Canonical logarithmic operator for cameras `2, ..., 7`. -/
def sixCameraLogOperator : Matrix (Fin 6) (Fin 6) ℝ :=
  whitenedFirstMoment sixCameraGram sixCameraFirstMoment

/-- Canonical whitened second moment for cameras `2, ..., 7`. -/
def sixCameraWhitenedSecondMoment : Matrix (Fin 6) (Fin 6) ℝ :=
  whitenedSecondMoment sixCameraGram sixCameraSecondCenteredMoment

/-- Canonical variance operator for cameras `2, ..., 7`. -/
def sixCameraVariance : Matrix (Fin 6) (Fin 6) ℝ :=
  varianceOperator sixCameraGram sixCameraFirstMoment
    sixCameraSecondCenteredMoment

/-- The concrete six-camera inverse square root is positive definite. -/
theorem sixCameraInverseSqrt_posDef : sixCameraInverseSqrt.PosDef :=
  positiveInverseSqrt_posDef sixCameraGram_posDef

/-- The concrete six-camera inverse square root is self-adjoint. -/
theorem sixCameraInverseSqrt_isSelfAdjoint :
    IsSelfAdjoint sixCameraInverseSqrt :=
  positiveInverseSqrt_isSelfAdjoint sixCameraGram_posDef

/-- Exact whitening identity for the six-camera Gram matrix. -/
theorem sixCamera_whitening_identity :
    sixCameraInverseSqrt * sixCameraGram * sixCameraInverseSqrt = 1 :=
  positiveInverseSqrt_whitens sixCameraGram_posDef

/-- Equivalent packaged whitening identity for the six-camera Gram matrix. -/
theorem sixCameraWhitenedGram_eq_one :
    whitenedMatrix sixCameraGram sixCameraGram = 1 :=
  whitenedGram_eq_one sixCameraGram_posDef

/-- The source construction over period `420` recovers the canonical concrete
six-camera logarithmic operator. -/
theorem sixCameraLogOperator_source_eq :
    whitenedFirstMoment (periodicGramMatrix 420 sixCamera)
        (firstMomentMatrix 420 sixCamera) = sixCameraLogOperator := by
  rw [sixCameraGram_eq, sixCameraFirstMoment_eq]
  rfl

/-- The source construction over period `420` recovers the canonical concrete
six-camera whitened second moment. -/
theorem sixCameraWhitenedSecondMoment_source_eq :
    whitenedSecondMoment (periodicGramMatrix 420 sixCamera)
        (secondCenteredMomentMatrix 420 sixCamera) =
      sixCameraWhitenedSecondMoment := by
  rw [sixCameraGram_eq, sixCameraSecondCenteredMoment_eq]
  rfl

/-- The source construction over period `420` recovers the canonical concrete
six-camera variance. -/
theorem sixCameraVariance_source_eq :
    varianceOperator (periodicGramMatrix 420 sixCamera)
        (firstMomentMatrix 420 sixCamera)
        (secondCenteredMomentMatrix 420 sixCamera) = sixCameraVariance := by
  rw [sixCameraGram_eq, sixCameraFirstMoment_eq,
    sixCameraSecondCenteredMoment_eq]
  rfl

/-- The exact six-camera logarithmic operator is self-adjoint. -/
theorem sixCameraLogOperator_isSelfAdjoint :
    IsSelfAdjoint sixCameraLogOperator :=
  whitenedFirstMoment_isSelfAdjoint sixCameraGram_posDef
    sixCameraFirstMoment_isSelfAdjoint.isHermitian

/-- The exact six-camera whitened second moment is self-adjoint. -/
theorem sixCameraWhitenedSecondMoment_isSelfAdjoint :
    IsSelfAdjoint sixCameraWhitenedSecondMoment :=
  whitenedSecondMoment_isSelfAdjoint sixCameraGram_posDef
    sixCameraSecondCenteredMoment_isSelfAdjoint.isHermitian

/-- The exact six-camera variance satisfies the documented whitened Schur
complement identity. -/
theorem sixCameraVariance_eq_whitened_schur :
    sixCameraVariance = whitenedMatrix sixCameraGram
      (momentSchurComplement sixCameraGram sixCameraFirstMoment
        sixCameraSecondCenteredMoment) :=
  varianceOperator_eq_whitened_schur sixCameraGram_posDef

/-- The exact six-camera variance is self-adjoint. -/
theorem sixCameraVariance_isSelfAdjoint :
    IsSelfAdjoint sixCameraVariance :=
  varianceOperator_isSelfAdjoint sixCameraGram_posDef
    sixCameraFirstMoment_isSelfAdjoint.isHermitian
    sixCameraSecondCenteredMoment_isSelfAdjoint.isHermitian

end NativeCarrySpectralWeyl.Finite
