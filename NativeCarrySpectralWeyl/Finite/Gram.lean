import NativeCarrySpectralWeyl.Camera.PeriodicProfiles
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Finite native-camera Gram matrices

This file formalizes the first finite spectral package from the research notes.
For a finite family of cameras it defines the periodic product mean

`m(b,c) = (1 / P) * sum (a_b(r) * a_c(r)),  0 <= r < P`,

and the slope-weighted Gram matrix

`G(b,c) = min(ell_b, ell_c) * m(b,c)`.

The periodic mean matrix is a normalized sum of rank-one matrices.  The slope
minimum matrix is likewise a sum of rank-one level indicators.  Their
entrywise product is therefore positive semidefinite by the Schur product
theorem.  For the six cameras `2, ..., 7`, the common period `420` gives the
exact rational matrix recorded in the source notes; its determinant is
`4_981_760`, so the matrix is positive definite.
-/

open scoped BigOperators Matrix

noncomputable section

namespace NativeCarrySpectralWeyl.Finite

open NativeCarrySpectralWeyl.Camera

/-- A chosen period is common to a camera family when every camera slope
divides it. -/
def IsCommonProfilePeriod {ι : Type*} (period : ℕ) (camera : ι → ℕ) : Prop :=
  ∀ i, cameraSlope (camera i) ∣ period

/-- A supported profile is invariant under translation by every multiple of
its exact spectral slope. -/
theorem profile_add_commonPeriod {camera period : ℕ} (hcamera : 2 ≤ camera)
    (hperiod : cameraSlope camera ∣ period) (n : ℕ) :
    profile camera (n + period) = profile camera n := by
  obtain ⟨k, rfl⟩ := hperiod
  have hperiodic : Function.Periodic (profile camera) (cameraSlope camera) :=
    profile_add_period hcamera
  simpa [Nat.mul_comm] using (hperiodic.nat_mul k n)

/-- The overlap count of two initial level intervals is their minimum. -/
theorem sum_indicator_eq_min {a b bound : ℕ} (ha : a ≤ bound) :
    ∑ x ∈ Finset.range bound,
        (if x < a then (1 : ℝ) else 0) * (if x < b then 1 else 0) =
      (min a b : ℕ) := by
  let f : ℕ → ℝ := fun x =>
    (if x < a then 1 else 0) * (if x < b then 1 else 0)
  have hsub : Finset.range a ∩ Finset.range b ⊆ Finset.range bound := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_range] at hx ⊢
    omega
  have hsum :
      ∑ x ∈ Finset.range a ∩ Finset.range b, f x =
        ∑ x ∈ Finset.range bound, f x :=
    Finset.sum_subset hsub (fun x _ hxNotInter => by
      by_cases hxa : x < a
      · have hxb : ¬x < b := by
          intro hxb
          exact hxNotInter (by simp [hxa, hxb])
        simp [f, hxb]
      · simp [f, hxa])
  rw [← hsum, Finset.range_inter_range]
  have hinside : ∀ x ∈ Finset.range (min a b), f x = 1 := by
    intro x hx
    have hx' : x < min a b := Finset.mem_range.mp hx
    simp [f, lt_of_lt_of_le hx' (min_le_left _ _),
      lt_of_lt_of_le hx' (min_le_right _ _)]
  rw [Finset.sum_congr rfl hinside]
  simp

/-- Rank-one level vector used to realize the minimum kernel. -/
def slopeLevelVector {ι : Type*} (slope : ι → ℕ) (level : ℕ) : ι → ℝ :=
  fun i => if level < slope i then 1 else 0

/-- The slope minimum kernel on a camera index family. -/
def slopeMinMatrix {ι : Type*} (slope : ι → ℕ) : Matrix ι ι ℝ :=
  fun i j => min (slope i) (slope j)

private theorem slopeMinMatrix_posSemidef_of_bound {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) (bound : ℕ) (hbound : ∀ i, slope i ≤ bound) :
    (slopeMinMatrix slope).PosSemidef := by
  classical
  have heq : slopeMinMatrix slope =
      ∑ level ∈ Finset.range bound,
        Matrix.vecMulVec (slopeLevelVector slope level)
          (star (slopeLevelVector slope level)) := by
    ext i j
    simp only [slopeMinMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply,
      star_trivial]
    simpa [slopeLevelVector] using
      (sum_indicator_eq_min (a := slope i) (b := slope j) (hbound i)).symm
  rw [heq]
  exact Matrix.posSemidef_sum (Finset.range bound) fun level _ =>
    Matrix.posSemidef_vecMulVec_self_star (slopeLevelVector slope level)

/-- The minimum of any finite family of natural slopes is a positive
semidefinite kernel. -/
theorem slopeMinMatrix_posSemidef {ι : Type*} [Fintype ι]
    (slope : ι → ℕ) : (slopeMinMatrix slope).PosSemidef := by
  classical
  apply slopeMinMatrix_posSemidef_of_bound slope (∑ i, slope i)
  intro i
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (slope j))
    (Finset.mem_univ i)

/-- Integer product sum of two camera profiles over a chosen period. -/
def periodicProductSum (period camera₁ camera₂ : ℕ) : ℤ :=
  ∑ residue ∈ Finset.range period,
    profile camera₁ residue * profile camera₂ residue

/-- Normalized real product mean of two camera profiles. -/
def periodicProductMean (period camera₁ camera₂ : ℕ) : ℝ :=
  (period : ℝ)⁻¹ * periodicProductSum period camera₁ camera₂

/-- Vector of camera-profile values at one residue. -/
def profileVector {ι : Type*} (camera : ι → ℕ) (residue : ℕ) : ι → ℝ :=
  fun i => profile (camera i) residue

/-- Periodic product-mean matrix as a normalized sum of rank-one matrices. -/
def periodicMeanMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  (period : ℝ)⁻¹ • ∑ residue ∈ Finset.range period,
    Matrix.vecMulVec (profileVector camera residue)
      (star (profileVector camera residue))

/-- Entry formula for the periodic product-mean matrix. -/
theorem periodicMeanMatrix_apply {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    periodicMeanMatrix period camera i j =
      periodicProductMean period (camera i) (camera j) := by
  simp only [periodicMeanMatrix, periodicProductMean, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial, profileVector,
    smul_eq_mul, periodicProductSum, Int.cast_sum, Int.cast_mul]

/-- Every finite periodic product-mean matrix is positive semidefinite. -/
theorem periodicMeanMatrix_posSemidef {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (periodicMeanMatrix period camera).PosSemidef := by
  classical
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_sum (Finset.range period) fun residue _ =>
      Matrix.posSemidef_vecMulVec_self_star (profileVector camera residue)
  · positivity

/-- Slope-weighted finite periodic camera Gram matrix. -/
def periodicGramMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  slopeMinMatrix (fun i => cameraSlope (camera i)) ⊙
    periodicMeanMatrix period camera

/-- Entry formula `G(b,c) = min(ell_b,ell_c) * m(b,c)`. -/
theorem periodicGramMatrix_apply {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    periodicGramMatrix period camera i j =
      (min (cameraSlope (camera i)) (cameraSlope (camera j)) : ℕ) *
        periodicProductMean period (camera i) (camera j) := by
  rw [periodicGramMatrix, Matrix.hadamard_apply, periodicMeanMatrix_apply]
  simp [slopeMinMatrix]

/-- The slope-weighted Gram matrix of every finite camera family is positive
semidefinite. -/
theorem periodicGramMatrix_posSemidef {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (periodicGramMatrix period camera).PosSemidef := by
  exact (slopeMinMatrix_posSemidef _).hadamard
    (periodicMeanMatrix_posSemidef period camera)

/-- Camera index list `2, 3, 4, 5, 6, 7`. -/
def sixCamera (i : Fin 6) : ℕ :=
  i + 2

/-- Exact six-camera Gram matrix over the rationals. -/
def sixCameraGramRat : Matrix (Fin 6) (Fin 6) ℚ :=
  !![6, 0, 10, 0, 16 / 3, 0;
     0, 6, 0, 0, 6, 0;
     10, 0, 22, 0, 16 / 3, 0;
     0, 0, 0, 20, 0, 0;
     16 / 3, 6, 16 / 3, 0, 44, 0;
     0, 0, 0, 0, 0, 42]

/-- Exact six-camera Gram matrix over the reals. -/
def sixCameraGram : Matrix (Fin 6) (Fin 6) ℝ :=
  (Rat.castHom ℝ).mapMatrix sixCameraGramRat

/-- Unit lower-triangular factor in an exact `L D Lᵀ` certificate for the
six-camera rational Gram matrix. -/
def sixCameraLDLLower : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     5 / 3, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     8 / 9, 1, -2 / 3, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Positive diagonal factor in the exact six-camera `L D Lᵀ` certificate. -/
def sixCameraLDDiagonal : Matrix (Fin 6) (Fin 6) ℚ :=
  Matrix.diagonal ![6, 6, 16 / 3, 20, 278 / 9, 42]

private theorem sixCameraGramRat_ldl :
    sixCameraGramRat =
      sixCameraLDLLower * sixCameraLDDiagonal * sixCameraLDLLowerᵀ := by
  ext i j
  simp only [sixCameraLDDiagonal, Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraGramRat, sixCameraLDLLower, Matrix.diagonal_apply,
      Fin.sum_univ_succ]

private theorem sixCameraLDLLower_det : sixCameraLDLLower.det = 1 := by
  have htri : sixCameraLDLLower.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    fin_cases i <;> fin_cases j <;> simp_all [sixCameraLDLLower]
  rw [Matrix.det_of_lowerTriangular sixCameraLDLLower htri]
  norm_num [sixCameraLDLLower, Fin.prod_univ_succ]

private theorem sixCameraLDDiagonal_det :
    sixCameraLDDiagonal.det = 4_981_760 := by
  rw [sixCameraLDDiagonal, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

/-- Unnormalized integer product sums over the common period `420`. -/
def sixCameraProductSum : Matrix (Fin 6) (Fin 6) ℤ :=
  !![630, 0, 1050, 0, 560, 0;
     0, 840, 0, 0, 840, 0;
     1050, 0, 2310, 0, 560, 0;
     0, 0, 0, 1680, 0, 0;
     560, 840, 560, 0, 3080, 0;
     0, 0, 0, 0, 0, 2520]

/-- `420` is a common profile period for cameras `2, ..., 7`. -/
theorem sixCamera_commonPeriod : IsCommonProfilePeriod 420 sixCamera := by
  intro i
  fin_cases i <;> norm_num [sixCamera, cameraSlope]

/-- Exact integer profile-product certificate for cameras `2, ..., 7`. -/
theorem sixCameraProductSum_eq :
    (fun i j => periodicProductSum 420 (sixCamera i) (sixCamera j)) =
      sixCameraProductSum := by
  set_option maxRecDepth 100_000 in
  decide

/-- The period-`420` slope-weighted construction equals the exact matrix in
the research notes. -/
theorem sixCameraGram_eq :
    periodicGramMatrix 420 sixCamera = sixCameraGram := by
  ext i j
  rw [periodicGramMatrix_apply]
  have hsum := congr_fun (congr_fun sixCameraProductSum_eq i) j
  simp only [periodicProductMean]
  rw [hsum]
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCamera, sixCameraGram, sixCameraProductSum,
      sixCameraGramRat, cameraSlope]

/-- Exact determinant of the six-camera Gram matrix. -/
theorem sixCameraGram_det : sixCameraGram.det = 4_981_760 := by
  have hdet : sixCameraGramRat.det = (4_981_760 : ℚ) := by
    rw [sixCameraGramRat_ldl, Matrix.det_mul, Matrix.det_mul,
      sixCameraLDLLower_det, sixCameraLDDiagonal_det, Matrix.det_transpose,
      sixCameraLDLLower_det]
    norm_num
  rw [sixCameraGram]
  change (sixCameraGramRat.map fun x => (x : ℝ)).det = _
  rw [← Rat.cast_det, hdet]
  norm_num

/-- Positive semidefiniteness of the exact six-camera matrix. -/
theorem sixCameraGram_posSemidef : sixCameraGram.PosSemidef := by
  rw [← sixCameraGram_eq]
  exact periodicGramMatrix_posSemidef 420 sixCamera

/-- Positive definiteness of the exact Gram matrix for cameras `2, ..., 7`. -/
theorem sixCameraGram_posDef : sixCameraGram.PosDef := by
  rw [sixCameraGram_posSemidef.posDef_iff_det_ne_zero]
  rw [sixCameraGram_det]
  norm_num

end NativeCarrySpectralWeyl.Finite
