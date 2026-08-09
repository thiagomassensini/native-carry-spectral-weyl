import NativeCarrySpectralWeyl.Camera.PeriodicProfiles
import FiniteNativeCarryOperator.Operator.FiniteReal
import Mathlib.Data.Finsupp.Basic

/-!
# Formal coefficient bridge to the finite native operator

The real-plane samples at a fixed time need not be linearly independent, so
coefficients cannot be extracted from an equality in `ℝ × ℝ`.  We first build
the finite camera in the free integer module `ℕ →₀ ℤ`, then evaluate it through
the upstream `nativeState`.  This makes coefficient extraction literal while
retaining an exact theorem back to the published finite operator.
-/

open scoped BigOperators

namespace NativeCarrySpectralWeyl.Camera.FiniteBridge

open FiniteNativeCarryOperator

noncomputable section

/-- Finitely supported formal integer coefficients indexed by native position. -/
abbrev FormalStencil := ℕ →₀ ℤ

/-- One formal native sample at position `n`. -/
def atom (n : ℕ) : FormalStencil := Finsupp.single n 1

/-- Formal centered second difference at a center and radius. -/
def centeredBracketStencil (center radius : ℕ) : FormalStencil :=
  atom (center - radius) - 2 • atom center + atom (center + radius)

/-- Formal seed block, with the same exceptional C2 branch as upstream. -/
def seedStencil (camera : ℕ) : FormalStencil :=
  if camera = 2 then atom 1
  else ∑ radius ∈ Camera.radiusSet camera, atom radius

/-- Formal radius sum at one upstream aligned center. -/
def centerStencil (camera index : ℕ) : FormalStencil :=
  if camera = 2 then
    centeredBracketStencil (Camera.alignedCenter 2 index) 1
  else
    ∑ radius ∈ Camera.radiusSet camera,
      centeredBracketStencil (Camera.alignedCenter camera index) radius

/-- Formal finite native-camera stencil for exactly `cutoff` aligned centers. -/
def finiteStencil (camera cutoff : ℕ) : FormalStencil :=
  seedStencil camera +
    ∑ index ∈ Finset.range cutoff, centerStencil camera index

/-- Scalar coefficient contributed by one centered bracket at position `n`. -/
def bracketCoefficient (center radius n : ℕ) : ℤ :=
  (if center - radius = n then 1 else 0) -
    2 * (if center = n then 1 else 0) +
      (if center + radius = n then 1 else 0)

/-- Scalar seed coefficient at position `n`. -/
def seedCoefficient (camera n : ℕ) : ℤ :=
  if camera = 2 then
    if n = 1 then 1 else 0
  else
    ∑ radius ∈ Camera.radiusSet camera, if radius = n then 1 else 0

/-- Scalar coefficient contributed by one aligned center block at position `n`. -/
def centerCoefficient (camera index n : ℕ) : ℤ :=
  if camera = 2 then
    bracketCoefficient (Camera.alignedCenter 2 index) 1 n
  else
    ∑ radius ∈ Camera.radiusSet camera,
      bracketCoefficient (Camera.alignedCenter camera index) radius n

/-- Exact scalar coefficient of position `n` in the finite formal camera. -/
def finiteCoefficient (camera cutoff n : ℕ) : ℤ :=
  seedCoefficient camera n +
    ∑ index ∈ Finset.range cutoff, centerCoefficient camera index n

@[simp] theorem atom_apply (position n : ℕ) :
    atom position n = if position = n then 1 else 0 := by
  simp [atom, Finsupp.single_apply]

/-- Formal bracket evaluation at an index is its literal scalar bracket coefficient. -/
theorem centeredBracketStencil_apply (center radius n : ℕ) :
    centeredBracketStencil center radius n = bracketCoefficient center radius n := by
  simp [centeredBracketStencil, bracketCoefficient, atom_apply]

/-- Formal seed evaluation at an index is its literal scalar seed coefficient. -/
theorem seedStencil_apply (camera n : ℕ) :
    seedStencil camera n = seedCoefficient camera n := by
  by_cases h2 : camera = 2
  · subst camera
    simp [seedStencil, seedCoefficient, atom_apply, eq_comm]
  · simp [seedStencil, seedCoefficient, h2, atom_apply]

/-- Formal center evaluation at an index is its literal scalar center coefficient. -/
theorem centerStencil_apply (camera index n : ℕ) :
    centerStencil camera index n = centerCoefficient camera index n := by
  by_cases h2 : camera = 2
  · subst camera
    simp [centerStencil, centerCoefficient, centeredBracketStencil_apply]
  · simp [centerStencil, centerCoefficient, h2, centeredBracketStencil_apply]

/-- Coefficient extraction from the free stencil is exactly `finiteCoefficient`. -/
theorem finiteStencil_apply (camera cutoff n : ℕ) :
    finiteStencil camera cutoff n = finiteCoefficient camera cutoff n := by
  simp [finiteStencil, finiteCoefficient, seedStencil_apply, centerStencil_apply]

@[simp] theorem finiteStencil_zero (camera : ℕ) :
    finiteStencil camera 0 = seedStencil camera := by
  simp [finiteStencil]

/-- Adding one cutoff center adds exactly its formal center stencil. -/
theorem finiteStencil_succ (camera cutoff : ℕ) :
    finiteStencil camera (cutoff + 1) =
      finiteStencil camera cutoff + centerStencil camera cutoff := by
  simp [finiteStencil, Finset.sum_range_succ, add_assoc]

@[simp] theorem finiteCoefficient_zero (camera n : ℕ) :
    finiteCoefficient camera 0 n = seedCoefficient camera n := by
  simp [finiteCoefficient]

/-- Scalar coefficients obey the same one-center cutoff recurrence. -/
theorem finiteCoefficient_succ (camera cutoff n : ℕ) :
    finiteCoefficient camera (cutoff + 1) n =
      finiteCoefficient camera cutoff n + centerCoefficient camera cutoff n := by
  simp [finiteCoefficient, Finset.sum_range_succ, add_assoc]

/-- Evaluate formal coefficients using the upstream real-plane native state. -/
def evalStencil (time : ℝ) :
    FormalStencil →ₗ[ℤ] Operator.RealPlane :=
  Finsupp.linearCombination ℤ (Operator.nativeState time)

@[simp] theorem evalStencil_atom (time : ℝ) (n : ℕ) :
    evalStencil time (atom n) = Operator.nativeState time n := by
  simp [evalStencil, atom]

/-- Evaluation of the formal bracket is the upstream centered bracket exactly. -/
theorem evalStencil_centeredBracketStencil (time : ℝ) (center radius : ℕ) :
    evalStencil time (centeredBracketStencil center radius) =
      Operator.centeredBracket time center radius := by
  simp [centeredBracketStencil, Operator.centeredBracket]

/-- Evaluation of the formal seed block is the upstream seed block exactly. -/
theorem evalStencil_seedStencil (time : ℝ) (camera : ℕ) :
    evalStencil time (seedStencil camera) = Operator.seedSum camera time := by
  by_cases h2 : camera = 2
  · simp [seedStencil, Operator.seedSum, h2]
  · simp [seedStencil, Operator.seedSum, h2]

/-- Evaluation of one formal center block is the upstream center block exactly. -/
theorem evalStencil_centerStencil (time : ℝ) (camera index : ℕ) :
    evalStencil time (centerStencil camera index) =
      Operator.centerBracketSum camera index time := by
  by_cases h2 : camera = 2
  · subst camera
    simp [centerStencil, Operator.centerBracketSum,
      evalStencil_centeredBracketStencil]
  · simp [centerStencil, Operator.centerBracketSum, h2,
      evalStencil_centeredBracketStencil]

/-- The formal finite stencil evaluates to the pinned finite native operator. -/
theorem evalStencil_finiteStencil (time : ℝ) (camera cutoff : ℕ) :
    evalStencil time (finiteStencil camera cutoff) =
      Operator.finiteNativeOperator camera cutoff time := by
  simp [finiteStencil, Operator.finiteNativeOperator,
    evalStencil_seedStencil, evalStencil_centerStencil]

end

end NativeCarrySpectralWeyl.Camera.FiniteBridge
