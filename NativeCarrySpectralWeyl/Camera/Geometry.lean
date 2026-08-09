import NativeCarrySpectralWeyl.Camera.PeriodicProfiles

/-!
# Bridge to the finite native-camera geometry

The spectral arithmetic uses `cameraSlope`, while the finite operator stores
aligned centers and radius sets.  The statements below identify those two
descriptions without redefining the upstream camera.
-/

namespace NativeCarrySpectralWeyl.Camera

open FiniteNativeCarryOperator.Camera

/-- The spectral camera range is exactly the support range of the finite operator. -/
theorem isSupported_iff {camera : ℕ} :
    IsSupported camera ↔ 2 ≤ camera := by
  rfl

/-- Upstream aligned centers are precisely the positive multiples of the spectral slope. -/
theorem alignedCenter_eq_cameraSlope_mul (camera index : ℕ) :
    alignedCenter camera index = cameraSlope camera * (index + 1) := by
  by_cases h2 : camera = 2
  · subst camera
    simp
  · simp [alignedCenter_of_ne_two h2, cameraSlope_of_ne_two h2]

/-- Consecutive upstream centers differ by one exact camera slope. -/
theorem alignedCenter_succ (camera index : ℕ) :
    alignedCenter camera (index + 1) =
      alignedCenter camera index + cameraSlope camera := by
  rw [alignedCenter_eq_cameraSlope_mul, alignedCenter_eq_cameraSlope_mul]
  simpa [Nat.add_assoc] using Nat.mul_succ (cameraSlope camera) (index + 1)

/-- The upstream natural-camera radii are exactly `1, ..., floor(camera / 2)`. -/
theorem mem_radiusSet_iff {camera radius : ℕ} :
    radius ∈ radiusSet camera ↔ 1 ≤ radius ∧ radius ≤ camera / 2 := by
  simp [radiusSet, halfRange]

/-- A supported camera has a nonempty natural half range. -/
theorem halfRange_pos {camera : ℕ} (hcamera : IsSupported camera) :
    0 < halfRange camera := by
  simp only [IsSupported] at hcamera
  simp [halfRange]
  omega

/-- The cardinality of the upstream radius set equals the natural half range. -/
theorem card_radiusSet {camera : ℕ} (hcamera : IsSupported camera) :
    (radiusSet camera).card = halfRange camera := by
  rw [radiusSet, Nat.card_Icc]
  have hhalf := halfRange_pos hcamera
  omega

/-- Outside the exceptional aligned C2 chart, seed count is radius-set cardinality. -/
theorem seedCount_eq_card_radiusSet {camera : ℕ}
    (hcamera : IsSupported camera) (h2 : camera ≠ 2) :
    seedCount camera = (radiusSet camera).card := by
  rw [card_radiusSet hcamera]
  simp [seedCount, h2]

/-- Upstream bracket count is cutoff times the exact number of natural radii. -/
theorem bracketCount_eq_cutoff_mul_card_radiusSet {camera cutoff : ℕ}
    (hcamera : IsSupported camera) (h2 : camera ≠ 2) :
    bracketCount camera cutoff = cutoff * (radiusSet camera).card := by
  rw [card_radiusSet hcamera]
  simp [bracketCount, h2]

end NativeCarrySpectralWeyl.Camera
