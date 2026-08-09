import NativeCarrySpectralWeyl.Camera.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Explicit native-camera factors

This module records the exact complex multipliers from the source derivation.
Their analytic factorization and uniform lower bound are separate theorem
obligations; introducing the formulas here does not assume either result.
-/

namespace NativeCarrySpectralWeyl.Camera

noncomputable section

/-- The native spectral line, with angular parameter kept independent of all defect probes. -/
def nativeLine (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- Explicit factor of the exceptional aligned C2 chart. -/
def c2Factor (s : ℂ) : ℂ :=
  (1 + (2 : ℂ) ^ (-s)) * (1 - (2 : ℂ) ^ (1 - s))

/-- Explicit factor of a natural odd camera. -/
def oddFactor (camera : ℕ) (s : ℂ) : ℂ :=
  1 - (camera : ℂ) ^ (1 - s)

/-- Explicit factor of a natural even camera. -/
def evenFactor (camera : ℕ) (s : ℂ) : ℂ :=
  1 + (camera / 2 : ℕ) ^ (-s) - (camera + 2 : ℕ) * (camera : ℂ) ^ (-s)

/-- Unified explicit camera factor `A_camera(s)`. -/
def factor (camera : ℕ) (s : ℂ) : ℂ :=
  if camera = 2 then c2Factor s
  else if Odd camera then oddFactor camera s
  else evenFactor camera s

@[simp] theorem nativeLine_re (t : ℝ) : (nativeLine t).re = 1 / 2 := by
  simp [nativeLine]

@[simp] theorem nativeLine_im (t : ℝ) : (nativeLine t).im = t := by
  simp [nativeLine]

@[simp] theorem factor_two (s : ℂ) : factor 2 s = c2Factor s := by
  simp [factor]

theorem factor_of_odd {camera : ℕ} (h2 : camera ≠ 2) (hodd : Odd camera) (s : ℂ) :
    factor camera s = oddFactor camera s := by
  simp [factor, h2, hodd]

theorem factor_of_even {camera : ℕ} (h2 : camera ≠ 2) (heven : Even camera) (s : ℂ) :
    factor camera s = evenFactor camera s := by
  simp [factor, h2, (Nat.not_odd_iff_even.mpr heven)]

/-- The aligned C2 factor splits into its two explicit nonvanishing obligations. -/
theorem c2Factor_ne_zero_iff (s : ℂ) :
    c2Factor s ≠ 0 ↔
      1 + (2 : ℂ) ^ (-s) ≠ 0 ∧ 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
  simp [c2Factor]

/-- An odd-camera factor vanishes exactly when its complex power equals one. -/
theorem oddFactor_eq_zero_iff (camera : ℕ) (s : ℂ) :
    oddFactor camera s = 0 ↔ (camera : ℂ) ^ (1 - s) = 1 := by
  unfold oddFactor
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    exact sub_eq_zero.mpr h.symm

end

end NativeCarrySpectralWeyl.Camera
