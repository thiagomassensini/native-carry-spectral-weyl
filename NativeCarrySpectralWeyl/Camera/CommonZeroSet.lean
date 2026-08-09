import NativeCarrySpectralWeyl.Camera.CrossFactorization
import NativeCarrySpectralWeyl.Camera.NativeLineFloor

/-!
# Native scalar and common camera zero sets

Camera 3 has a nonvanishing factor on `-1 < re s < 1`, so its bracket
characteristic defines the native scalar there without postulating an analytic
continuation of zeta.  The continued cross identity factors every supported
camera through this scalar.  The uniform factor nonvanishing theorem then gives
the common zero set of all supported cameras on the native line.

This module proves equality of zero sets, not equality of local zero
multiplicities; multiplicity requires a separate local-order argument.
-/

open Set

namespace NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Strip where camera 3 canonically defines the native scalar. -/
def nativeScalarDomain : Set ℂ := {s | -1 < s.re ∧ s.re < 1}

theorem isOpen_nativeScalarDomain : IsOpen nativeScalarDomain := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- The camera-3 factor has no zero below `re s = 1`. -/
theorem factor_three_ne_zero_of_re_lt_one {s : ℂ} (hs : s.re < 1) :
    factor 3 s ≠ 0 := by
  rw [factor_of_odd (by omega : 3 ≠ 2) (by decide : Odd 3)]
  intro hzero
  have heq := (oddFactor_eq_zero_iff 3 s).mp hzero
  have hnorm := congrArg norm heq
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < 3)] at hnorm
  norm_num at hnorm
  have hpow : 1 < (3 : ℝ) ^ ((1 - s).re) := by
    apply Real.one_lt_rpow
    · norm_num
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
  simp only [Complex.sub_re, Complex.one_re] at hpow
  linarith

/-- Native scalar recovered from camera 3 without invoking zeta continuation. -/
def nativeScalar (s : ℂ) : ℂ :=
  bracketCharacteristic 3 s / factor 3 s

/-- Every camera factors through the native scalar on its canonical strip. -/
theorem bracketCharacteristic_eq_factor_mul_nativeScalar {camera : ℕ}
    (hcamera : 2 ≤ camera) {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    bracketCharacteristic camera s = factor camera s * nativeScalar s := by
  have hdomain : s ∈ bracketDomain := hs.1
  have hthree : factor 3 s ≠ 0 := factor_three_ne_zero_of_re_lt_one hs.2
  have hcross := bracketCharacteristic_cross_eq hcamera hdomain
  unfold nativeScalar
  rw [← mul_div_assoc]
  apply (eq_div_iff hthree).2
  simpa only [mul_comm] using hcross

/-- The native scalar is holomorphic on `-1 < re s < 1`. -/
theorem nativeScalar_differentiableOn :
    DifferentiableOn ℂ nativeScalar nativeScalarDomain := by
  apply DifferentiableOn.div
  · exact (bracketCharacteristic_differentiableOn (by omega : 2 ≤ 3)).mono
      (fun _ hs => hs.1)
  · exact (factor_differentiable (by omega : 2 ≤ 3)).differentiableOn
  · intro s hs
    exact factor_three_ne_zero_of_re_lt_one hs.2

/-- Every supported camera has exactly the native scalar's zeros on the native line. -/
theorem bracketCharacteristic_nativeLine_eq_zero_iff {camera : ℕ}
    (hcamera : 2 ≤ camera) (t : ℝ) :
    bracketCharacteristic camera (nativeLine t) = 0 ↔
      nativeScalar (nativeLine t) = 0 := by
  have hstrip : nativeLine t ∈ nativeScalarDomain := by
    simp [nativeScalarDomain]
    norm_num
  rw [bracketCharacteristic_eq_factor_mul_nativeScalar hcamera hstrip]
  exact mul_eq_zero.trans (or_iff_right (factor_nativeLine_ne_zero hcamera t))

/-- Any two supported camera characteristics have the same native-line zero set. -/
theorem bracketCharacteristic_nativeLine_common_zero {camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂) (t : ℝ) :
    bracketCharacteristic camera₁ (nativeLine t) = 0 ↔
      bracketCharacteristic camera₂ (nativeLine t) = 0 := by
  rw [bracketCharacteristic_nativeLine_eq_zero_iff hcamera₁,
    bracketCharacteristic_nativeLine_eq_zero_iff hcamera₂]

end

end NativeCarrySpectralWeyl.Camera
