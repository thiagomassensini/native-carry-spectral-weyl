import NativeCarrySpectralWeyl.Camera.Factors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Camera-factor bounds on the native line

The first quantitative step is to compute the norms of the complex powers
exactly on `re s = 1/2`.  The exceptional C2 and odd-camera lower bounds then
follow from the reverse triangle inequality.
-/

namespace NativeCarrySpectralWeyl.Camera

noncomputable section

/-- On the native line, the positive power `b^(1-s)` has norm `sqrt b`. -/
theorem norm_cpow_one_sub_nativeLine {camera : ℕ} (hcamera : 0 < camera) (t : ℝ) :
    ‖(camera : ℂ) ^ (1 - nativeLine t)‖ = Real.sqrt camera := by
  rw [Complex.norm_natCast_cpow_of_pos hcamera]
  rw [Complex.sub_re, Complex.one_re, nativeLine_re]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  exact Real.sqrt_eq_rpow camera |>.symm

/-- On the native line, the reciprocal power `b^(-s)` has norm `1 / sqrt b`. -/
theorem norm_cpow_neg_nativeLine {camera : ℕ} (hcamera : 0 < camera) (t : ℝ) :
    ‖(camera : ℂ) ^ (-nativeLine t)‖ = (Real.sqrt camera)⁻¹ := by
  rw [Complex.cpow_neg, norm_inv, Complex.norm_natCast_cpow_of_pos hcamera,
    nativeLine_re, ← Real.sqrt_eq_rpow]

/-- Odd-camera factors satisfy their exact reverse-triangle lower bound. -/
theorem oddFactor_nativeLine_lower {camera : ℕ} (hcamera : 0 < camera) (t : ℝ) :
    Real.sqrt camera - 1 ≤ ‖oddFactor camera (nativeLine t)‖ := by
  have hnorm := norm_cpow_one_sub_nativeLine hcamera t
  calc
    Real.sqrt camera - 1 =
        ‖(camera : ℂ) ^ (1 - nativeLine t)‖ - ‖(1 : ℂ)‖ := by simp [hnorm]
    _ ≤ ‖(camera : ℂ) ^ (1 - nativeLine t) - 1‖ :=
      norm_sub_norm_le _ _
    _ = ‖oddFactor camera (nativeLine t)‖ := by
      rw [norm_sub_rev]
      rfl

/-- The odd-camera lower bound is strictly positive for every natural odd camera. -/
theorem oddFactor_nativeLine_lower_pos {camera : ℕ} (hcamera : 3 ≤ camera) :
    0 < Real.sqrt camera - 1 := by
  have hsqrt_sq : (Real.sqrt camera) ^ 2 = camera :=
    Real.sq_sqrt (Nat.cast_nonneg camera)
  have hcast : (3 : ℝ) ≤ camera := by exact_mod_cast hcamera
  nlinarith [Real.sqrt_nonneg (camera : ℝ)]

/-- Every natural odd-camera factor is nonzero on the native line. -/
theorem oddFactor_nativeLine_ne_zero {camera : ℕ} (hcamera : 3 ≤ camera) (t : ℝ) :
    oddFactor camera (nativeLine t) ≠ 0 := by
  have hlower := oddFactor_nativeLine_lower (lt_of_lt_of_le (by omega) hcamera) t
  have hpos := oddFactor_nativeLine_lower_pos hcamera
  intro hzero
  rw [hzero, norm_zero] at hlower
  linarith

/-- The universal constant dictated by the exceptional aligned C2 chart. -/
def universalFloor : ℝ :=
  (1 - (Real.sqrt 2)⁻¹) * (Real.sqrt 2 - 1)

/-- The universal floor in the alternate closed form recorded by the source derivation. -/
theorem universalFloor_eq_sq_div_sqrt :
    universalFloor = (Real.sqrt 2 - 1) ^ 2 / Real.sqrt 2 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  unfold universalFloor
  field_simp

/-- The aligned C2 factor satisfies the universal lower bound on the native line. -/
theorem c2Factor_nativeLine_lower (t : ℝ) :
    universalFloor ≤ ‖c2Factor (nativeLine t)‖ := by
  have hneg : ‖(2 : ℂ) ^ (-nativeLine t)‖ = (Real.sqrt 2)⁻¹ := by
    simpa using norm_cpow_neg_nativeLine (camera := 2) (by norm_num) t
  have hpos : ‖(2 : ℂ) ^ (1 - nativeLine t)‖ = Real.sqrt 2 := by
    simpa using norm_cpow_one_sub_nativeLine (camera := 2) (by norm_num) t
  have hfirst :
      1 - (Real.sqrt 2)⁻¹ ≤ ‖1 + (2 : ℂ) ^ (-nativeLine t)‖ := by
    calc
      1 - (Real.sqrt 2)⁻¹ =
          ‖(1 : ℂ)‖ - ‖(2 : ℂ) ^ (-nativeLine t)‖ := by simp [hneg]
      _ ≤ ‖(1 : ℂ) + (2 : ℂ) ^ (-nativeLine t)‖ :=
        norm_sub_le_norm_add _ _
  have hsecond :
      Real.sqrt 2 - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - nativeLine t)‖ := by
    calc
      Real.sqrt 2 - 1 =
          ‖(2 : ℂ) ^ (1 - nativeLine t)‖ - ‖(1 : ℂ)‖ := by simp [hpos]
      _ ≤ ‖(2 : ℂ) ^ (1 - nativeLine t) - 1‖ :=
        norm_sub_norm_le _ _
      _ = ‖(1 : ℂ) - (2 : ℂ) ^ (1 - nativeLine t)‖ := norm_sub_rev _ _
  have hsqrt : 0 ≤ Real.sqrt 2 - 1 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  calc
    universalFloor ≤
        ‖1 + (2 : ℂ) ^ (-nativeLine t)‖ *
          ‖1 - (2 : ℂ) ^ (1 - nativeLine t)‖ := by
      exact mul_le_mul hfirst hsecond hsqrt (norm_nonneg _)
    _ = ‖c2Factor (nativeLine t)‖ := by
      rw [c2Factor, norm_mul]

/-- The universal C2 floor is strictly positive. -/
theorem universalFloor_pos : 0 < universalFloor := by
  have hsqrt : 1 < Real.sqrt 2 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hinv : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsqrt
  exact mul_pos (sub_pos.mpr hinv) (sub_pos.mpr hsqrt)

/-- The exceptional aligned C2 factor is nonzero everywhere on the native line. -/
theorem c2Factor_nativeLine_ne_zero (t : ℝ) : c2Factor (nativeLine t) ≠ 0 := by
  have hlower := c2Factor_nativeLine_lower t
  have hfloor := universalFloor_pos
  intro hzero
  rw [hzero, norm_zero] at hlower
  linarith

/-- The universal C2 constant is at most one. -/
theorem universalFloor_le_one : universalFloor ≤ 1 := by
  have hsqrt_lower : 1 ≤ Real.sqrt 2 := by
    exact Real.one_le_sqrt.mpr (by norm_num)
  have hsqrt_upper : Real.sqrt 2 ≤ 2 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hinv_nonneg : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  have hfirst : 1 - (Real.sqrt 2)⁻¹ ≤ 1 := by linarith
  have hsecond : Real.sqrt 2 - 1 ≤ 1 := by linarith
  have hsecond_nonneg : 0 ≤ Real.sqrt 2 - 1 := by linarith
  calc
    universalFloor ≤ 1 * 1 := by
      exact mul_le_mul hfirst hsecond hsecond_nonneg (by norm_num)
    _ = 1 := by norm_num

/-- Every supported natural even-camera factor has the coarse uniform bound one. -/
theorem evenFactor_nativeLine_lower_one {camera : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) (t : ℝ) :
    1 ≤ ‖evenFactor camera (nativeLine t)‖ := by
  obtain ⟨k, rfl⟩ := heven
  have hk : 2 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have hcameraPos : 0 < k + k := by omega
  have hhalf : (k + k) / 2 = k := by omega
  have hhalfNorm :
      ‖(k : ℂ) ^ (-nativeLine t)‖ = (Real.sqrt k)⁻¹ :=
    norm_cpow_neg_nativeLine hkpos t
  have hfullNorm :
      ‖((k + k : ℕ) : ℂ) ^ (-nativeLine t)‖ =
        (Real.sqrt ((k + k : ℕ) : ℝ))⁻¹ := by
    simpa using norm_cpow_neg_nativeLine hcameraPos t
  have hkSqrt : 1 ≤ Real.sqrt k := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ k by omega))
  have hkInv : (Real.sqrt k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hkSqrt
  have hsmall :
      ‖(1 : ℂ) + (k : ℂ) ^ (-nativeLine t)‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) + (k : ℂ) ^ (-nativeLine t)‖ ≤
          ‖(1 : ℂ)‖ + ‖(k : ℂ) ^ (-nativeLine t)‖ := norm_add_le _ _
      _ = 1 + (Real.sqrt k)⁻¹ := by rw [norm_one, hhalfNorm]
      _ ≤ 2 := by linarith
  let x : ℝ := Real.sqrt ((k + k : ℕ) : ℝ)
  have hx2 : 2 ≤ x := by
    dsimp [x]
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg (k + k))).2
    exact_mod_cast hcamera
  have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx2)
  have hxsq : x ^ 2 = (k + k : ℕ) := by
    dsimp [x]
    exact Real.sq_sqrt (Nat.cast_nonneg (k + k))
  have hnum : 3 * x ≤ (k + k + 2 : ℕ) := by
    have hprod : 0 ≤ (x - 1) * (x - 2) :=
      mul_nonneg (by linarith) (by linarith)
    norm_num at hxsq ⊢
    nlinarith
  have hinv_nonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr (by linarith)
  have hlargeScalar : 3 ≤ (k + k + 2 : ℕ) * x⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hnum hinv_nonneg
    rw [mul_assoc, mul_inv_cancel₀ hxne, mul_one] at hmul
    exact hmul
  have hlargeNorm :
      3 ≤ ‖((k + k + 2 : ℕ) : ℂ) *
        ((k + k : ℕ) : ℂ) ^ (-nativeLine t)‖ := by
    rw [norm_mul, norm_natCast, hfullNorm]
    exact hlargeScalar
  calc
    1 ≤
        ‖((k + k + 2 : ℕ) : ℂ) *
            ((k + k : ℕ) : ℂ) ^ (-nativeLine t)‖ -
          ‖(1 : ℂ) + (k : ℂ) ^ (-nativeLine t)‖ := by linarith
    _ ≤ ‖((k + k + 2 : ℕ) : ℂ) *
          ((k + k : ℕ) : ℂ) ^ (-nativeLine t) -
        ((1 : ℂ) + (k : ℂ) ^ (-nativeLine t))‖ := norm_sub_norm_le _ _
    _ = ‖evenFactor (k + k) (nativeLine t)‖ := by
      rw [evenFactor, hhalf, norm_sub_rev]

/-- Natural even cameras dominate the universal aligned-C2 floor. -/
theorem evenFactor_nativeLine_lower {camera : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) (t : ℝ) :
    universalFloor ≤ ‖evenFactor camera (nativeLine t)‖ :=
  universalFloor_le_one.trans (evenFactor_nativeLine_lower_one hcamera heven t)

/-- Every supported natural even-camera factor is nonzero on the native line. -/
theorem evenFactor_nativeLine_ne_zero {camera : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) (t : ℝ) :
    evenFactor camera (nativeLine t) ≠ 0 := by
  have hlower := evenFactor_nativeLine_lower hcamera heven t
  have hfloor := universalFloor_pos
  intro hzero
  rw [hzero, norm_zero] at hlower
  linarith

/-- A convenient rational upper bound for the universal C2 constant. -/
theorem universalFloor_le_half : universalFloor ≤ 1 / 2 := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_upper : Real.sqrt 2 ≤ 2 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hinv_lower : (1 / 2 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by
    rw [one_div]
    exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hsqrt_pos).mpr hsqrt_upper
  have hfirst : 1 - (Real.sqrt 2)⁻¹ ≤ 1 / 2 := by linarith
  have hsecond : Real.sqrt 2 - 1 ≤ 1 := by linarith
  have hsecond_nonneg : 0 ≤ Real.sqrt 2 - 1 := by
    have := Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  calc
    universalFloor ≤ (1 / 2 : ℝ) * 1 := by
      exact mul_le_mul hfirst hsecond hsecond_nonneg (by norm_num)
    _ = 1 / 2 := by ring

/-- Natural odd cameras also dominate the universal aligned-C2 floor. -/
theorem oddFactor_nativeLine_uniform_lower {camera : ℕ}
    (hcamera : 3 ≤ camera) (t : ℝ) :
    universalFloor ≤ ‖oddFactor camera (nativeLine t)‖ := by
  have hsquare : (Real.sqrt camera) ^ 2 = camera :=
    Real.sq_sqrt (Nat.cast_nonneg camera)
  have hcast : (3 : ℝ) ≤ camera := by exact_mod_cast hcamera
  have hsqrt_nonneg := Real.sqrt_nonneg (camera : ℝ)
  have hsqrt : (3 / 2 : ℝ) ≤ Real.sqrt camera := by
    nlinarith
  calc
    universalFloor ≤ 1 / 2 := universalFloor_le_half
    _ ≤ Real.sqrt camera - 1 := by linarith
    _ ≤ ‖oddFactor camera (nativeLine t)‖ :=
      oddFactor_nativeLine_lower (lt_of_lt_of_le (by omega) hcamera) t

/-- Uniform all-camera floor on the native line. -/
theorem factor_nativeLine_lower {camera : ℕ} (hcamera : 2 ≤ camera) (t : ℝ) :
    universalFloor ≤ ‖factor camera (nativeLine t)‖ := by
  by_cases h2 : camera = 2
  · subst camera
    simpa using c2Factor_nativeLine_lower t
  · rcases Nat.even_or_odd camera with heven | hodd
    · have h4 : 4 ≤ camera := by
        obtain ⟨k, hk⟩ := heven
        omega
      rw [factor_of_even h2 heven]
      exact evenFactor_nativeLine_lower h4 heven t
    · have h3 : 3 ≤ camera := by omega
      rw [factor_of_odd h2 hodd]
      exact oddFactor_nativeLine_uniform_lower h3 t

/-- Every supported native-camera factor is nonzero on the native line. -/
theorem factor_nativeLine_ne_zero {camera : ℕ} (hcamera : 2 ≤ camera) (t : ℝ) :
    factor camera (nativeLine t) ≠ 0 := by
  have hlower := factor_nativeLine_lower hcamera t
  have hfloor := universalFloor_pos
  intro hzero
  rw [hzero, norm_zero] at hlower
  linarith

end

end NativeCarrySpectralWeyl.Camera
