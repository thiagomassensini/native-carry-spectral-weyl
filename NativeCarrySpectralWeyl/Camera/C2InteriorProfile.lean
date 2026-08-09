import NativeCarrySpectralWeyl.Camera.FiniteCoefficientBridge

/-!
# Exact finite-to-periodic bridge for the aligned C2 camera

The C2 finite stencil is proved coefficientwise equal to its periodic profile
on the entire emitted window `1 ≤ n ≤ 4 * cutoff + 1`, and zero outside it.
-/

namespace NativeCarrySpectralWeyl.Camera.FiniteBridge

open FiniteNativeCarryOperator

noncomputable section

private theorem seedCoefficient_two (n : ℕ) :
    seedCoefficient 2 n = if n = 1 then 1 else 0 := by
  rw [seedCoefficient, if_pos rfl]

/-- One aligned C2 center contributes only at its two legs and center. -/
theorem c2_centerCoefficient (index n : ℕ) :
    centerCoefficient 2 index n =
      if n = 4 * (index + 1) - 1 then 1
      else if n = 4 * (index + 1) then -2
      else if n = 4 * (index + 1) + 1 then 1 else 0 := by
  simp [centerCoefficient, bracketCoefficient, Camera.alignedCenter]
  split_ifs <;> omega

private theorem c2Profile_four_mul_add_two (index : ℕ) :
    c2Profile (4 * index + 2) = 0 := by
  have h2 : 2 ∣ 4 * index + 2 := by omega
  have h4 : ¬4 ∣ 4 * index + 2 := by omega
  simp [c2Profile, dvdIndicator, h2, h4]

private theorem c2Profile_four_mul_add_three (index : ℕ) :
    c2Profile (4 * index + 3) = 1 := by
  have h2 : ¬2 ∣ 4 * index + 3 := by omega
  have h4 : ¬4 ∣ 4 * index + 3 := by omega
  simp [c2Profile, dvdIndicator, h2, h4]

private theorem c2Profile_four_mul_add_four (index : ℕ) :
    c2Profile (4 * index + 4) = -2 := by
  have h2 : 2 ∣ 4 * index + 4 := by omega
  have h4 : 4 ∣ 4 * index + 4 := by omega
  simp [c2Profile, dvdIndicator, h2, h4]

private theorem c2Profile_four_mul_add_five (index : ℕ) :
    c2Profile (4 * index + 5) = 1 := by
  have h2 : ¬2 ∣ 4 * index + 5 := by omega
  have h4 : ¬4 ∣ 4 * index + 5 := by omega
  simp [c2Profile, dvdIndicator, h2, h4]

/-- Complete coefficient formula for every finite aligned C2 cutoff. -/
theorem c2_finiteCoefficient_eq_profile_window (cutoff n : ℕ) :
    finiteCoefficient 2 cutoff n =
      if 1 ≤ n ∧ n ≤ 4 * cutoff + 1 then c2Profile n else 0 := by
  induction cutoff with
  | zero =>
      simp only [finiteCoefficient_zero]
      rw [seedCoefficient_two]
      by_cases hn : n = 1
      · subst n
        norm_num [c2Profile, dvdIndicator]
      · have hout : ¬(1 ≤ n ∧ n ≤ 4 * 0 + 1) := by omega
        simp [hn, hout]
  | succ cutoff ih =>
      rw [finiteCoefficient_succ, ih, c2_centerCoefficient]
      by_cases hold : 1 ≤ n ∧ n ≤ 4 * cutoff + 1
      · have hext : 1 ≤ n ∧ n ≤ 4 * (cutoff + 1) + 1 := by omega
        have hleft : n ≠ 4 * (cutoff + 1) - 1 := by omega
        have hcenter : n ≠ 4 * (cutoff + 1) := by omega
        have hright : n ≠ 4 * (cutoff + 1) + 1 := by omega
        simp [hold, hext, hleft, hcenter, hright]
      · by_cases hext : 1 ≤ n ∧ n ≤ 4 * (cutoff + 1) + 1
        · have hcases :
            n = 4 * cutoff + 2 ∨ n = 4 * cutoff + 3 ∨
              n = 4 * cutoff + 4 ∨ n = 4 * cutoff + 5 := by
            omega
          rcases hcases with h2 | h3 | h4 | h5
          · subst n
            simp [hext, c2Profile_four_mul_add_two]
            omega
          · subst n
            simp [hext, c2Profile_four_mul_add_three]
            omega
          · subst n
            simp [hext, c2Profile_four_mul_add_four]
            omega
          · subst n
            simp [hext, c2Profile_four_mul_add_five]
            omega
        · have hleft : n ≠ 4 * (cutoff + 1) - 1 := by omega
          have hcenter : n ≠ 4 * (cutoff + 1) := by omega
          have hright : n ≠ 4 * (cutoff + 1) + 1 := by omega
          simp [hold, hext, hleft, hcenter, hright]

/-- Inside the emitted C2 window, the extracted finite coefficient is the profile. -/
theorem c2_finiteCoefficient_eq_profile {cutoff n : ℕ}
    (hn : 1 ≤ n) (hupper : n ≤ 4 * cutoff + 1) :
    finiteCoefficient 2 cutoff n = c2Profile n := by
  rw [c2_finiteCoefficient_eq_profile_window]
  simp [hn, hupper]

/-- Outside the emitted C2 window, the extracted finite coefficient vanishes. -/
theorem c2_finiteCoefficient_eq_zero_of_outside {cutoff n : ℕ}
    (hout : n < 1 ∨ 4 * cutoff + 1 < n) :
    finiteCoefficient 2 cutoff n = 0 := by
  rw [c2_finiteCoefficient_eq_profile_window]
  split_ifs <;> omega

end

end NativeCarrySpectralWeyl.Camera.FiniteBridge
