import NativeCarrySpectralWeyl.Camera.C2InteriorProfile

/-!
# Finite-to-periodic bridge for natural cameras

This file develops the interval-counting lemmas needed to identify the free
finite coefficients of natural saturated cameras with their periodic profiles.
-/

namespace NativeCarrySpectralWeyl.Camera.FiniteBridge

open FiniteNativeCarryOperator

noncomputable section

private theorem sum_leftLeg_indicator (center half n : ℕ) (hcenter : half ≤ center) :
    ∑ radius ∈ Finset.Icc 1 half,
      (if center - radius = n then (1 : ℤ) else 0) =
        if center - half ≤ n ∧ n < center then 1 else 0 := by
  by_cases hwindow : center - half ≤ n ∧ n < center
  · have hmem : center - n ∈ Finset.Icc 1 half := by
      simp only [Finset.mem_Icc]
      omega
    have heq : ∀ radius ∈ Finset.Icc 1 half,
        center - radius = n ↔ radius = center - n := by
      intro radius hradius
      simp only [Finset.mem_Icc] at hradius
      omega
    calc
      (∑ radius ∈ Finset.Icc 1 half,
          if center - radius = n then (1 : ℤ) else 0) =
          ∑ radius ∈ Finset.Icc 1 half,
            if radius = center - n then (1 : ℤ) else 0 := by
              apply Finset.sum_congr rfl
              intro radius hradius
              rw [if_congr (heq radius hradius) rfl rfl]
      _ = 1 := by simp [hmem]
      _ = (if center - half ≤ n ∧ n < center then 1 else 0) := by
        rw [if_pos hwindow]
  · have hne : ∀ radius ∈ Finset.Icc 1 half, center - radius ≠ n := by
      intro radius hradius heq
      simp only [Finset.mem_Icc] at hradius
      apply hwindow
      omega
    calc
      (∑ radius ∈ Finset.Icc 1 half,
          if center - radius = n then (1 : ℤ) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro radius hradius
            simp [hne radius hradius]
      _ = (if center - half ≤ n ∧ n < center then 1 else 0) := by
        rw [if_neg hwindow]

private theorem sum_rightLeg_indicator (center half n : ℕ) :
    ∑ radius ∈ Finset.Icc 1 half,
      (if center + radius = n then (1 : ℤ) else 0) =
        if center < n ∧ n ≤ center + half then 1 else 0 := by
  by_cases hwindow : center < n ∧ n ≤ center + half
  · have hmem : n - center ∈ Finset.Icc 1 half := by
      simp only [Finset.mem_Icc]
      omega
    have heq : ∀ radius ∈ Finset.Icc 1 half,
        center + radius = n ↔ radius = n - center := by
      intro radius hradius
      simp only [Finset.mem_Icc] at hradius
      omega
    calc
      (∑ radius ∈ Finset.Icc 1 half,
          if center + radius = n then (1 : ℤ) else 0) =
          ∑ radius ∈ Finset.Icc 1 half,
            if radius = n - center then (1 : ℤ) else 0 := by
              apply Finset.sum_congr rfl
              intro radius hradius
              rw [if_congr (heq radius hradius) rfl rfl]
      _ = 1 := by simp [hmem]
      _ = (if center < n ∧ n ≤ center + half then 1 else 0) := by
        rw [if_pos hwindow]
  · have hne : ∀ radius ∈ Finset.Icc 1 half, center + radius ≠ n := by
      intro radius hradius heq
      simp only [Finset.mem_Icc] at hradius
      apply hwindow
      omega
    calc
      (∑ radius ∈ Finset.Icc 1 half,
          if center + radius = n then (1 : ℤ) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro radius hradius
            simp [hne radius hradius]
      _ = (if center < n ∧ n ≤ center + half then 1 else 0) := by
        rw [if_neg hwindow]

/-- One natural odd-camera center is a contiguous unit block with center weight `-(b-1)`. -/
theorem odd_centerCoefficient (half index n : ℕ) (hhalf : 1 ≤ half) :
    let camera := half + half + 1
    let center := camera * (index + 1)
    centerCoefficient camera index n =
      if center - half ≤ n ∧ n < center then 1
      else if n = center then -((camera - 1 : ℕ) : ℤ)
      else if center < n ∧ n ≤ center + half then 1 else 0 := by
  dsimp only
  have h2 : half + half + 1 ≠ 2 := by omega
  have hdiv : (half + half + 1) / 2 = half := by omega
  have hcenter : half ≤ (half + half + 1) * (index + 1) := by
    exact le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
  rw [centerCoefficient, if_neg h2, Camera.alignedCenter_of_ne_two h2]
  simp only [Camera.radiusSet, Camera.halfRange, hdiv, bracketCoefficient,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hleft := sum_leftLeg_indicator
    ((half + half + 1) * (index + 1)) half n hcenter
  have hright := sum_rightLeg_indicator
    ((half + half + 1) * (index + 1)) half n
  have hmiddle :
      (∑ _radius ∈ Finset.Icc 1 half,
        2 * if (half + half + 1) * (index + 1) = n then (1 : ℤ) else 0) =
      if (half + half + 1) * (index + 1) = n then 2 * (half : ℤ) else 0 := by
    by_cases hc : (half + half + 1) * (index + 1) = n
    · simp [hc, Nat.card_Icc, mul_comm]
    · simp [hc]
  rw [hleft, hmiddle, hright]
  split_ifs <;> norm_num at * <;> omega

/-- Seeds of an odd natural camera occupy exactly `1, ..., half`. -/
theorem odd_seedCoefficient (half n : ℕ) :
    seedCoefficient (half + half + 1) n =
      if 1 ≤ n ∧ n ≤ half then 1 else 0 := by
  have h2 : half + half + 1 ≠ 2 := by omega
  have hdiv : (half + half + 1) / 2 = half := by omega
  rw [seedCoefficient, if_neg h2]
  simp [Camera.radiusSet, Camera.halfRange, hdiv, Finset.mem_Icc, eq_comm]

private theorem not_dvd_between_consecutive_multiples
    {camera quotient n : ℕ} (hcamera : 0 < camera)
    (hlower : camera * quotient < n) (hupper : n < camera * (quotient + 1)) :
    ¬camera ∣ n := by
  rintro ⟨multiple, rfl⟩
  have hl : quotient < multiple :=
    (Nat.mul_lt_mul_left hcamera).mp hlower
  have hu : multiple < quotient + 1 :=
    (Nat.mul_lt_mul_left hcamera).mp hupper
  omega

private theorem oddProfile_eq_one_of_not_dvd
    {camera n : ℕ} (hnot : ¬camera ∣ n) : oddProfile camera n = 1 := by
  simp [oddProfile, dvdIndicator, hnot]

private theorem oddProfile_center (half index : ℕ) :
    oddProfile (half + half + 1) ((half + half + 1) * (index + 1)) =
      -(((half + half + 1) - 1 : ℕ) : ℤ) := by
  have hdvd : half + half + 1 ∣ (half + half + 1) * (index + 1) :=
    dvd_mul_right _ _
  simp [oddProfile, dvdIndicator, hdvd]

/-- Complete coefficient formula for every finite natural odd-camera cutoff. -/
theorem odd_finiteCoefficient_eq_profile_window_of_half
    (half cutoff n : ℕ) (hhalf : 1 ≤ half) :
    let camera := half + half + 1
    finiteCoefficient camera cutoff n =
      if 1 ≤ n ∧ n ≤ camera * cutoff + half then oddProfile camera n else 0 := by
  dsimp only
  induction cutoff with
  | zero =>
      rw [finiteCoefficient_zero, odd_seedCoefficient half n]
      by_cases hwindow : 1 ≤ n ∧ n ≤ half
      · have hnot : ¬(half + half + 1) ∣ n := by
          intro hdvd
          have hle := Nat.le_of_dvd (by omega : 0 < n) hdvd
          omega
        rw [if_pos hwindow, oddProfile_eq_one_of_not_dvd hnot]
        simp [hwindow]
      · simp [hwindow]
  | succ cutoff ih =>
      rw [finiteCoefficient_succ, ih, odd_centerCoefficient half cutoff n hhalf]
      let camera := half + half + 1
      let center := camera * (cutoff + 1)
      change
        (if 1 ≤ n ∧ n ≤ camera * cutoff + half then oddProfile camera n else 0) +
            (if center - half ≤ n ∧ n < center then 1
            else if n = center then -((camera - 1 : ℕ) : ℤ)
            else if center < n ∧ n ≤ center + half then 1 else 0) =
          if 1 ≤ n ∧ n ≤ camera * (cutoff + 1) + half then
            oddProfile camera n else 0
      have hcamera : 0 < camera := by dsimp [camera]; omega
      have hstart : center - half = camera * cutoff + half + 1 := by
        dsimp [center, camera]
        rw [Nat.mul_add]
        omega
      have hnext : camera * (cutoff + 2) = center + camera := by
        dsimp [center]
        rw [Nat.mul_add, Nat.mul_add]
        omega
      by_cases hold : 1 ≤ n ∧ n ≤ camera * cutoff + half
      · have hext : 1 ≤ n ∧ n ≤ camera * (cutoff + 1) + half := by
          exact ⟨hold.1, hold.2.trans (by gcongr; omega)⟩
        have hleft : ¬(center - half ≤ n ∧ n < center) := by
          rw [hstart]
          omega
        have hcenter : n ≠ center := by
          rw [hstart] at hleft
          omega
        have hright : ¬(center < n ∧ n ≤ center + half) := by omega
        split_ifs
        all_goals omega
      · by_cases hext : 1 ≤ n ∧ n ≤ camera * (cutoff + 1) + half
        · have hblock : center - half ≤ n ∧ n ≤ center + half := by
            rw [hstart]
            omega
          by_cases hleft : n < center
          · have hnot : ¬camera ∣ n := by
              apply not_dvd_between_consecutive_multiples hcamera
              · rw [hstart] at hblock
                have : camera * cutoff < camera * cutoff + half + 1 := by omega
                exact this.trans_le hblock.1
              · exact hleft
            have hprofile := oddProfile_eq_one_of_not_dvd hnot
            rw [hprofile]
            split_ifs <;> omega
          · by_cases hcenter : n = center
            · subst n
              rw [oddProfile_center]
              split_ifs
              all_goals norm_num at *
              all_goals omega
            · have hright : center < n := by omega
              have hnot : ¬camera ∣ n := by
                apply not_dvd_between_consecutive_multiples hcamera hright
                rw [hnext]
                have hhalf_lt : half < camera := by dsimp [camera]; omega
                exact lt_of_le_of_lt hblock.2 (Nat.add_lt_add_left hhalf_lt center)
              have hprofile := oddProfile_eq_one_of_not_dvd hnot
              rw [hprofile]
              split_ifs <;> omega
        · have hleft : ¬(center - half ≤ n ∧ n < center) := by
            rw [hstart]
            omega
          have hcenter : n ≠ center := by omega
          have hright : ¬(center < n ∧ n ≤ center + half) := by omega
          split_ifs
          all_goals omega

/-- Supported odd cameras have the exact finite/profile window formula. -/
theorem odd_finiteCoefficient_eq_profile_window {camera cutoff n : ℕ}
    (hcamera : 3 ≤ camera) (hodd : Odd camera) :
    finiteCoefficient camera cutoff n =
      if 1 ≤ n ∧ n ≤ camera * cutoff + camera / 2 then oddProfile camera n else 0 := by
  obtain ⟨half, rfl⟩ := hodd
  have hhalf : 1 ≤ half := by omega
  rw [show (2 * half + 1) / 2 = half by omega]
  simpa [two_mul] using
    odd_finiteCoefficient_eq_profile_window_of_half half cutoff n hhalf

/-- In its emitted window, an odd natural camera coefficient is its periodic profile. -/
theorem odd_finiteCoefficient_eq_profile {camera cutoff n : ℕ}
    (hcamera : 3 ≤ camera) (hodd : Odd camera)
    (hn : 1 ≤ n) (hupper : n ≤ camera * cutoff + camera / 2) :
    finiteCoefficient camera cutoff n = oddProfile camera n := by
  rw [odd_finiteCoefficient_eq_profile_window hcamera hodd]
  simp [hn, hupper]

/-- One natural even-camera center is a contiguous unit block with center weight `-b`. -/
theorem even_centerCoefficient (half index n : ℕ) (hhalf : 2 ≤ half) :
    let camera := half + half
    let center := camera * (index + 1)
    centerCoefficient camera index n =
      if center - half ≤ n ∧ n < center then 1
      else if n = center then -((camera : ℕ) : ℤ)
      else if center < n ∧ n ≤ center + half then 1 else 0 := by
  dsimp only
  have h2 : half + half ≠ 2 := by omega
  have hdiv : (half + half) / 2 = half := by omega
  have hcenter : half ≤ (half + half) * (index + 1) := by
    exact le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega))
  rw [centerCoefficient, if_neg h2, Camera.alignedCenter_of_ne_two h2]
  simp only [Camera.radiusSet, Camera.halfRange, hdiv, bracketCoefficient,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hleft := sum_leftLeg_indicator
    ((half + half) * (index + 1)) half n hcenter
  have hright := sum_rightLeg_indicator
    ((half + half) * (index + 1)) half n
  have hmiddle :
      (∑ _radius ∈ Finset.Icc 1 half,
        2 * if (half + half) * (index + 1) = n then (1 : ℤ) else 0) =
      if (half + half) * (index + 1) = n then 2 * (half : ℤ) else 0 := by
    by_cases hc : (half + half) * (index + 1) = n
    · simp [hc, Nat.card_Icc, mul_comm]
    · simp [hc]
  rw [hleft, hmiddle, hright]
  split_ifs <;> norm_num at * <;> omega

/-- Seeds of a natural even camera occupy exactly `1, ..., half`. -/
theorem even_seedCoefficient (half n : ℕ) (hhalf : 2 ≤ half) :
    seedCoefficient (half + half) n =
      if 1 ≤ n ∧ n ≤ half then 1 else 0 := by
  have h2 : half + half ≠ 2 := by omega
  have hdiv : (half + half) / 2 = half := by omega
  rw [seedCoefficient, if_neg h2]
  simp [Camera.radiusSet, Camera.halfRange, hdiv, Finset.mem_Icc, eq_comm]

private theorem evenProfile_eq_one_of_not_half_dvd
    {half n : ℕ} (hnot : ¬half ∣ n) : evenProfile (half + half) n = 1 := by
  have hdiv : (half + half) / 2 = half := by omega
  have hnotCamera : ¬(half + half) ∣ n := by
    intro hcamera
    exact hnot ((dvd_add (dvd_refl half) (dvd_refl half)).trans hcamera)
  simp [evenProfile, dvdIndicator, hdiv, hnot, hnotCamera]

private theorem evenProfile_center (half index : ℕ) :
    evenProfile (half + half) ((half + half) * (index + 1)) =
      -(((half + half : ℕ)) : ℤ) := by
  have hdiv : (half + half) / 2 = half := by omega
  have hdvdHalf : half ∣ (half + half) * (index + 1) := by
    exact (dvd_add (dvd_refl half) (dvd_refl half)).trans (dvd_mul_right _ _)
  have hdvdCamera : half + half ∣ (half + half) * (index + 1) :=
    dvd_mul_right _ _
  simp [evenProfile, dvdIndicator, hdiv, hdvdHalf, hdvdCamera]

private theorem evenProfile_antipodal (half quotient : ℕ) (hhalf : 0 < half) :
    evenProfile (half + half) ((half + half) * quotient + half) = 2 := by
  have hdiv : (half + half) / 2 = half := by omega
  have hdvdHalf : half ∣ (half + half) * quotient + half := by
    use quotient + quotient + 1
    ring
  have hnotCamera : ¬(half + half) ∣ (half + half) * quotient + half := by
    apply not_dvd_between_consecutive_multiples
      (camera := half + half) (quotient := quotient) (n := (half + half) * quotient + half)
      (by omega)
    · omega
    · rw [Nat.mul_add]
      omega
  simp [evenProfile, dvdIndicator, hdiv, hdvdHalf, hnotCamera]

/--
Complete coefficient formula for every finite natural even-camera cutoff.

The final antipodal point has coefficient `1`; it becomes the periodic value
`2` only when the next center is appended.
-/
theorem even_finiteCoefficient_eq_profile_window_of_half
    (half cutoff n : ℕ) (hhalf : 2 ≤ half) :
    let camera := half + half
    let endpoint := camera * cutoff + half
    finiteCoefficient camera cutoff n =
      if 1 ≤ n ∧ n < endpoint then evenProfile camera n
      else if n = endpoint then 1 else 0 := by
  dsimp only
  induction cutoff with
  | zero =>
      rw [finiteCoefficient_zero, even_seedCoefficient half n hhalf]
      simp only [Nat.mul_zero, zero_add]
      by_cases hinterior : 1 ≤ n ∧ n < half
      · have hnot : ¬half ∣ n := by
          intro hdvd
          have hle := Nat.le_of_dvd (by omega : 0 < n) hdvd
          omega
        have hseed : 1 ≤ n ∧ n ≤ half := by omega
        rw [if_pos hinterior, evenProfile_eq_one_of_not_half_dvd hnot]
        simp [hinterior, hseed]
      · by_cases hendpoint : n = half
        · subst n
          have hne : half ≠ 0 := by omega
          simp [hne]
        · have hseed : ¬(1 ≤ n ∧ n ≤ half) := by omega
          simp [hinterior, hendpoint, hseed]
  | succ cutoff ih =>
      rw [finiteCoefficient_succ, ih, even_centerCoefficient half cutoff n hhalf]
      let camera := half + half
      let oldEndpoint := camera * cutoff + half
      let center := camera * (cutoff + 1)
      let newEndpoint := camera * (cutoff + 1) + half
      change
        (if 1 ≤ n ∧ n < oldEndpoint then evenProfile camera n
          else if n = oldEndpoint then 1 else 0) +
            (if center - half ≤ n ∧ n < center then 1
            else if n = center then -((camera : ℕ) : ℤ)
            else if center < n ∧ n ≤ center + half then 1 else 0) =
          if 1 ≤ n ∧ n < newEndpoint then evenProfile camera n
          else if n = newEndpoint then 1 else 0
      have hhalfPos : 0 < half := by omega
      have holdPos : 0 < oldEndpoint := by dsimp [oldEndpoint]; omega
      have hcenterEq : center = oldEndpoint + half := by
        dsimp [center, oldEndpoint, camera]
        ring
      have hnewEq : newEndpoint = center + half := by rfl
      have hleftStart : center - half = oldEndpoint := by
        rw [hcenterEq]
        omega
      have holdMul : oldEndpoint = half * (cutoff + cutoff + 1) := by
        dsimp [oldEndpoint, camera]
        ring
      have hcenterMul : center = half * ((cutoff + cutoff + 1) + 1) := by
        dsimp [center, camera]
        ring
      have hnewMul : newEndpoint = half * (((cutoff + cutoff + 1) + 1) + 1) := by
        dsimp [newEndpoint, camera]
        ring
      by_cases hold : 1 ≤ n ∧ n < oldEndpoint
      · have hnew : 1 ≤ n ∧ n < newEndpoint := by
          constructor
          · exact hold.1
          · rw [hnewEq, hcenterEq]
            omega
        have hleft : ¬(center - half ≤ n ∧ n < center) := by
          rw [hleftStart]
          omega
        have hcenter : n ≠ center := by
          rw [hcenterEq]
          omega
        have hright : ¬(center < n ∧ n ≤ center + half) := by omega
        rw [if_pos hold, if_neg hleft, if_neg hcenter, if_neg hright, if_pos hnew]
        simp
      · by_cases holdEndpoint : n = oldEndpoint
        · subst n
          rw [evenProfile_antipodal half cutoff hhalfPos]
          split_ifs <;> norm_num at * <;> omega
        · by_cases hnew : 1 ≤ n ∧ n < newEndpoint
          · have hafterOld : oldEndpoint < n := by omega
            by_cases hleft : n < center
            · have hnotHalf : ¬half ∣ n := by
                apply not_dvd_between_consecutive_multiples
                  (camera := half) (quotient := cutoff + cutoff + 1) (n := n)
                  hhalfPos
                · rw [← holdMul]
                  exact hafterOld
                · rw [← hcenterMul]
                  exact hleft
              rw [evenProfile_eq_one_of_not_half_dvd hnotHalf]
              split_ifs <;> norm_num at * <;> omega
            · by_cases hcenter : n = center
              · subst n
                rw [evenProfile_center half cutoff]
                split_ifs <;> norm_num at *
                all_goals omega
              · have hright : center < n := by omega
                have hnotHalf : ¬half ∣ n := by
                  apply not_dvd_between_consecutive_multiples
                    (camera := half) (quotient := (cutoff + cutoff + 1) + 1) (n := n)
                    hhalfPos
                  · rw [← hcenterMul]
                    exact hright
                  · rw [← hnewMul]
                    exact hnew.2
                rw [evenProfile_eq_one_of_not_half_dvd hnotHalf]
                split_ifs <;> norm_num at *
                all_goals omega
          · by_cases hnewEndpoint : n = newEndpoint
            · subst n
              split_ifs <;> norm_num at * <;> omega
            · have hleft : ¬(center - half ≤ n ∧ n < center) := by
                rw [hleftStart]
                omega
              have hcenter : n ≠ center := by omega
              have hright : ¬(center < n ∧ n ≤ center + half) := by
                rw [← hnewEq]
                omega
              rw [if_neg hold, if_neg holdEndpoint, if_neg hleft, if_neg hcenter,
                if_neg hright, if_neg hnew, if_neg hnewEndpoint]
              simp

/-- Supported even cameras have the exact finite/profile window with one final correction. -/
theorem even_finiteCoefficient_eq_profile_window {camera cutoff n : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) :
    finiteCoefficient camera cutoff n =
      if 1 ≤ n ∧ n < camera * cutoff + camera / 2 then evenProfile camera n
      else if n = camera * cutoff + camera / 2 then 1 else 0 := by
  obtain ⟨half, rfl⟩ := heven
  have hhalf : 2 ≤ half := by omega
  rw [show (half + half) / 2 = half by omega]
  exact even_finiteCoefficient_eq_profile_window_of_half half cutoff n hhalf

/-- Strictly before its final antipodal point, an even finite camera equals its profile. -/
theorem even_finiteCoefficient_eq_profile {camera cutoff n : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera)
    (hn : 1 ≤ n) (hupper : n < camera * cutoff + camera / 2) :
    finiteCoefficient camera cutoff n = evenProfile camera n := by
  rw [even_finiteCoefficient_eq_profile_window hcamera heven]
  simp [hn, hupper]

/-- The last emitted antipodal coefficient of an even finite camera is exactly `1`. -/
theorem even_finiteCoefficient_endpoint {camera cutoff : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) :
    finiteCoefficient camera cutoff (camera * cutoff + camera / 2) = 1 := by
  rw [even_finiteCoefficient_eq_profile_window hcamera heven]
  simp

/-- The final even-camera endpoint is one below its periodic profile value. -/
theorem evenProfile_endpoint {camera cutoff : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) :
    evenProfile camera (camera * cutoff + camera / 2) = 2 := by
  obtain ⟨half, rfl⟩ := heven
  have hhalf : 0 < half := by omega
  rw [show (half + half) / 2 = half by omega]
  exact evenProfile_antipodal half cutoff hhalf

/-- Equivalent even-camera formula as the periodic profile minus one final endpoint unit. -/
theorem even_finiteCoefficient_eq_profile_window_corrected {camera cutoff n : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) :
    finiteCoefficient camera cutoff n =
      if 1 ≤ n ∧ n ≤ camera * cutoff + camera / 2 then
        evenProfile camera n -
          (if n = camera * cutoff + camera / 2 then 1 else 0)
      else 0 := by
  obtain ⟨half, rfl⟩ := heven
  have hhalf : 2 ≤ half := by omega
  have hhalfPos : 0 < half := by omega
  rw [show (half + half) / 2 = half by omega]
  rw [even_finiteCoefficient_eq_profile_window_of_half half cutoff n hhalf]
  let endpoint := (half + half) * cutoff + half
  change
    (if 1 ≤ n ∧ n < endpoint then evenProfile (half + half) n
      else if n = endpoint then 1 else 0) =
      if 1 ≤ n ∧ n ≤ endpoint then
        evenProfile (half + half) n - (if n = endpoint then 1 else 0)
      else 0
  by_cases hinterior : 1 ≤ n ∧ n < endpoint
  · have hwindow : 1 ≤ n ∧ n ≤ endpoint := by omega
    have hne : n ≠ endpoint := by omega
    simp [hinterior, hwindow, hne]
  · by_cases hendpoint : n = endpoint
    · subst n
      rw [evenProfile_antipodal half cutoff hhalfPos]
      have hpos : 1 ≤ endpoint := by dsimp [endpoint]; omega
      simp [hpos]
    · have hout : ¬(1 ≤ n ∧ n ≤ endpoint) := by omega
      simp [hinterior, hendpoint, hout]

/-- Unified natural-camera bridge on the strict common interior window. -/
theorem natural_finiteCoefficient_eq_profile {camera cutoff n : ℕ}
    (hcamera : 3 ≤ camera) (hn : 1 ≤ n)
    (hupper : n < camera * cutoff + camera / 2) :
    finiteCoefficient camera cutoff n = profile camera n := by
  have h2 : camera ≠ 2 := by omega
  rcases Nat.even_or_odd camera with heven | hodd
  · have hcameraEven : 4 ≤ camera := by
      obtain ⟨half, hhalf⟩ := heven
      omega
    rw [even_finiteCoefficient_eq_profile hcameraEven heven hn hupper,
      profile_of_even h2 heven]
  · have hle : n ≤ camera * cutoff + camera / 2 := by omega
    rw [odd_finiteCoefficient_eq_profile hcamera hodd hn hle,
      profile_of_odd h2 hodd]

end

end NativeCarrySpectralWeyl.Camera.FiniteBridge
