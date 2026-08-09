import FiniteNativeCarryOperator.Camera.AllBase
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Periodic native-camera profiles

This file isolates the exact integer coefficient profiles of the aligned C2
camera and of every natural saturated camera.  The definitions use only
divisibility and are independent of the angular or spectral parameters.
-/

open scoped BigOperators

namespace NativeCarrySpectralWeyl.Camera

/-- Integer indicator of divisibility. -/
def dvdIndicator (divisor n : ℕ) : ℤ :=
  if divisor ∣ n then 1 else 0

/-- C2 is aligned on centers `4m`, hence its periodic slope is four. -/
def cameraSlope (camera : ℕ) : ℕ :=
  if camera = 2 then 4 else camera

/-- Exact periodic coefficient profile of the aligned C2 camera. -/
def c2Profile (n : ℕ) : ℤ :=
  1 - dvdIndicator 2 n - 2 * dvdIndicator 4 n

/-- Exact periodic coefficient profile of an odd natural camera. -/
def oddProfile (camera n : ℕ) : ℤ :=
  1 - (camera : ℤ) * dvdIndicator camera n

/-- Exact periodic coefficient profile of an even natural camera. -/
def evenProfile (camera n : ℕ) : ℤ :=
  1 + dvdIndicator (camera / 2) n - (camera + 2 : ℕ) * dvdIndicator camera n

/-- Unified native-camera profile.  Theorems about it assume `2 ≤ camera`. -/
def profile (camera n : ℕ) : ℤ :=
  if camera = 2 then c2Profile n
  else if Odd camera then oddProfile camera n
  else evenProfile camera n

@[simp] theorem cameraSlope_two : cameraSlope 2 = 4 := by
  simp [cameraSlope]

@[simp] theorem cameraSlope_of_ne_two {camera : ℕ} (h : camera ≠ 2) :
    cameraSlope camera = camera := by
  simp [cameraSlope, h]

@[simp] theorem profile_two (n : ℕ) : profile 2 n = c2Profile n := by
  simp [profile]

theorem profile_of_odd {camera : ℕ} (h2 : camera ≠ 2) (hodd : Odd camera) (n : ℕ) :
    profile camera n = oddProfile camera n := by
  simp [profile, h2, hodd]

theorem profile_of_even {camera : ℕ} (h2 : camera ≠ 2) (heven : Even camera) (n : ℕ) :
    profile camera n = evenProfile camera n := by
  simp [profile, h2, (Nat.not_odd_iff_even.mpr heven)]

/-- A divisibility indicator is invariant under translation by a multiple of its divisor. -/
theorem dvdIndicator_add_of_dvd {divisor shift n : ℕ} (hdiv : divisor ∣ shift) :
    dvdIndicator divisor (n + shift) = dvdIndicator divisor n := by
  have hiff : divisor ∣ n + shift ↔ divisor ∣ n :=
    (Nat.dvd_add_iff_left hdiv).symm
  simp only [dvdIndicator, hiff]

/-- The aligned C2 coefficient profile is four-periodic. -/
theorem c2Profile_add_period (n : ℕ) : c2Profile (n + 4) = c2Profile n := by
  simp only [c2Profile]
  rw [dvdIndicator_add_of_dvd (by norm_num : 2 ∣ 4),
    dvdIndicator_add_of_dvd (by norm_num : 4 ∣ 4)]

/-- An odd natural-camera profile is periodic with its camera width. -/
theorem oddProfile_add_period (camera n : ℕ) :
    oddProfile camera (n + camera) = oddProfile camera n := by
  simp only [oddProfile]
  rw [dvdIndicator_add_of_dvd (dvd_refl camera)]

/-- An even natural-camera profile is periodic with its camera width. -/
theorem evenProfile_add_period {camera : ℕ} (heven : Even camera) (n : ℕ) :
    evenProfile camera (n + camera) = evenProfile camera n := by
  obtain ⟨k, rfl⟩ := heven
  have hhalf : (k + k) / 2 = k := by omega
  simp only [evenProfile, hhalf]
  rw [dvdIndicator_add_of_dvd (dvd_add (dvd_refl k) (dvd_refl k)),
    dvdIndicator_add_of_dvd (dvd_refl (k + k))]

/-- Every supported native profile is periodic with its exact spectral slope. -/
theorem profile_add_period {camera : ℕ} (hcamera : 2 ≤ camera) (n : ℕ) :
    profile camera (n + cameraSlope camera) = profile camera n := by
  by_cases h2 : camera = 2
  · subst camera
    simpa using c2Profile_add_period n
  · rw [cameraSlope_of_ne_two h2]
    rcases Nat.even_or_odd camera with heven | hodd
    · simp_rw [profile_of_even h2 heven]
      exact evenProfile_add_period heven n
    · simp_rw [profile_of_odd h2 hodd]
      exact oddProfile_add_period camera n

/-- Count divisibility indicators on the positive period `(0, bound]`. -/
theorem sum_dvdIndicator_Ioc (bound divisor : ℕ) :
    ∑ n ∈ Finset.Ioc 0 bound, dvdIndicator divisor n = (bound / divisor : ℕ) := by
  simp [dvdIndicator, Nat.Ioc_filter_dvd_card_eq_div]

/-- The aligned C2 profile has zero mean over its exact period. -/
theorem c2Profile_sum_period :
    ∑ n ∈ Finset.Ioc 0 4, c2Profile n = 0 := by
  simp only [c2Profile, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, sum_dvdIndicator_Ioc, sum_dvdIndicator_Ioc]
  norm_num

/-- Every positive odd-camera profile has zero mean over one camera period. -/
theorem oddProfile_sum_period {camera : ℕ} (hcamera : 0 < camera) :
    ∑ n ∈ Finset.Ioc 0 camera, oddProfile camera n = 0 := by
  simp only [oddProfile, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, sum_dvdIndicator_Ioc]
  simp [hcamera]

/-- Every supported even-camera profile has zero mean over one camera period. -/
theorem evenProfile_sum_period {camera : ℕ} (hcamera : 2 ≤ camera) (heven : Even camera) :
    ∑ n ∈ Finset.Ioc 0 camera, evenProfile camera n = 0 := by
  obtain ⟨k, rfl⟩ := heven
  have hk : 0 < k := by omega
  have hhalf : (k + k) / 2 = k := by omega
  have hadd : k + k = 2 * k := by omega
  have hquot : (k + k) / k = 2 := by
    rw [hadd, Nat.mul_div_cancel _ hk]
  have hself : (k + k) / (k + k) = 1 := Nat.div_self (by omega)
  simp only [evenProfile, hhalf, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, sum_dvdIndicator_Ioc, sum_dvdIndicator_Ioc]
  simp [hquot, hself]

/-- Every supported native camera has zero coefficient mean over its slope. -/
theorem profile_sum_period {camera : ℕ} (hcamera : 2 ≤ camera) :
    ∑ n ∈ Finset.Ioc 0 (cameraSlope camera), profile camera n = 0 := by
  by_cases h2 : camera = 2
  · subst camera
    simpa using c2Profile_sum_period
  · rw [cameraSlope_of_ne_two h2]
    rcases Nat.even_or_odd camera with heven | hodd
    · simp_rw [profile_of_even h2 heven]
      exact evenProfile_sum_period hcamera heven
    · simp_rw [profile_of_odd h2 hodd]
      exact oddProfile_sum_period (lt_of_lt_of_le (by norm_num) hcamera)

end NativeCarrySpectralWeyl.Camera
