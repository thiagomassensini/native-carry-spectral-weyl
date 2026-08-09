import NativeCarrySpectralWeyl.Camera.NormalConvergence
import NativeCarrySpectralWeyl.Camera.ProfileDirichlet

/-!
# Bridge from finite brackets to periodic profile Dirichlet series

This module complexifies the free finite stencil, identifies its exact
Dirichlet polynomial for C2, odd and even natural cameras, and passes to the
limit on `re s > 1`.  In that common absolutely convergent half-plane the
normally convergent bracket characteristic equals the profile series and hence
the explicit camera factor times Mathlib's `riemannZeta`.

The final theorem records the cross-factor identity only on `re s > 1`.
Extending it to `re s > -1` by the holomorphic identity theorem is a separate
obligation.
-/

open scoped BigOperators

namespace NativeCarrySpectralWeyl.Camera.FiniteBridge

open FiniteNativeCarryOperator
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Evaluate a formal stencil against complex Dirichlet samples. -/
def evalDirichletStencil (s : ℂ) : FormalStencil →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ (dirichletValue s)

@[simp] theorem evalDirichletStencil_atom (s : ℂ) (n : ℕ) :
    evalDirichletStencil s (atom n) = dirichletValue s n := by
  simp [evalDirichletStencil, atom]

theorem evalDirichletStencil_centeredBracketStencil
    (s : ℂ) (center radius : ℕ) :
    evalDirichletStencil s (centeredBracketStencil center radius) =
      centeredBracketTerm s center radius := by
  simp [centeredBracketStencil, centeredBracketTerm]

theorem evalDirichletStencil_seedStencil (s : ℂ) (camera : ℕ) :
    evalDirichletStencil s (seedStencil camera) = seedDirichletTerm camera s := by
  by_cases h2 : camera = 2
  · subst camera
    simp [seedStencil, seedDirichletTerm]
  · simp [seedStencil, seedDirichletTerm, h2]

theorem evalDirichletStencil_centerStencil (s : ℂ) (camera index : ℕ) :
    evalDirichletStencil s (centerStencil camera index) =
      centerBracketTerm camera s index := by
  by_cases h2 : camera = 2
  · subst camera
    simp [centerStencil, centerBracketTerm,
      evalDirichletStencil_centeredBracketStencil]
  · simp [centerStencil, centerBracketTerm, h2,
      evalDirichletStencil_centeredBracketStencil]

theorem evalDirichletStencil_finiteStencil (s : ℂ) (camera cutoff : ℕ) :
    evalDirichletStencil s (finiteStencil camera cutoff) =
      finiteBracketCharacteristic camera cutoff s := by
  simp [finiteStencil, finiteBracketCharacteristic,
    evalDirichletStencil_seedStencil, evalDirichletStencil_centerStencil]

/-- Formal stencil of the first `length` positive coefficients. -/
def coefficientPrefixStencil (coeff : ℕ → ℤ) (length : ℕ) : FormalStencil :=
  ∑ index ∈ Finset.range length, (coeff (index + 1)) • atom (index + 1)

theorem coefficientPrefixStencil_apply (coeff : ℕ → ℤ) (length n : ℕ) :
    coefficientPrefixStencil coeff length n =
      if 1 ≤ n ∧ n ≤ length then coeff n else 0 := by
  induction length with
  | zero =>
      have hwindow : ¬(1 ≤ n ∧ n ≤ 0) := by omega
      rw [coefficientPrefixStencil]
      simp only [Finset.sum_range_zero, Finsupp.zero_apply, if_neg hwindow]
  | succ length ih =>
      rw [show coefficientPrefixStencil coeff (length + 1) =
          coefficientPrefixStencil coeff length +
            (coeff (length + 1)) • atom (length + 1) by
        simp [coefficientPrefixStencil, Finset.sum_range_succ]]
      simp only [Finsupp.add_apply, Finsupp.smul_apply, ih, atom_apply]
      by_cases hold : 1 ≤ n ∧ n ≤ length
      · have hnew : 1 ≤ n ∧ n ≤ length + 1 := by omega
        have hne : length + 1 ≠ n := by omega
        simp [hold, hnew, hne]
      · by_cases heq : n = length + 1
        · subst n
          have hnew : 1 ≤ length + 1 ∧ length + 1 ≤ length + 1 := by omega
          simp [hnew]
        · have hnew : ¬(1 ≤ n ∧ n ≤ length + 1) := by omega
          have hne : length + 1 ≠ n := Ne.symm heq
          simp [hold, hnew, hne]

/-- Complex Dirichlet polynomial of the first `length` positive coefficients. -/
def coefficientDirichletPrefix (coeff : ℕ → ℤ) (length : ℕ) (s : ℂ) : ℂ :=
  ∑ index ∈ Finset.range length,
    (coeff (index + 1) : ℂ) * dirichletValue s (index + 1)

theorem evalDirichletStencil_coefficientPrefixStencil
    (coeff : ℕ → ℤ) (length : ℕ) (s : ℂ) :
    evalDirichletStencil s (coefficientPrefixStencil coeff length) =
      coefficientDirichletPrefix coeff length s := by
  simp [coefficientPrefixStencil, coefficientDirichletPrefix]

/-- The complete finite C2 stencil is exactly its periodic-profile prefix. -/
theorem finiteStencil_two_eq_coefficientPrefixStencil (cutoff : ℕ) :
    finiteStencil 2 cutoff = coefficientPrefixStencil c2Profile (4 * cutoff + 1) := by
  ext n
  rw [finiteStencil_apply, c2_finiteCoefficient_eq_profile_window,
    coefficientPrefixStencil_apply]

/-- A finite odd natural camera is exactly its periodic-profile prefix. -/
theorem finiteStencil_odd_eq_coefficientPrefixStencil {camera : ℕ}
    (hcamera : 3 ≤ camera) (hodd : Odd camera) (cutoff : ℕ) :
    finiteStencil camera cutoff =
      coefficientPrefixStencil (oddProfile camera)
        (camera * cutoff + camera / 2) := by
  ext n
  rw [finiteStencil_apply, odd_finiteCoefficient_eq_profile_window hcamera hodd,
    coefficientPrefixStencil_apply]

/-- A finite even natural camera is its periodic-profile prefix minus the one
missing unit at the final antipodal endpoint. -/
theorem finiteStencil_even_eq_coefficientPrefixStencil_sub {camera : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) (cutoff : ℕ) :
    finiteStencil camera cutoff =
      coefficientPrefixStencil (evenProfile camera)
          (camera * cutoff + camera / 2) -
        atom (camera * cutoff + camera / 2) := by
  ext n
  rw [finiteStencil_apply,
    even_finiteCoefficient_eq_profile_window_corrected hcamera heven,
    Finsupp.sub_apply, coefficientPrefixStencil_apply, atom_apply]
  let endpoint := camera * cutoff + camera / 2
  have hendpoint : 1 ≤ endpoint := by
    dsimp [endpoint]
    omega
  by_cases hwindow : 1 ≤ n ∧ n ≤ endpoint
  · by_cases heq : n = endpoint
    · subst n
      simp [endpoint, hendpoint]
    · have hne : endpoint ≠ n := Ne.symm heq
      simp [endpoint, hwindow, heq, hne]
  · have hne : endpoint ≠ n := by
      intro heq
      subst n
      exact hwindow ⟨hendpoint, le_rfl⟩
    simp [endpoint, hwindow, hne]

/-- Exact finite C2 characteristic as a profile Dirichlet prefix. -/
theorem finiteBracketCharacteristic_two_eq_profilePrefix (cutoff : ℕ) (s : ℂ) :
    finiteBracketCharacteristic 2 cutoff s =
      coefficientDirichletPrefix c2Profile (4 * cutoff + 1) s := by
  rw [← evalDirichletStencil_finiteStencil, finiteStencil_two_eq_coefficientPrefixStencil,
    evalDirichletStencil_coefficientPrefixStencil]

/-- Exact finite odd-camera characteristic as a profile Dirichlet prefix. -/
theorem finiteBracketCharacteristic_odd_eq_profilePrefix {camera : ℕ}
    (hcamera : 3 ≤ camera) (hodd : Odd camera) (cutoff : ℕ) (s : ℂ) :
    finiteBracketCharacteristic camera cutoff s =
      coefficientDirichletPrefix (oddProfile camera)
        (camera * cutoff + camera / 2) s := by
  rw [← evalDirichletStencil_finiteStencil,
    finiteStencil_odd_eq_coefficientPrefixStencil hcamera hodd,
    evalDirichletStencil_coefficientPrefixStencil]

/-- Exact finite even-camera characteristic, including its final antipodal
correction. -/
theorem finiteBracketCharacteristic_even_eq_profilePrefix_sub {camera : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) (cutoff : ℕ) (s : ℂ) :
    finiteBracketCharacteristic camera cutoff s =
      coefficientDirichletPrefix (evenProfile camera)
          (camera * cutoff + camera / 2) s -
        dirichletValue s (camera * cutoff + camera / 2) := by
  rw [← evalDirichletStencil_finiteStencil,
    finiteStencil_even_eq_coefficientPrefixStencil_sub hcamera heven]
  simp [evalDirichletStencil_coefficientPrefixStencil]

/-- Dirichlet prefixes converge to the corresponding positive-index series. -/
theorem coefficientDirichletPrefix_tendsto {coeff : ℕ → ℤ} {s : ℂ}
    (hsummable : Summable (coefficientDirichletTerm coeff s)) :
    Filter.Tendsto (fun length => coefficientDirichletPrefix coeff length s)
      Filter.atTop (nhds (coefficientDirichletSeries coeff s)) := by
  have hnat : Summable (fun index : ℕ =>
      (coeff (index + 1) : ℂ) * dirichletValue s (index + 1)) := by
    apply (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => (coeff n : ℂ) * dirichletValue s n)).mp
    change Summable (fun n : ℕ+ =>
      (coeff (n : ℕ) : ℂ) * dirichletValue s (n : ℕ)) at hsummable
    exact hsummable
  have htsum : (∑' index : ℕ,
      (coeff (index + 1) : ℂ) * dirichletValue s (index + 1)) =
      coefficientDirichletSeries coeff s := by
    rw [coefficientDirichletSeries]
    have hp := tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => (coeff n : ℂ) * dirichletValue s n)
    simpa [coefficientDirichletTerm, positiveDirichletTerm, dirichletValue] using hp.symm
  rw [← htsum]
  exact hnat.hasSum.tendsto_sum_nat

/-- Positive affine cutoff lengths tend to infinity. -/
theorem tendsto_nat_mul_add_atTop {slope offset : ℕ} (hslope : 0 < slope) :
    Filter.Tendsto (fun cutoff => slope * cutoff + offset)
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro lower
  filter_upwards [Filter.eventually_ge_atTop lower] with cutoff hcutoff
  have hmul : cutoff ≤ slope * cutoff := Nat.le_mul_of_pos_left cutoff hslope
  omega

/-- Individual positive Dirichlet samples vanish at infinity on `re s > 1`. -/
theorem dirichletValue_tendsto_zero {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (dirichletValue s) Filter.atTop (nhds 0) := by
  have hpnat := positiveDirichletTerm_summable hs
  have hnat : Summable (fun index : ℕ => dirichletValue s (index + 1)) := by
    apply (summable_pnat_iff_summable_succ (f := dirichletValue s)).mp
    change Summable (fun n : ℕ+ => dirichletValue s (n : ℕ)) at hpnat
    exact hpnat
  have hshift : Filter.Tendsto (fun n : ℕ => n - 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro lower
    filter_upwards [Filter.eventually_ge_atTop (lower + 1)] with n hn
    omega
  apply (hnat.tendsto_atTop_zero.comp hshift).congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply, Nat.sub_add_cancel hn]

/-- C2 finite characteristics converge to the C2 profile series on `re s > 1`. -/
theorem finiteBracketCharacteristic_two_tendsto_profileSeries {s : ℂ}
    (hs : 1 < s.re) :
    Filter.Tendsto (fun cutoff => finiteBracketCharacteristic 2 cutoff s)
      Filter.atTop (nhds (coefficientDirichletSeries c2Profile s)) := by
  have hprefix := (coefficientDirichletPrefix_tendsto
    (c2ProfileDirichletTerm_summable hs)).comp
      (tendsto_nat_mul_add_atTop (slope := 4) (offset := 1) (by omega))
  change Filter.Tendsto
    (fun cutoff => coefficientDirichletPrefix c2Profile (4 * cutoff + 1) s)
      Filter.atTop (nhds (coefficientDirichletSeries c2Profile s)) at hprefix
  simpa only [finiteBracketCharacteristic_two_eq_profilePrefix] using hprefix

/-- Odd natural finite characteristics converge to their profile series on
`re s > 1`. -/
theorem finiteBracketCharacteristic_odd_tendsto_profileSeries {camera : ℕ}
    (hcamera : 3 ≤ camera) (hodd : Odd camera) {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun cutoff => finiteBracketCharacteristic camera cutoff s)
      Filter.atTop (nhds (coefficientDirichletSeries (oddProfile camera) s)) := by
  have hprefix := (coefficientDirichletPrefix_tendsto
    (oddProfileDirichletTerm_summable (camera := camera) (by omega) hs)).comp
      (tendsto_nat_mul_add_atTop (slope := camera) (offset := camera / 2) (by omega))
  change Filter.Tendsto
    (fun cutoff => coefficientDirichletPrefix (oddProfile camera)
      (camera * cutoff + camera / 2) s) Filter.atTop
      (nhds (coefficientDirichletSeries (oddProfile camera) s)) at hprefix
  simpa only [finiteBracketCharacteristic_odd_eq_profilePrefix hcamera hodd] using hprefix

/-- Even natural finite characteristics converge to their profile series; the
single antipodal endpoint correction vanishes. -/
theorem finiteBracketCharacteristic_even_tendsto_profileSeries {camera : ℕ}
    (hcamera : 4 ≤ camera) (heven : Even camera) {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun cutoff => finiteBracketCharacteristic camera cutoff s)
      Filter.atTop (nhds (coefficientDirichletSeries (evenProfile camera) s)) := by
  have hlength := tendsto_nat_mul_add_atTop (slope := camera)
    (offset := camera / 2) (by omega)
  have hprefix := (coefficientDirichletPrefix_tendsto
    (evenProfileDirichletTerm_summable hcamera heven hs)).comp hlength
  have hcorrection := (dirichletValue_tendsto_zero hs).comp hlength
  simpa only [Function.comp_apply, sub_zero,
    finiteBracketCharacteristic_even_eq_profilePrefix_sub hcamera heven] using
      hprefix.sub hcorrection

end

end NativeCarrySpectralWeyl.Camera.FiniteBridge
