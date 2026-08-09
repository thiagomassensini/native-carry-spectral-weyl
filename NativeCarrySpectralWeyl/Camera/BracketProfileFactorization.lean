import NativeCarrySpectralWeyl.Camera.BracketProfileBridge

/-!
# Infinite bracket/profile factorization

The finite stencil bridge is passed to the limit on `re s > 1`.  There the
normally convergent bracket characteristic agrees with the periodic-profile
Dirichlet series and therefore with the explicit camera factor times Mathlib's
`riemannZeta`.  The final theorem records the cross-factor identity on this
initial open half-plane.
-/

namespace NativeCarrySpectralWeyl.Camera

open FiniteBridge

noncomputable section

/-- On `re s > 1`, every supported finite bracket sequence converges to its
unified periodic-profile Dirichlet series. -/
theorem finiteBracketCharacteristic_tendsto_profileDirichletSeries
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun cutoff => finiteBracketCharacteristic camera cutoff s)
      Filter.atTop (nhds (profileDirichletSeries camera s)) := by
  by_cases h2 : camera = 2
  · subst camera
    unfold profileDirichletSeries
    rw [show profile 2 = c2Profile from funext profile_two]
    exact finiteBracketCharacteristic_two_tendsto_profileSeries hs
  · rcases Nat.even_or_odd camera with heven | hodd
    · have hcamera4 : 4 ≤ camera := by
        obtain ⟨half, hhalf⟩ := heven
        omega
      unfold profileDirichletSeries
      rw [show profile camera = evenProfile camera from
        funext (profile_of_even h2 heven)]
      exact finiteBracketCharacteristic_even_tendsto_profileSeries
        hcamera4 heven hs
    · have hcamera3 : 3 ≤ camera := by omega
      unfold profileDirichletSeries
      rw [show profile camera = oddProfile camera from
        funext (profile_of_odd h2 hodd)]
      exact finiteBracketCharacteristic_odd_tendsto_profileSeries
        hcamera3 hodd hs

/-- The normally convergent bracket characteristic agrees with the periodic
profile series in their common absolutely convergent half-plane. -/
theorem bracketCharacteristic_eq_profileDirichletSeries {camera : ℕ}
    (hcamera : 2 ≤ camera) {s : ℂ} (hs : 1 < s.re) :
    bracketCharacteristic camera s = profileDirichletSeries camera s := by
  exact tendsto_nhds_unique (finiteBracketCharacteristic_tendsto hcamera (by linarith))
    (finiteBracketCharacteristic_tendsto_profileDirichletSeries hcamera hs)

/-- Initial bracket factorization by Mathlib's zeta function on `re s > 1`. -/
theorem bracketCharacteristic_eq_factor_mul_riemannZeta {camera : ℕ}
    (hcamera : 2 ≤ camera) {s : ℂ} (hs : 1 < s.re) :
    bracketCharacteristic camera s = factor camera s * riemannZeta s := by
  rw [bracketCharacteristic_eq_profileDirichletSeries hcamera hs,
    profileDirichletSeries_eq_factor_mul_riemannZeta hcamera hs]

/-- The native cross-factor identity on its initial open half-plane. -/
theorem bracketCharacteristic_cross_eq_on_gt_one {camera : ℕ}
    (hcamera : 2 ≤ camera) {s : ℂ} (hs : 1 < s.re) :
    factor 3 s * bracketCharacteristic camera s =
      factor camera s * bracketCharacteristic 3 s := by
  rw [bracketCharacteristic_eq_factor_mul_riemannZeta hcamera hs,
    bracketCharacteristic_eq_factor_mul_riemannZeta (by omega : 2 ≤ 3) hs]
  ring

end


end NativeCarrySpectralWeyl.Camera
