import NativeCarrySpectralWeyl.Camera.BracketProfileFactorization
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-!
# Analytic continuation of the native cross-factor identity

The explicit factors are entire and the bracket characteristics are
holomorphic on `re s > -1`.  Since their cross identity was proved on the
nonempty open sub-half-plane `re s > 1`, the analytic identity principle
extends it to the whole connected bracket domain.

This module proves the cross identity itself.  Division by the camera-3 factor,
nonvanishing strips, common-zero sets and multiplicity remain downstream
obligations.
-/

open Set
open scoped Topology

namespace NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Positive natural bases raised to an affine complex exponent are entire. -/
theorem natCastCpow_const_sub_differentiable (n : ℕ) (hn : 0 < n) (a : ℂ) :
    Differentiable ℂ (fun s : ℂ => (n : ℂ) ^ (a - s)) := by
  exact ((differentiable_const (c := a)).sub differentiable_id).const_cpow
    (Or.inl (by exact_mod_cast hn.ne'))

theorem c2Factor_differentiable : Differentiable ℂ c2Factor := by
  have hneg : Differentiable ℂ (fun s : ℂ => (2 : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (by norm_num))
  have hone := natCastCpow_const_sub_differentiable 2 (by omega) 1
  intro s
  exact ((differentiableAt_const (c := (1 : ℂ))).add (hneg s)).mul
    ((differentiableAt_const (c := (1 : ℂ))).sub (hone s))

theorem oddFactor_differentiable {camera : ℕ} (hcamera : 0 < camera) :
    Differentiable ℂ (oddFactor camera) := by
  exact (differentiable_const (c := (1 : ℂ))).sub
    (natCastCpow_const_sub_differentiable camera hcamera 1)

theorem evenFactor_differentiable {camera : ℕ} (hcamera : 4 ≤ camera) :
    Differentiable ℂ (evenFactor camera) := by
  have hhalf : 0 < camera / 2 := by omega
  have hhalfPow : Differentiable ℂ
      (fun s : ℂ => ((camera / 2 : ℕ) : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast hhalf.ne'))
  have hcameraPow : Differentiable ℂ (fun s : ℂ => (camera : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : camera ≠ 0)))
  intro s
  exact ((differentiableAt_const (c := (1 : ℂ))).add (hhalfPow s)).sub
    ((hcameraPow s).const_mul ((camera + 2 : ℕ) : ℂ))

/-- Every supported explicit camera factor is entire. -/
theorem factor_differentiable {camera : ℕ} (hcamera : 2 ≤ camera) :
    Differentiable ℂ (factor camera) := by
  by_cases h2 : camera = 2
  · subst camera
    change Differentiable ℂ (fun s => c2Factor s)
    exact c2Factor_differentiable
  · rcases Nat.even_or_odd camera with heven | hodd
    · have hcamera4 : 4 ≤ camera := by
        obtain ⟨half, hhalf⟩ := heven
        omega
      change Differentiable ℂ (fun s => if camera = 2 then c2Factor s
        else if Odd camera then oddFactor camera s else evenFactor camera s)
      have hnotodd : ¬Odd camera := Nat.not_odd_iff_even.mpr heven
      simp only [h2, hnotodd, if_false]
      exact evenFactor_differentiable hcamera4
    · change Differentiable ℂ (fun s => if camera = 2 then _
          else if Odd camera then oddFactor camera s else evenFactor camera s)
      simp only [h2, hodd, if_false, if_true]
      exact oddFactor_differentiable (camera := camera) (by omega)

/-- The bracket domain is convex, hence preconnected. -/
theorem isPreconnected_bracketDomain : IsPreconnected bracketDomain := by
  simpa only [bracketDomain] using (convex_halfSpace_re_gt (-1)).isPreconnected

/-- Analytic continuation of the cross-factor identity from `re s > 1` to
the full normally convergent half-plane `re s > -1`. -/
theorem bracketCharacteristic_cross_eq {camera : ℕ} (hcamera : 2 ≤ camera)
    {s : ℂ} (hs : s ∈ bracketDomain) :
    factor 3 s * bracketCharacteristic camera s =
      factor camera s * bracketCharacteristic 3 s := by
  let lhs : ℂ → ℂ := fun z => factor 3 z * bracketCharacteristic camera z
  let rhs : ℂ → ℂ := fun z => factor camera z * bracketCharacteristic 3 z
  have hlhsDiff : DifferentiableOn ℂ lhs bracketDomain :=
    (factor_differentiable (by omega : 2 ≤ 3)).differentiableOn.mul
      (bracketCharacteristic_differentiableOn hcamera)
  have hrhsDiff : DifferentiableOn ℂ rhs bracketDomain :=
    (factor_differentiable hcamera).differentiableOn.mul
      (bracketCharacteristic_differentiableOn (by omega : 2 ≤ 3))
  have hlhs : AnalyticOnNhd ℂ lhs bracketDomain :=
    hlhsDiff.analyticOnNhd isOpen_bracketDomain
  have hrhs : AnalyticOnNhd ℂ rhs bracketDomain :=
    hrhsDiff.analyticOnNhd isOpen_bracketDomain
  have htwo : (2 : ℂ) ∈ bracketDomain := by norm_num [bracketDomain]
  have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have heq : lhs =ᶠ[𝓝 (2 : ℂ)] rhs := by
    apply Filter.eventually_of_mem hopen
    intro z hz
    exact bracketCharacteristic_cross_eq_on_gt_one hcamera hz
  exact hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs
    isPreconnected_bracketDomain htwo heq hs

end

end NativeCarrySpectralWeyl.Camera
