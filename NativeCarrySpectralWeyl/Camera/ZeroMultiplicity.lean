import NativeCarrySpectralWeyl.Camera.CommonZeroSet
import Mathlib.Analysis.Analytic.Order

/-!
# Common analytic zero multiplicities

The source notes strengthen the common-zero-set theorem as follows.  At a
native-line point, every camera factor is holomorphic and nonzero, hence is a
unit in the local ring of analytic germs.  Multiplication by this local unit
does not change the order of vanishing of the common native scalar.

Mathlib's `analyticOrderAt : ℕ∞` expresses exactly this local invariant.  The
value `⊤` covers the degenerate case of a function that vanishes throughout a
neighborhood, so the equality below is valid without an unnecessary isolated-
zero hypothesis.  When one camera has a finite zero of order `m`, every other
supported camera has the same finite order `m`.
-/

open Set
open Filter
open scoped Topology

namespace NativeCarrySpectralWeyl.Camera

noncomputable section

/-- A supported camera factor that is nonzero at a point has analytic order
zero there; this is the local-unit statement used by the source notes. -/
theorem factor_analyticOrderAt_eq_zero_of_ne_zero {camera : ℕ}
    (hcamera : 2 ≤ camera) {s : ℂ} (hfactor : factor camera s ≠ 0) :
    analyticOrderAt (factor camera) s = 0 := by
  exact ((factor_differentiable hcamera).analyticAt s).analyticOrderAt_eq_zero.mpr
    hfactor

/-- The native scalar is analytic at every point of its canonical strip. -/
theorem nativeScalar_analyticAt {s : ℂ} (hs : s ∈ nativeScalarDomain) :
    AnalyticAt ℂ nativeScalar s :=
  nativeScalar_differentiableOn.analyticAt
    (isOpen_nativeScalarDomain.mem_nhds hs)

/-- The strip factorization is an equality of germs at each point of the
native-scalar domain. -/
theorem bracketCharacteristic_eventuallyEq_factor_mul_nativeScalar
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ nativeScalarDomain) :
    bracketCharacteristic camera =ᶠ[𝓝 s]
      fun z => factor camera z * nativeScalar z := by
  filter_upwards [isOpen_nativeScalarDomain.mem_nhds hs] with z hz
  exact bracketCharacteristic_eq_factor_mul_nativeScalar hcamera hz

/-- Multiplication by a nonvanishing camera factor preserves the analytic
order of the native scalar. -/
theorem bracketCharacteristic_analyticOrderAt_eq_nativeScalar_of_factor_ne_zero
    {camera : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ nativeScalarDomain) (hfactor : factor camera s ≠ 0) :
    analyticOrderAt (bracketCharacteristic camera) s =
      analyticOrderAt nativeScalar s := by
  have hfactorAnalytic : AnalyticAt ℂ (factor camera) s :=
    (factor_differentiable hcamera).analyticAt s
  have hscalarAnalytic : AnalyticAt ℂ nativeScalar s := nativeScalar_analyticAt hs
  calc
    analyticOrderAt (bracketCharacteristic camera) s =
        analyticOrderAt (fun z => factor camera z * nativeScalar z) s :=
      analyticOrderAt_congr
        (bracketCharacteristic_eventuallyEq_factor_mul_nativeScalar hcamera hs)
    _ = analyticOrderAt (factor camera) s + analyticOrderAt nativeScalar s := by
      exact analyticOrderAt_mul hfactorAnalytic hscalarAnalytic
    _ = analyticOrderAt nativeScalar s := by
      rw [factor_analyticOrderAt_eq_zero_of_ne_zero hcamera hfactor, zero_add]

/-- Every supported camera characteristic has exactly the native scalar's
analytic order at every native-line point. -/
theorem bracketCharacteristic_nativeLine_analyticOrderAt_eq_nativeScalar
    {camera : ℕ} (hcamera : 2 ≤ camera) (t : ℝ) :
    analyticOrderAt (bracketCharacteristic camera) (nativeLine t) =
      analyticOrderAt nativeScalar (nativeLine t) := by
  apply bracketCharacteristic_analyticOrderAt_eq_nativeScalar_of_factor_ne_zero
    hcamera
  · simp [nativeScalarDomain]
    norm_num
  · exact factor_nativeLine_ne_zero hcamera t

/-- Source theorem: any two supported camera characteristics have the same
analytic zero multiplicity at every native-line point. -/
theorem bracketCharacteristic_nativeLine_common_analyticOrder
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (t : ℝ) :
    analyticOrderAt (bracketCharacteristic camera₁) (nativeLine t) =
      analyticOrderAt (bracketCharacteristic camera₂) (nativeLine t) := by
  rw [bracketCharacteristic_nativeLine_analyticOrderAt_eq_nativeScalar hcamera₁,
    bracketCharacteristic_nativeLine_analyticOrderAt_eq_nativeScalar hcamera₂]

/-- Natural-valued form of the common analytic order.  For a finite isolated
zero this is its usual multiplicity. -/
theorem bracketCharacteristic_nativeLine_common_analyticOrderNat
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (t : ℝ) :
    analyticOrderNatAt (bracketCharacteristic camera₁) (nativeLine t) =
      analyticOrderNatAt (bracketCharacteristic camera₂) (nativeLine t) := by
  unfold analyticOrderNatAt
  rw [bracketCharacteristic_nativeLine_common_analyticOrder hcamera₁ hcamera₂]

/-- If one supported camera has a zero of finite analytic order `order`, every
other supported camera has that same order. -/
theorem bracketCharacteristic_nativeLine_zero_order_transfer
    {camera₁ camera₂ order : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (t : ℝ)
    (hzero : bracketCharacteristic camera₁ (nativeLine t) = 0)
    (horder : analyticOrderAt (bracketCharacteristic camera₁) (nativeLine t) =
      (order : ℕ∞)) :
    0 < order ∧
      analyticOrderAt (bracketCharacteristic camera₂) (nativeLine t) =
        (order : ℕ∞) := by
  have hdomain : nativeLine t ∈ bracketDomain := by
    simp [bracketDomain]
    norm_num
  have hanalytic : AnalyticAt ℂ (bracketCharacteristic camera₁) (nativeLine t) :=
    (bracketCharacteristic_differentiableOn hcamera₁).analyticAt
      (isOpen_bracketDomain.mem_nhds hdomain)
  have horderNe : (order : ℕ∞) ≠ 0 := by
    rw [← horder]
    exact hanalytic.analyticOrderAt_ne_zero.mpr hzero
  constructor
  · exact Nat.pos_of_ne_zero (by
      intro hzeroOrder
      subst order
      exact horderNe rfl)
  · rw [← horder]
    exact (bracketCharacteristic_nativeLine_common_analyticOrder
      hcamera₁ hcamera₂ t).symm

end

end NativeCarrySpectralWeyl.Camera
