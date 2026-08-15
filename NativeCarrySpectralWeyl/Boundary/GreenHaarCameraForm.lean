import NativeCarrySpectralWeyl.Infinite.Naimark

/-!
# Form-first Green/Haar interface on the all-bases camera completion

This module provides only the functional-analytic infrastructure needed by a
future research-specific Green/Haar core formula.

A bounded real functional on the finitely supported intrinsic Gram core has a
unique continuous extension to `CameraHilbert`.  The extension agrees on the
core, preserves its exact operator norm, and restricts to every isometrically
embedded atlas with the same bound.  The concrete finite-label restrictions
are compatible under enlargement.

The explicit Naimark realization supplies the canonical target functional

`u ↦ inner g (naimarkIsometry u)`.

It is the unique extension of the corresponding core pairing and has bound
`‖g‖`; hence a unit source gives an atlas-independent constant one.

No research-specific Green/Haar formula, source realization, vector-valued
synthesis, zero statement, or confinement result is asserted here.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

abbrev CameraCoreFunctional := CameraFinsupp →L[ℝ] ℝ

abbrev CameraHilbertFunctional := CameraHilbert →L[ℝ] ℝ

def extendCameraCoreFunctional
    (q : CameraCoreFunctional) : CameraHilbertFunctional :=
  q.extend cameraEmbedding.toContinuousLinearMap

@[simp] theorem extendCameraCoreFunctional_cameraEmbedding
    (q : CameraCoreFunctional) (u : CameraFinsupp) :
    extendCameraCoreFunctional q (cameraEmbedding u) = q u := by
  exact ContinuousLinearMap.extend_eq q cameraEmbedding_denseRange
    cameraEmbedding.isometry.isUniformInducing u

theorem extendCameraCoreFunctional_unique
    (q : CameraCoreFunctional) (Q : CameraHilbertFunctional)
    (hQ : ∀ u : CameraFinsupp, Q (cameraEmbedding u) = q u) :
    Q = extendCameraCoreFunctional q := by
  symm
  apply ContinuousLinearMap.extend_unique q cameraEmbedding_denseRange
    cameraEmbedding.isometry.isUniformInducing Q
  ext u
  exact hQ u

theorem extendCameraCoreFunctional_norm_le
    (q : CameraCoreFunctional) :
    ‖extendCameraCoreFunctional q‖ ≤ ‖q‖ := by
  apply (extendCameraCoreFunctional q).opNorm_le_bound (norm_nonneg q)
  intro x
  refine cameraEmbedding_denseRange.induction_on
    (p := fun y => ‖extendCameraCoreFunctional q y‖ ≤ ‖q‖ * ‖y‖)
    x ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp (extendCameraCoreFunctional q).continuous)
      (continuous_const.mul continuous_norm)
  · intro u
    rw [extendCameraCoreFunctional_cameraEmbedding, cameraEmbedding.norm_map]
    exact q.le_opNorm u

theorem extendCameraCoreFunctional_norm
    (q : CameraCoreFunctional) :
    ‖extendCameraCoreFunctional q‖ = ‖q‖ := by
  apply le_antisymm (extendCameraCoreFunctional_norm_le q)
  apply q.opNorm_le_bound
    (show (0 : ℝ) ≤ ‖extendCameraCoreFunctional q‖ by positivity)
  intro u
  rw [← extendCameraCoreFunctional_cameraEmbedding q u]
  simpa using (extendCameraCoreFunctional q).le_opNorm (cameraEmbedding u)

theorem extendCameraCoreFunctional_add
    (q r : CameraCoreFunctional) :
    extendCameraCoreFunctional (q + r) =
      extendCameraCoreFunctional q + extendCameraCoreFunctional r := by
  apply ContinuousLinearMap.extend_unique
    (q + r) cameraEmbedding_denseRange
    cameraEmbedding.isometry.isUniformInducing
  ext u
  change (extendCameraCoreFunctional q) (cameraEmbedding u) +
      (extendCameraCoreFunctional r) (cameraEmbedding u) = q u + r u
  rw [extendCameraCoreFunctional_cameraEmbedding,
    extendCameraCoreFunctional_cameraEmbedding]

theorem extendCameraCoreFunctional_smul
    (a : ℝ) (q : CameraCoreFunctional) :
    extendCameraCoreFunctional (a • q) =
      a • extendCameraCoreFunctional q := by
  apply ContinuousLinearMap.extend_unique
    (a • q) cameraEmbedding_denseRange
    cameraEmbedding.isometry.isUniformInducing
  ext u
  change a * (extendCameraCoreFunctional q) (cameraEmbedding u) = a * q u
  rw [extendCameraCoreFunctional_cameraEmbedding]

def cameraFunctionalExtensionIsometry :
    CameraCoreFunctional →ₗᵢ[ℝ] CameraHilbertFunctional where
  toLinearMap :=
    { toFun := extendCameraCoreFunctional
      map_add' := extendCameraCoreFunctional_add
      map_smul' := extendCameraCoreFunctional_smul }
  norm_map' := extendCameraCoreFunctional_norm

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def restrictCameraCoreFunctional
    (q : CameraCoreFunctional) (inclusion : A →ₗᵢ[ℝ] CameraHilbert) :
    A →L[ℝ] ℝ :=
  (extendCameraCoreFunctional q).comp inclusion.toContinuousLinearMap

@[simp] theorem restrictCameraCoreFunctional_apply
    (q : CameraCoreFunctional) (inclusion : A →ₗᵢ[ℝ] CameraHilbert)
    (u : A) :
    restrictCameraCoreFunctional q inclusion u =
      extendCameraCoreFunctional q (inclusion u) := rfl

theorem restrictCameraCoreFunctional_bound
    (q : CameraCoreFunctional) (inclusion : A →ₗᵢ[ℝ] CameraHilbert)
    (u : A) :
    ‖restrictCameraCoreFunctional q inclusion u‖ ≤ ‖q‖ * ‖u‖ := by
  change ‖extendCameraCoreFunctional q (inclusion u)‖ ≤ ‖q‖ * ‖u‖
  rw [← extendCameraCoreFunctional_norm q, ← inclusion.norm_map u]
  exact (extendCameraCoreFunctional q).le_opNorm (inclusion u)

theorem restrictCameraCoreFunctional_norm_le
    (q : CameraCoreFunctional) (inclusion : A →ₗᵢ[ℝ] CameraHilbert) :
    ‖restrictCameraCoreFunctional q inclusion‖ ≤ ‖q‖ := by
  apply (restrictCameraCoreFunctional q inclusion).opNorm_le_bound
    (norm_nonneg q)
  exact restrictCameraCoreFunctional_bound q inclusion

def finiteCameraFunctional
    (q : CameraCoreFunctional) (bound : ℕ) :
    finiteCameraSubspace bound →L[ℝ] ℝ :=
  restrictCameraCoreFunctional q (finiteCameraInclusion bound)

@[simp] theorem finiteCameraFunctional_apply
    (q : CameraCoreFunctional) (bound : ℕ)
    (u : finiteCameraSubspace bound) :
    finiteCameraFunctional q bound u =
      extendCameraCoreFunctional q (cameraEmbedding u.1) := rfl

theorem finiteCameraFunctional_bound
    (q : CameraCoreFunctional) (bound : ℕ)
    (u : finiteCameraSubspace bound) :
    ‖finiteCameraFunctional q bound u‖ ≤ ‖q‖ * ‖u‖ :=
  restrictCameraCoreFunctional_bound q (finiteCameraInclusion bound) u

theorem finiteCameraFunctional_compatible
    (q : CameraCoreFunctional) {bound₁ bound₂ : ℕ}
    (hbound : bound₁ ≤ bound₂) (u : finiteCameraSubspace bound₁) :
    finiteCameraFunctional q bound₂
        ⟨u.1, finiteCameraSubspace_mono hbound u.2⟩ =
      finiteCameraFunctional q bound₁ u := by
  simp only [finiteCameraFunctional_apply]

def naimarkCoreCameraFunctional (g : NaimarkSpace) :
    CameraCoreFunctional :=
  (innerSL ℝ g).comp naimarkCoreIsometry.toContinuousLinearMap

def naimarkCameraFunctional (g : NaimarkSpace) :
    CameraHilbertFunctional :=
  (innerSL ℝ g).comp naimarkIsometry.toContinuousLinearMap

@[simp] theorem naimarkCoreCameraFunctional_apply
    (g : NaimarkSpace) (u : CameraFinsupp) :
    naimarkCoreCameraFunctional g u =
      inner ℝ g (naimarkCoreIsometry u) := rfl

@[simp] theorem naimarkCameraFunctional_apply
    (g : NaimarkSpace) (u : CameraHilbert) :
    naimarkCameraFunctional g u =
      inner ℝ g (naimarkIsometry u) := rfl

theorem extend_naimarkCoreCameraFunctional
    (g : NaimarkSpace) :
    extendCameraCoreFunctional (naimarkCoreCameraFunctional g) =
      naimarkCameraFunctional g := by
  apply ContinuousLinearMap.extend_unique
    (naimarkCoreCameraFunctional g) cameraEmbedding_denseRange
    cameraEmbedding.isometry.isUniformInducing
  ext u
  change inner ℝ g (naimarkIsometry (cameraEmbedding u)) =
    inner ℝ g (naimarkCoreIsometry u)
  rw [naimarkIsometry_cameraEmbedding]

theorem naimarkCameraFunctional_bound
    (g : NaimarkSpace) (u : CameraHilbert) :
    ‖naimarkCameraFunctional g u‖ ≤ ‖g‖ * ‖u‖ := by
  rw [naimarkCameraFunctional_apply]
  simpa only [naimarkIsometry.norm_map] using
    (norm_inner_le_norm g (naimarkIsometry u))

theorem naimarkCameraFunctional_norm_le (g : NaimarkSpace) :
    ‖naimarkCameraFunctional g‖ ≤ ‖g‖ := by
  apply (naimarkCameraFunctional g).opNorm_le_bound (norm_nonneg g)
  exact naimarkCameraFunctional_bound g

theorem naimarkCameraFunctional_bound_one
    {g : NaimarkSpace} (hg : ‖g‖ ≤ 1) (u : CameraHilbert) :
    ‖naimarkCameraFunctional g u‖ ≤ ‖u‖ := by
  calc
    ‖naimarkCameraFunctional g u‖ ≤ ‖g‖ * ‖u‖ :=
      naimarkCameraFunctional_bound g u
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg u)
    _ = ‖u‖ := one_mul _

end NativeCarrySpectralWeyl.Infinite
