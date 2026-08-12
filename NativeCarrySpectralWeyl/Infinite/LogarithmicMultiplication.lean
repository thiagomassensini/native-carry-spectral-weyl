import NativeCarrySpectralWeyl.Finite.StepDensity
import NativeCarrySpectralWeyl.Infinite.Naimark
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The logarithmic multiplication operator on the all-bases Naimark space

The explicit Naimark dilation lives in

`NaimarkSpace = L² ((0, ∞), KolmogorovSpace)`.

This file installs the spectral coordinate from the research notes,

`y(x) = 1 + log x`,

and defines multiplication by `y` on its natural maximal domain

`{f ∈ L² : y f ∈ L²}`.

The operator is bundled as a Mathlib `LinearPMap`.  Its domain contains every
explicit camera step vector and hence the finite all-bases camera core.  The
domain is dense in the whole Naimark space: multiplication by the bounded,
strictly positive regularizer `(1 + |y|)⁻¹` has dense range, and that range
lies in the maximal domain.  Finally, multiplication by the real coordinate
is symmetric in the precise `LinearPMap.IsFormalAdjoint` sense.

Closedness and equality with the Hilbert-space adjoint are intentionally left
to the next operator-theoretic layer; no self-adjointness claim is made here.
-/

open scoped ENNReal MeasureTheory RealInnerProductSpace
open Set MeasureTheory

noncomputable section

namespace NativeCarrySpectralWeyl.Infinite

open NativeCarrySpectralWeyl.Camera

/-- The spectral coordinate used throughout the finite moment and all-bases
Naimark notes. -/
def logarithmicCoordinate (x : ℝ) : ℝ :=
  1 + Real.log x

/-- The logarithmic spectral coordinate is measurable. -/
theorem measurable_logarithmicCoordinate : Measurable logarithmicCoordinate := by
  exact measurable_const.add Real.measurable_log

/-- Pointwise multiplication of an `L²` representative by the logarithmic
coordinate. -/
def logarithmicWeightedFunction (f : NaimarkSpace) (x : ℝ) : KolmogorovSpace :=
  logarithmicCoordinate x • f x

/-- The weighted representative is strongly measurable, whether or not it is
square integrable. -/
theorem logarithmicWeightedFunction_aestronglyMeasurable (f : NaimarkSpace) :
    AEStronglyMeasurable (logarithmicWeightedFunction f)
      positiveLebesgueMeasure := by
  exact measurable_logarithmicCoordinate.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable f)

/-- Multiplication by the coordinate respects addition, almost everywhere
for the canonical `L²` representatives. -/
theorem logarithmicWeightedFunction_add (f g : NaimarkSpace) :
    logarithmicWeightedFunction (f + g) =ᵐ[positiveLebesgueMeasure]
      logarithmicWeightedFunction f + logarithmicWeightedFunction g := by
  filter_upwards [Lp.coeFn_add f g] with x hx
  simp only [Pi.add_apply, logarithmicWeightedFunction]
  rw [hx]
  simp only [Pi.add_apply, smul_add]

/-- Multiplication by the coordinate respects real scalar multiplication,
almost everywhere for the canonical `L²` representatives. -/
theorem logarithmicWeightedFunction_smul (c : ℝ) (f : NaimarkSpace) :
    logarithmicWeightedFunction (c • f) =ᵐ[positiveLebesgueMeasure]
      c • logarithmicWeightedFunction f := by
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp only [Pi.smul_apply, logarithmicWeightedFunction]
  rw [hx]
  simp [smul_smul, mul_comm]

/-- Multiplication by the coordinate sends the zero `L²` vector to zero
almost everywhere. -/
theorem logarithmicWeightedFunction_zero :
    logarithmicWeightedFunction (0 : NaimarkSpace) =ᵐ[positiveLebesgueMeasure] 0 := by
  filter_upwards [Lp.coeFn_zero (E := KolmogorovSpace)
    (p := (2 : ℝ≥0∞)) (positiveLebesgueMeasure)] with x hx
  change logarithmicCoordinate x • (0 : NaimarkSpace) x = 0
  rw [hx]
  simp

/-- Natural maximal domain of multiplication by `1 + log x`. -/
def logarithmicMultiplicationDomain : Submodule ℝ NaimarkSpace where
  carrier := {f | MemLp (logarithmicWeightedFunction f) 2 positiveLebesgueMeasure}
  zero_mem' := by
    exact MemLp.zero.ae_eq logarithmicWeightedFunction_zero.symm
  add_mem' {f g} hf hg := by
    exact (hf.add hg).ae_eq (logarithmicWeightedFunction_add f g).symm
  smul_mem' c f hf := by
    exact (hf.const_smul c).ae_eq (logarithmicWeightedFunction_smul c f).symm

/-- Membership in the natural domain is exactly square integrability after
multiplication by the logarithmic coordinate. -/
theorem mem_logarithmicMultiplicationDomain_iff (f : NaimarkSpace) :
    f ∈ logarithmicMultiplicationDomain ↔
      MemLp (logarithmicWeightedFunction f) 2 positiveLebesgueMeasure :=
  Iff.rfl

/-- A domain element carries the square-integrability witness needed to form
its image in `L²`. -/
theorem logarithmicWeightedFunction_memLp
    (f : logarithmicMultiplicationDomain) :
    MemLp (logarithmicWeightedFunction (f : NaimarkSpace)) 2
      positiveLebesgueMeasure :=
  f.property

/-- Multiplication by `1 + log x`, as a linear map from its natural domain. -/
def logarithmicMultiplicationLinearMap :
    logarithmicMultiplicationDomain →ₗ[ℝ] NaimarkSpace where
  toFun f := (logarithmicWeightedFunction_memLp f).toLp
    (logarithmicWeightedFunction f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr (logarithmicWeightedFunction_memLp (f + g))
      ((logarithmicWeightedFunction_memLp f).add
        (logarithmicWeightedFunction_memLp g))
      (logarithmicWeightedFunction_add f g)
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr (logarithmicWeightedFunction_memLp (c • f))
      ((logarithmicWeightedFunction_memLp f).const_smul c)
      (logarithmicWeightedFunction_smul c f)

/-- The unbounded logarithmic multiplication operator, bundled as a partial
linear map on `NaimarkSpace`. -/
def logarithmicMultiplication : NaimarkSpace →ₗ.[ℝ] NaimarkSpace where
  domain := logarithmicMultiplicationDomain
  toFun := logarithmicMultiplicationLinearMap

/-- The partial operator has the documented natural maximal domain. -/
@[simp] theorem logarithmicMultiplication_domain :
    logarithmicMultiplication.domain = logarithmicMultiplicationDomain :=
  rfl

/-- On its domain, the partial operator acts almost everywhere by
`f(x) ↦ (1 + log x) f(x)`. -/
theorem logarithmicMultiplication_coeFn
    (f : logarithmicMultiplication.domain) :
    ⇑(logarithmicMultiplication f) =ᵐ[positiveLebesgueMeasure]
      logarithmicWeightedFunction (f : NaimarkSpace) :=
  f.property.coeFn_toLp

/-- The scalar logarithmic coordinate, cut off to one camera interval, is in
`L²` on the positive half-line.  This is the analytic endpoint estimate that
makes every explicit Naimark camera vector belong to the operator domain. -/
theorem memLp_indicator_logarithmicCoordinate (camera : CameraIndex) :
    MemLp ((cameraInterval camera).indicator logarithmicCoordinate) 2
      positiveLebesgueMeasure := by
  have hmeas : AEStronglyMeasurable
      ((cameraInterval camera).indicator logarithmicCoordinate)
      positiveLebesgueMeasure :=
    (measurable_logarithmicCoordinate.indicator
      (cameraInterval_measurable camera)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hslope : (0 : ℝ) < cameraSlope (cameraLabel camera) := by
    exact_mod_cast cameraSlope_pos camera
  have hint : IntegrableOn (fun x : ℝ => logarithmicCoordinate x ^ 2)
      (cameraInterval camera) volume := by
    rw [cameraInterval]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hslope.le).mp
      (by simpa [logarithmicCoordinate] using
        NativeCarrySpectralWeyl.Finite.intervalIntegrable_centeredLogSq_zero hslope)
  have hvolume : Integrable
      ((cameraInterval camera).indicator
        (fun x : ℝ => logarithmicCoordinate x ^ 2)) volume :=
    hint.integrable_indicator (cameraInterval_measurable camera)
  have hpositive : Integrable
      ((cameraInterval camera).indicator
        (fun x : ℝ => logarithmicCoordinate x ^ 2))
      positiveLebesgueMeasure := by
    rw [positiveLebesgueMeasure]
    exact hvolume.mono_measure Measure.restrict_le_self
  apply hpositive.congr
  filter_upwards with x
  by_cases hx : x ∈ cameraInterval camera
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- Every explicit Naimark camera step vector lies in the natural domain of
the logarithmic multiplication operator. -/
theorem naimarkCameraVector_mem_logarithmicMultiplicationDomain
    (camera : CameraIndex) :
    naimarkCameraVector camera ∈ logarithmicMultiplicationDomain := by
  rw [mem_logarithmicMultiplicationDomain_iff]
  have hscalar := memLp_indicator_logarithmicCoordinate camera
  have hcomposed : MemLp
      ((ContinuousLinearMap.toSpanSingleton ℝ (kolmogorovVector camera)) ∘
        (cameraInterval camera).indicator logarithmicCoordinate)
      2 positiveLebesgueMeasure :=
    (ContinuousLinearMap.toSpanSingleton ℝ
      (kolmogorovVector camera)).comp_memLp' hscalar
  have hindicator : MemLp
      (fun x : ℝ => logarithmicCoordinate x •
        (cameraInterval camera).indicator
          (fun _ => kolmogorovVector camera) x)
      2 positiveLebesgueMeasure := by
    apply hcomposed.ae_eq
    filter_upwards with x
    by_cases hx : x ∈ cameraInterval camera
    · simp [Function.comp_apply, Set.indicator_of_mem hx,
        ContinuousLinearMap.toSpanSingleton_apply]
    · simp [Function.comp_apply, Set.indicator_of_notMem hx,
        ContinuousLinearMap.toSpanSingleton_apply]
  apply hindicator.ae_eq
  filter_upwards [naimarkCameraVector_coeFn camera] with x hx
  exact congrArg (fun value => logarithmicCoordinate x • value) hx.symm

/-- The finite all-bases camera core lies in the natural logarithmic domain. -/
theorem naimarkCoreMap_mem_logarithmicMultiplicationDomain
    (u : CameraFinsupp) :
    naimarkCoreMap u ∈ logarithmicMultiplicationDomain := by
  classical
  rw [naimarkCoreMap_apply]
  exact Submodule.sum_mem logarithmicMultiplicationDomain fun camera _ =>
    Submodule.smul_mem logarithmicMultiplicationDomain _
      (naimarkCameraVector_mem_logarithmicMultiplicationDomain camera)

/-! ## Density of the maximal domain -/

/-- Bounded, strictly positive regularizer used to exhibit a dense subspace
inside the maximal logarithmic domain. -/
def logarithmicRegularizer (x : ℝ) : ℝ :=
  (1 + |logarithmicCoordinate x|)⁻¹

/-- The regularizer is measurable. -/
theorem measurable_logarithmicRegularizer : Measurable logarithmicRegularizer := by
  have hnorm : Measurable (fun x => ‖logarithmicCoordinate x‖) :=
    measurable_logarithmicCoordinate.norm
  have habs : Measurable (fun x => |logarithmicCoordinate x|) := by
    simpa only [Real.norm_eq_abs] using hnorm
  have hden : Measurable (fun x => 1 + |logarithmicCoordinate x|) :=
    measurable_const.add habs
  change Measurable (fun x => (1 + |logarithmicCoordinate x|)⁻¹)
  exact measurable_inv.comp hden

/-- The regularizer is strictly positive at every point. -/
theorem logarithmicRegularizer_pos (x : ℝ) :
    0 < logarithmicRegularizer x := by
  rw [logarithmicRegularizer, inv_pos]
  positivity

/-- The regularizer is bounded above by one. -/
theorem logarithmicRegularizer_le_one (x : ℝ) :
    logarithmicRegularizer x ≤ 1 := by
  rw [logarithmicRegularizer]
  exact inv_le_one_of_one_le₀
    (by linarith [abs_nonneg (logarithmicCoordinate x)])

/-- Multiplying the coordinate by the regularizer remains bounded by one. -/
theorem abs_logarithmicCoordinate_mul_regularizer_le_one (x : ℝ) :
    |logarithmicCoordinate x| * logarithmicRegularizer x ≤ 1 := by
  rw [logarithmicRegularizer]
  exact mul_inv_le_one_of_le₀ (by linarith [abs_nonneg (logarithmicCoordinate x)])
    (by positivity)

/-- Pointwise regularization of an `L²` representative. -/
def logarithmicRegularizedFunction (f : NaimarkSpace) (x : ℝ) :
    KolmogorovSpace :=
  logarithmicRegularizer x • f x

/-- Regularized representatives are strongly measurable. -/
theorem logarithmicRegularizedFunction_aestronglyMeasurable
    (f : NaimarkSpace) :
    AEStronglyMeasurable (logarithmicRegularizedFunction f)
      positiveLebesgueMeasure := by
  exact measurable_logarithmicRegularizer.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable f)

/-- Pointwise regularization preserves square integrability. -/
theorem logarithmicRegularizedFunction_memLp (f : NaimarkSpace) :
    MemLp (logarithmicRegularizedFunction f) 2 positiveLebesgueMeasure := by
  apply (Lp.memLp f).of_le_mul
    (logarithmicRegularizedFunction_aestronglyMeasurable f)
  filter_upwards with x
  rw [logarithmicRegularizedFunction, norm_smul, Real.norm_eq_abs,
    abs_of_pos (logarithmicRegularizer_pos x), one_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (logarithmicRegularizer_le_one x)
      (norm_nonneg (f x))

/-- Regularization respects addition almost everywhere. -/
theorem logarithmicRegularizedFunction_add (f g : NaimarkSpace) :
    logarithmicRegularizedFunction (f + g) =ᵐ[positiveLebesgueMeasure]
      logarithmicRegularizedFunction f + logarithmicRegularizedFunction g := by
  filter_upwards [Lp.coeFn_add f g] with x hx
  simp only [Pi.add_apply, logarithmicRegularizedFunction]
  rw [hx]
  simp only [Pi.add_apply, smul_add]

/-- Regularization respects real scalar multiplication almost everywhere. -/
theorem logarithmicRegularizedFunction_smul (c : ℝ) (f : NaimarkSpace) :
    logarithmicRegularizedFunction (c • f) =ᵐ[positiveLebesgueMeasure]
      c • logarithmicRegularizedFunction f := by
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp only [Pi.smul_apply, logarithmicRegularizedFunction]
  rw [hx]
  simp [smul_smul, mul_comm]

/-- Bounded regularization as a linear endomorphism of the Naimark space. -/
def logarithmicRegularizationLinearMap : NaimarkSpace →ₗ[ℝ] NaimarkSpace where
  toFun f := (logarithmicRegularizedFunction_memLp f).toLp
    (logarithmicRegularizedFunction f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr (logarithmicRegularizedFunction_memLp (f + g))
      ((logarithmicRegularizedFunction_memLp f).add
        (logarithmicRegularizedFunction_memLp g))
      (logarithmicRegularizedFunction_add f g)
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr (logarithmicRegularizedFunction_memLp (c • f))
      ((logarithmicRegularizedFunction_memLp f).const_smul c)
      (logarithmicRegularizedFunction_smul c f)

/-- Almost-everywhere action of the bounded regularization map. -/
theorem logarithmicRegularizationLinearMap_coeFn (f : NaimarkSpace) :
    ⇑(logarithmicRegularizationLinearMap f) =ᵐ[positiveLebesgueMeasure]
      logarithmicRegularizedFunction f :=
  (logarithmicRegularizedFunction_memLp f).coeFn_toLp

/-- The range of the bounded regularizer lies in the maximal domain of the
unbounded logarithmic multiplier. -/
theorem logarithmicRegularizationLinearMap_mem_domain (f : NaimarkSpace) :
    logarithmicRegularizationLinearMap f ∈
      logarithmicMultiplicationDomain := by
  rw [mem_logarithmicMultiplicationDomain_iff]
  have hraw : MemLp
      (fun x : ℝ => logarithmicCoordinate x •
        logarithmicRegularizedFunction f x)
      2 positiveLebesgueMeasure := by
    apply (Lp.memLp f).of_le_mul
      (measurable_logarithmicCoordinate.aestronglyMeasurable.smul
        (logarithmicRegularizedFunction_aestronglyMeasurable f))
    filter_upwards with x
    change ‖logarithmicCoordinate x •
      (logarithmicRegularizer x • f x)‖ ≤ 1 * ‖f x‖
    rw [norm_smul, norm_smul]
    simp only [Real.norm_eq_abs,
      abs_of_pos (logarithmicRegularizer_pos x)]
    calc
      |logarithmicCoordinate x| *
          (logarithmicRegularizer x * ‖f x‖) =
          (|logarithmicCoordinate x| * logarithmicRegularizer x) *
            ‖f x‖ := by ring
      _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right
        (abs_logarithmicCoordinate_mul_regularizer_le_one x)
        (norm_nonneg (f x))
  apply hraw.ae_eq
  filter_upwards [logarithmicRegularizationLinearMap_coeFn f] with x hx
  exact congrArg (fun value => logarithmicCoordinate x • value) hx.symm

/-- Submodule inclusion witnessing that the regularizer range is contained in
the maximal logarithmic domain. -/
theorem range_logarithmicRegularizationLinearMap_le_domain :
    LinearMap.range logarithmicRegularizationLinearMap ≤
      logarithmicMultiplicationDomain := by
  rintro value ⟨f, rfl⟩
  exact logarithmicRegularizationLinearMap_mem_domain f

/-- The bounded regularizer is symmetric because its multiplier is real. -/
theorem logarithmicRegularizationLinearMap_isSymmetric :
    LinearMap.IsSymmetric logarithmicRegularizationLinearMap := by
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [logarithmicRegularizationLinearMap_coeFn f,
    logarithmicRegularizationLinearMap_coeFn g] with x hfx hgx
  rw [hfx, hgx]
  simp [logarithmicRegularizedFunction, real_inner_smul_left,
    real_inner_smul_right]

/-- The bounded regularizer has trivial kernel because its scalar multiplier
is strictly positive everywhere. -/
theorem logarithmicRegularizationLinearMap_injective :
    Function.Injective logarithmicRegularizationLinearMap := by
  intro f g hfg
  apply Lp.ext
  have hcoe : ⇑(logarithmicRegularizationLinearMap f) =ᵐ[positiveLebesgueMeasure]
      ⇑(logarithmicRegularizationLinearMap g) := by
    rw [hfg]
  filter_upwards [logarithmicRegularizationLinearMap_coeFn f,
    logarithmicRegularizationLinearMap_coeFn g, hcoe] with x hfx hgx hfgx
  have hregularized : logarithmicRegularizedFunction f x =
      logarithmicRegularizedFunction g x :=
    hfx.symm.trans (hfgx.trans hgx)
  have hinverse := congrArg
    (fun value => (logarithmicRegularizer x)⁻¹ • value) hregularized
  simpa [logarithmicRegularizedFunction, smul_smul,
    (logarithmicRegularizer_pos x).ne'] using hinverse

/-- The bounded regularizer has dense range in the whole Naimark space. -/
theorem logarithmicRegularizationLinearMap_denseRange :
    Dense (LinearMap.range logarithmicRegularizationLinearMap :
      Set NaimarkSpace) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  rw [← (LinearMap.range
    logarithmicRegularizationLinearMap).orthogonal_orthogonal_eq_closure]
  rw [logarithmicRegularizationLinearMap_isSymmetric.orthogonal_range,
    LinearMap.ker_eq_bot.mpr logarithmicRegularizationLinearMap_injective,
    Submodule.bot_orthogonal_eq_top]

/-- The natural maximal domain of logarithmic multiplication is dense in the
ambient Naimark `L²` space. -/
theorem logarithmicMultiplicationDomain_dense :
    Dense (logarithmicMultiplicationDomain : Set NaimarkSpace) :=
  logarithmicRegularizationLinearMap_denseRange.mono
    range_logarithmicRegularizationLinearMap_le_domain

/-- The bundled partial operator is densely defined. -/
theorem logarithmicMultiplication_denseDomain :
    Dense (logarithmicMultiplication.domain : Set NaimarkSpace) :=
  logarithmicMultiplicationDomain_dense

/-! ## Symmetry -/

/-- Multiplication by the real logarithmic coordinate is symmetric on its
natural maximal domain, expressed as formal self-adjointness of the partial
operator. -/
theorem logarithmicMultiplication_isFormalAdjoint :
    logarithmicMultiplication.IsFormalAdjoint
      logarithmicMultiplication := by
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [logarithmicMultiplication_coeFn f,
    logarithmicMultiplication_coeFn g] with x hfx hgx
  rw [hfx, hgx]
  simp [logarithmicWeightedFunction, real_inner_smul_left,
    real_inner_smul_right]

/-- The densely defined symmetric logarithmic multiplier is closable.  This
uses its closed Hilbert-space adjoint as an extension; it does not identify
the original operator with that adjoint. -/
theorem logarithmicMultiplication_isClosable :
    logarithmicMultiplication.IsClosable := by
  rw [LinearPMap.isClosable_iff_exists_closed_extension]
  refine ⟨logarithmicMultiplication.adjoint,
    LinearPMap.adjoint_isClosed logarithmicMultiplication_denseDomain, ?_⟩
  exact logarithmicMultiplication_isFormalAdjoint.le_adjoint
    logarithmicMultiplication_denseDomain

/-- The canonical graph closure of logarithmic multiplication is a closed
partial linear operator. -/
theorem logarithmicMultiplication_closure_isClosed :
    logarithmicMultiplication.closure.IsClosed :=
  logarithmicMultiplication_isClosable.closure_isClosed

end NativeCarrySpectralWeyl.Infinite
