import NativeCarrySpectralWeyl.Camera.Geometry
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Native camera bracket series

This module defines the finite and infinite scalar bracket characteristics from
the actual aligned camera geometry.  Its main result is absolute summability of
the center-block series throughout `-1 < re s`, proved from a quantitative
centered-second-difference estimate.

This is the convergence layer only.  Equality with the periodic-profile
Dirichlet series, holomorphy of the sum, analytic continuation of the cross
identity, and common-zero claims remain separate obligations.
-/

open scoped BigOperators
open Set

namespace NativeCarrySpectralWeyl.Camera

open FiniteNativeCarryOperator.Camera

noncomputable section

/-- Positive-real Dirichlet kernel used to obtain the bracket estimate. -/
def dirichletKernel (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-s)

/-- First real derivative of the positive-real Dirichlet kernel. -/
def dirichletKernelDeriv (s : ℂ) (x : ℝ) : ℂ :=
  (-s) * (x : ℂ) ^ (-s - 1)

/-- Second real derivative of the positive-real Dirichlet kernel. -/
def dirichletKernelSecondDeriv (s : ℂ) (x : ℝ) : ℂ :=
  s * (s + 1) * (x : ℂ) ^ (-s - 2)

/-- Exact first derivative of the positive-real Dirichlet kernel. -/
theorem dirichletKernel_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dirichletKernel s) (dirichletKernelDeriv s x) x := by
  change HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
    ((-s) * (x : ℂ) ^ (-s - 1)) x
  by_cases hs : s = 0
  · subst s
    simpa using hasDerivAt_const x (1 : ℂ)
  · simpa using
      hasDerivAt_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)

/-- Exact derivative of the first Dirichlet-kernel derivative. -/
theorem dirichletKernelDeriv_hasDerivAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dirichletKernelDeriv s) (dirichletKernelSecondDeriv s x) x := by
  change HasDerivAt (fun y : ℝ => (-s) * (y : ℂ) ^ (-s - 1))
    (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x
  by_cases hs : s = 0
  · subst s
    simpa using hasDerivAt_const x (0 : ℂ)
  · by_cases hs1 : s = -1
    · subst s
      simpa using hasDerivAt_const x (1 : ℂ)
    · have hexp : -s - 1 ≠ 0 := by
        intro h
        apply hs1
        linear_combination -h
      have hpow := hasDerivAt_ofReal_cpow_const hx.ne' hexp
      have h := (hasDerivAt_const x (-s)).mul hpow
      simp only [zero_mul, zero_add] at h
      rw [show -s - 1 - 1 = -s - 2 by ring, ← mul_assoc,
        show -s * (-s - 1) = s * (s + 1) by ring] at h
      exact h

/-- Exact norm of the second Dirichlet-kernel derivative on the positive axis. -/
theorem dirichletKernelSecondDeriv_norm (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖dirichletKernelSecondDeriv s x‖ =
      ‖s * (s + 1)‖ * x ^ (-s.re - 2) := by
  rw [dirichletKernelSecondDeriv, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1

/-- A twice differentiable function with bounded second derivative has a
quadratically bounded centered second difference. -/
theorem norm_centeredSecondDifference_le
    {f f' f'' : ℝ → ℂ} {center radius C : ℝ}
    (hradius : 0 ≤ radius)
    (hf : ∀ x ∈ Icc (center - radius) (center + radius),
      HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (center - radius) (center + radius),
      HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Icc (center - radius) (center + radius), ‖f'' x‖ ≤ C) :
    ‖f (center - radius) - 2 * f center + f (center + radius)‖ ≤
      C * radius ^ 2 := by
  let g : ℝ → ℂ := fun x => f (x + radius) - f x
  have hg : ∀ x ∈ Icc (center - radius) center,
      HasDerivWithinAt g (f' (x + radius) - f' x)
        (Icc (center - radius) center) x := by
    intro x hx
    have hxBig : x ∈ Icc (center - radius) (center + radius) :=
      ⟨hx.1, hx.2.trans (le_add_of_nonneg_right hradius)⟩
    have hxrBig : x + radius ∈ Icc (center - radius) (center + radius) := by
      constructor <;> linarith [hx.1, hx.2]
    have hcomp : HasDerivAt (fun y => f (y + radius)) (f' (x + radius)) x := by
      exact HasDerivAt.comp_add_const x radius (hf (x + radius) hxrBig)
    exact (hcomp.sub (hf x hxBig)).hasDerivWithinAt
  have hgBound : ∀ x ∈ Ico (center - radius) center,
      ‖f' (x + radius) - f' x‖ ≤ C * radius := by
    intro x hx
    have hsegment : Icc x (x + radius) ⊆
        Icc (center - radius) (center + radius) := by
      intro y hy
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hderiv : ∀ y ∈ Icc x (x + radius),
        HasDerivWithinAt f' (f'' y) (Icc x (x + radius)) y := by
      intro y hy
      exact (hf' y (hsegment hy)).hasDerivWithinAt
    have hC : ∀ y ∈ Ico x (x + radius), ‖f'' y‖ ≤ C := by
      intro y hy
      exact hbound y (hsegment (Ico_subset_Icc_self hy))
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hC
      (x + radius) (right_mem_Icc.mpr (le_add_of_nonneg_right hradius))
    convert hmv using 1
    ring
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' hg hgBound center
    (right_mem_Icc.mpr (sub_le_self center hradius))
  rw [show f (center - radius) - 2 * f center + f (center + radius) =
    (f (center + radius) - f center) - (f center - f (center - radius)) by ring]
  unfold g at hmain
  convert hmain using 1
  · rw [show center - radius + radius = center by ring]
  · ring

/-- Quantitative centered-difference bound for `x ↦ x⁻ˢ` on the positive axis. -/
theorem dirichletKernel_centered_bound (s : ℂ) {center radius : ℝ}
    (hradius : 0 ≤ radius) (hleft : 0 < center - radius)
    (hs : -1 < s.re) :
    ‖dirichletKernel s (center - radius) - 2 * dirichletKernel s center +
        dirichletKernel s (center + radius)‖ ≤
      (‖s * (s + 1)‖ * (center - radius) ^ (-s.re - 2)) * radius ^ 2 := by
  apply norm_centeredSecondDifference_le hradius
  · intro x hx
    exact dirichletKernel_hasDerivAt s (hleft.trans_le hx.1)
  · intro x hx
    exact dirichletKernelDeriv_hasDerivAt s (hleft.trans_le hx.1)
  · intro x hx
    rw [dirichletKernelSecondDeriv_norm s (hleft.trans_le hx.1)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_nonpos hleft hx.1 (by linarith)

/-- Scalar Dirichlet sample at a natural native position. -/
def dirichletValue (s : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (-s)

/-- Scalar centered bracket at a natural center and radius. -/
def centeredBracketTerm (s : ℂ) (center radius : ℕ) : ℂ :=
  dirichletValue s (center - radius) - 2 * dirichletValue s center +
    dirichletValue s (center + radius)

/-- The norm of one natural centered bracket has the required p-series decay. -/
theorem centeredBracketTerm_norm_le (s : ℂ) {center radius : ℕ}
    (hradius : radius < center) (hs : -1 < s.re) :
    ‖centeredBracketTerm s center radius‖ ≤
      (‖s * (s + 1)‖ * ((center - radius : ℕ) : ℝ) ^ (-s.re - 2)) *
        (radius : ℝ) ^ 2 := by
  have hleft : 0 < ((center : ℝ) - radius) := by
    apply sub_pos.mpr
    exact_mod_cast hradius
  have h := dirichletKernel_centered_bound s (center := (center : ℝ))
    (radius := (radius : ℝ)) (by positivity) hleft hs
  simpa [centeredBracketTerm, dirichletValue, dirichletKernel,
    Nat.cast_sub hradius.le] using h

/-- Any growing center sequence whose left leg dominates `n+1` produces an
absolutely summable centered-bracket series on `-1 < re s`. -/
theorem centeredBracketSequence_summable
    (s : ℂ) (centers : ℕ → ℕ) (radius : ℕ)
    (hs : -1 < s.re) (hradius : ∀ n, radius < centers n)
    (hlower : ∀ n, n + 1 ≤ centers n - radius) :
    Summable (fun n => centeredBracketTerm s (centers n) radius) := by
  let p : ℝ := -s.re - 2
  let C : ℝ := ‖s * (s + 1)‖ * (radius : ℝ) ^ 2
  have hp : p < -1 := by simp [p]; linarith
  have hbase : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ p) := by
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  apply (hbase.mul_left C).of_norm_bounded
  intro n
  have hterm := centeredBracketTerm_norm_le s (hradius n) hs
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos n)
  have hpow : ((centers n - radius : ℕ) : ℝ) ^ p ≤
      ((n + 1 : ℕ) : ℝ) ^ p := by
    apply Real.rpow_le_rpow_of_nonpos (x := ((n + 1 : ℕ) : ℝ))
      (y := ((centers n - radius : ℕ) : ℝ)) hpos
    · exact_mod_cast hlower n
    · exact hp.le.trans (by norm_num)
  calc
    ‖centeredBracketTerm s (centers n) radius‖ ≤
        (‖s * (s + 1)‖ * ((centers n - radius : ℕ) : ℝ) ^ p) *
          (radius : ℝ) ^ 2 := by simpa [p] using hterm
    _ ≤ C * ((n + 1 : ℕ) : ℝ) ^ p := by
      dsimp [C]
      calc
        (‖s * (s + 1)‖ * ((centers n - radius : ℕ) : ℝ) ^ p) *
            (radius : ℝ) ^ 2 ≤
            (‖s * (s + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ p) *
              (radius : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) (sq_nonneg _)
        _ = (‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((n + 1 : ℕ) : ℝ) ^ p := by ring

/-- Every aligned C2 left leg dominates its one-based center index. -/
theorem c2_index_succ_le_alignedCenter_sub (index : ℕ) :
    index + 1 ≤ alignedCenter 2 index - 1 := by
  rw [alignedCenter_eq_cameraSlope_mul]
  simp [cameraSlope]
  omega

/-- Every natural-camera left leg dominates its one-based center index. -/
theorem natural_index_succ_le_alignedCenter_sub {camera radius index : ℕ}
    (hcamera : 3 ≤ camera) (hradius : radius ∈ radiusSet camera) :
    index + 1 ≤ alignedCenter camera index - radius := by
  have h2 : camera ≠ 2 := by omega
  have hrange := (mem_radiusSet_iff.mp hradius).2
  have hmul : index ≤ camera * index :=
    Nat.le_mul_of_pos_left index (by omega)
  rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_of_ne_two h2,
    Nat.mul_succ]
  omega

/-- Sum of every radius bracket at one aligned camera center. -/
def centerBracketTerm (camera : ℕ) (s : ℂ) (index : ℕ) : ℂ :=
  if camera = 2 then
    centeredBracketTerm s (alignedCenter 2 index) 1
  else
    ∑ radius ∈ radiusSet camera,
      centeredBracketTerm s (alignedCenter camera index) radius

/-- Center blocks of every supported camera are summable throughout `-1 < re s`. -/
theorem centerBracketTerm_summable {camera : ℕ} (hcamera : 2 ≤ camera)
    {s : ℂ} (hs : -1 < s.re) :
    Summable (centerBracketTerm camera s) := by
  by_cases h2 : camera = 2
  · subst camera
    change Summable (fun index => if 2 = 2 then _ else _)
    exact centeredBracketSequence_summable s (fun n => alignedCenter 2 n) 1 hs
      (fun n => by
        rw [alignedCenter_eq_cameraSlope_mul]
        simp only [cameraSlope_two]
        omega)
      c2_index_succ_le_alignedCenter_sub
  · have hcamera3 : 3 ≤ camera := by omega
    change Summable (fun index => if camera = 2 then _ else _)
    simp only [h2, if_false]
    exact summable_sum fun radius hradius =>
      centeredBracketSequence_summable s (fun n => alignedCenter camera n)
        radius hs
        (fun n => by
          have hlower := natural_index_succ_le_alignedCenter_sub hcamera3 hradius
            (index := n)
          omega)
        (fun n => natural_index_succ_le_alignedCenter_sub hcamera3 hradius)

/-- Literal absolute summability in norm of every supported center-block series. -/
theorem centerBracketTerm_norm_summable {camera : ℕ} (hcamera : 2 ≤ camera)
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun index => ‖centerBracketTerm camera s index‖) :=
  summable_norm_iff.mpr (centerBracketTerm_summable hcamera hs)

/-- Finite seed contribution of the exceptional C2 or a natural camera. -/
def seedDirichletTerm (camera : ℕ) (s : ℂ) : ℂ :=
  if camera = 2 then dirichletValue s 1
  else ∑ radius ∈ radiusSet camera, dirichletValue s radius

/-- Scalar characteristic with exactly `cutoff` aligned center blocks. -/
def finiteBracketCharacteristic (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  seedDirichletTerm camera s + ∑ index ∈ Finset.range cutoff,
    centerBracketTerm camera s index

/-- Infinite scalar bracket characteristic on its summability domain. -/
def bracketCharacteristic (camera : ℕ) (s : ℂ) : ℂ :=
  seedDirichletTerm camera s + ∑' index, centerBracketTerm camera s index

@[simp] theorem finiteBracketCharacteristic_zero (camera : ℕ) (s : ℂ) :
    finiteBracketCharacteristic camera 0 s = seedDirichletTerm camera s := by
  simp [finiteBracketCharacteristic]

/-- Adding one cutoff appends precisely the next aligned center block. -/
theorem finiteBracketCharacteristic_succ (camera cutoff : ℕ) (s : ℂ) :
    finiteBracketCharacteristic camera (cutoff + 1) s =
      finiteBracketCharacteristic camera cutoff s + centerBracketTerm camera s cutoff := by
  simp [finiteBracketCharacteristic, Finset.sum_range_succ, add_assoc]

/-- Finite bracket characteristics converge to the infinite characteristic on
the complete source half-plane `-1 < re s`. -/
theorem finiteBracketCharacteristic_tendsto {camera : ℕ} (hcamera : 2 ≤ camera)
    {s : ℂ} (hs : -1 < s.re) :
    Filter.Tendsto (fun cutoff => finiteBracketCharacteristic camera cutoff s)
      Filter.atTop (nhds (bracketCharacteristic camera s)) := by
  exact tendsto_const_nhds.add (centerBracketTerm_summable hcamera hs).hasSum.tendsto_sum_nat

end

end NativeCarrySpectralWeyl.Camera
