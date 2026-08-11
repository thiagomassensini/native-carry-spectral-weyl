import NativeCarrySpectralWeyl.Limits.QuadraticFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarThirdFunctionalMoment
import Mathlib.Tactic

/-!
# Cubic functional covariance limit

This file connects the third scalar resolvent functional moment to the
periodic camera coefficients.  The new analytic feature is the unbounded
weight `log(n+1)³ w_z(n)`, which grows like `log n`.  Discrete summation by
parts bounds its zero-mean periodic sum by its endpoint size; since
`log M / A_M(z) → 0`, the normalized cubic residue still vanishes.  The
finite literal boundary is then eliminated and the complete coefficient,
direct and compatible return-metric covariances converge to the third
centered camera moment.
-/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Filter

namespace NativeCarrySpectralWeyl.Limits

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite

noncomputable section

/-- Third centered logarithmic moment weight. -/
def thirdCenteredMomentWeight (slope : ℕ) : ℝ :=
  Real.log slope ^ 3 + 3 * Real.log slope - 2

/-- Third centered logarithmic camera moment `K`. -/
def thirdCenteredMomentMatrix {ι : Type*} (period : ℕ) (camera : ι → ℕ) :
    Matrix ι ι ℝ :=
  weightedMomentMatrix period camera thirdCenteredMomentWeight

/-- Source formula
`K(i,j) = G(i,j) * (log(ell(i,j))³ + 3log(ell(i,j)) - 2)`. -/
theorem thirdCenteredMomentMatrix_apply {ι : Type*}
    (period : ℕ) (camera : ι → ℕ) (i j : ι) :
    thirdCenteredMomentMatrix period camera i j =
      periodicGramMatrix period camera i j *
        (Real.log (slopeOverlap camera i j) ^ 3 +
          3 * Real.log (slopeOverlap camera i j) - 2) := by
  rfl

/-- The third centered logarithmic camera moment is Hermitian. -/
theorem thirdCenteredMomentMatrix_isHermitian {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    (thirdCenteredMomentMatrix period camera).IsHermitian :=
  weightedMomentMatrix_isHermitian period camera thirdCenteredMomentWeight

/-- The third centered logarithmic camera moment is self-adjoint. -/
theorem thirdCenteredMomentMatrix_isSelfAdjoint {ι : Type*} [Fintype ι]
    (period : ℕ) (camera : ι → ℕ) :
    IsSelfAdjoint (thirdCenteredMomentMatrix period camera) :=
  (thirdCenteredMomentMatrix_isHermitian period camera).isSelfAdjoint

/-- Literal third centered moment for cameras `2, ..., 7`. -/
def sixCameraThirdCenteredMoment : Matrix (Fin 6) (Fin 6) ℝ :=
  !![6 * (Real.log 4 ^ 3 + 3 * Real.log 4 - 2), 0,
       10 * (Real.log 4 ^ 3 + 3 * Real.log 4 - 2), 0,
       (16 / 3) * (Real.log 4 ^ 3 + 3 * Real.log 4 - 2), 0;
     0, 6 * (Real.log 3 ^ 3 + 3 * Real.log 3 - 2), 0, 0,
       6 * (Real.log 3 ^ 3 + 3 * Real.log 3 - 2), 0;
     10 * (Real.log 4 ^ 3 + 3 * Real.log 4 - 2), 0,
       22 * (Real.log 4 ^ 3 + 3 * Real.log 4 - 2), 0,
       (16 / 3) * (Real.log 4 ^ 3 + 3 * Real.log 4 - 2), 0;
     0, 0, 0, 20 * (Real.log 5 ^ 3 + 3 * Real.log 5 - 2), 0, 0;
     (16 / 3) * (Real.log 4 ^ 3 + 3 * Real.log 4 - 2),
       6 * (Real.log 3 ^ 3 + 3 * Real.log 3 - 2),
       (16 / 3) * (Real.log 4 ^ 3 + 3 * Real.log 4 - 2), 0,
       44 * (Real.log 6 ^ 3 + 3 * Real.log 6 - 2), 0;
     0, 0, 0, 0, 0, 42 * (Real.log 7 ^ 3 + 3 * Real.log 7 - 2)]

/-- Exact recovery of the third centered moment for cameras `2, ..., 7`. -/
theorem sixCameraThirdCenteredMoment_eq :
    thirdCenteredMomentMatrix 420 sixCamera = sixCameraThirdCenteredMoment := by
  rw [thirdCenteredMomentMatrix, weightedMomentMatrix, sixCameraGram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraThirdCenteredMoment, slopeWeightMatrix,
      thirdCenteredMomentWeight, slopeOverlap, sixCamera, sixCameraGram,
      sixCameraGramRat, cameraSlope]

/-- The exact six-camera third centered moment is self-adjoint. -/
theorem sixCameraThirdCenteredMoment_isSelfAdjoint :
    IsSelfAdjoint sixCameraThirdCenteredMoment := by
  rw [← sixCameraThirdCenteredMoment_eq]
  exact thirdCenteredMomentMatrix_isSelfAdjoint 420 sixCamera

theorem norm_periodic_weightedSum_le_of_monotone
    {q weight : ℕ → ℝ} {period : ℕ}
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0)
    (hmono : Monotone weight) (hnonneg : ∀ n, 0 ≤ weight n)
    (cutoff : ℕ) :
    ‖∑ n ∈ Finset.range cutoff, weight n * q n‖ ≤
      2 * (∑ r ∈ Finset.range period, ‖q r‖) * weight cutoff := by
  let B : ℝ := ∑ r ∈ Finset.range period, ‖q r‖
  let Q : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, q i
  have hQ (n : ℕ) : ‖Q n‖ ≤ B :=
    norm_sum_range_le_period_norm_sum hperiod hq hsum n
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [show (∑ n ∈ Finset.range cutoff, weight n * q n) =
      ∑ n ∈ Finset.range cutoff, weight n • q n by
        apply Finset.sum_congr rfl
        intro n _
        rw [smul_eq_mul]]
  rw [Finset.sum_range_by_parts]
  calc
    ‖weight (cutoff - 1) • Q cutoff -
        ∑ i ∈ Finset.range (cutoff - 1),
          (weight (i + 1) - weight i) • Q (i + 1)‖ ≤
      ‖weight (cutoff - 1) • Q cutoff‖ +
        ‖∑ i ∈ Finset.range (cutoff - 1),
          (weight (i + 1) - weight i) • Q (i + 1)‖ := norm_sub_le _ _
    _ ≤ weight cutoff * B +
        ∑ i ∈ Finset.range (cutoff - 1),
          (weight (i + 1) - weight i) * B := by
      gcongr
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
        exact mul_le_mul (hmono (Nat.sub_le cutoff 1)) (hQ cutoff)
          (norm_nonneg _) (hnonneg _)
      · calc
          ‖∑ i ∈ Finset.range (cutoff - 1),
              (weight (i + 1) - weight i) • Q (i + 1)‖ ≤
            ∑ i ∈ Finset.range (cutoff - 1),
              ‖(weight (i + 1) - weight i) • Q (i + 1)‖ :=
                norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (cutoff - 1),
              (weight (i + 1) - weight i) * B := by
            gcongr with i hi
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ i)))]
            exact mul_le_mul_of_nonneg_left (hQ (i + 1))
              (sub_nonneg.mpr (hmono (Nat.le_succ i)))
    _ ≤ 2 * B * weight cutoff := by
      rw [← Finset.sum_mul]
      rw [Finset.sum_range_sub]
      have hlast : weight (cutoff - 1) ≤ weight cutoff :=
        hmono (Nat.sub_le cutoff 1)
      nlinarith [hnonneg 0, hnonneg cutoff]

theorem tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
    {q weight mass : ℕ → ℝ} {period : ℕ}
    (hperiod : 0 < period) (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0)
    (hnonneg : ∀ n, 0 ≤ weight n)
    (hmono : ∃ offset : ℕ, Monotone (fun n => weight (offset + n)))
    (hmassNe : ∀ᶠ n in atTop, mass n ≠ 0)
    (hinvMass : Tendsto (fun n => (mass n)⁻¹) atTop (nhds 0))
    (hweightDivMass : Tendsto (fun n => weight n / mass n)
      atTop (nhds 0)) :
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff, weight n * q n) / mass cutoff)
      atTop (nhds 0) := by
  obtain ⟨offset, hmono⟩ := hmono
  let shiftedWeight : ℕ → ℝ := fun n => weight (offset + n)
  let shiftedQ : ℕ → ℝ := fun n => q (offset + n)
  let shiftedMass : ℕ → ℝ := fun n => mass (offset + n)
  let shiftedNumerator : ℕ → ℝ := fun cutoff =>
    ∑ n ∈ Finset.range cutoff, shiftedWeight n * shiftedQ n
  let initialSum : ℝ := ∑ n ∈ Finset.range offset, weight n * q n
  have hshiftedQ : Function.Periodic shiftedQ period := by
    intro n
    simpa only [shiftedQ, Nat.add_assoc] using hq (offset + n)
  have hshiftedSum : ∑ r ∈ Finset.range period, shiftedQ r = 0 := by
    rw [show (∑ r ∈ Finset.range period, shiftedQ r) =
        ∑ r ∈ Finset.range period, q (offset + r) by rfl,
      sum_period_natAdd hq offset, hsum]
  have htailBig : shiftedNumerator =O[atTop] shiftedWeight := by
    apply Asymptotics.IsBigO.of_bound
      (2 * (∑ r ∈ Finset.range period, ‖shiftedQ r‖))
    filter_upwards with cutoff
    have hbound := norm_periodic_weightedSum_le_of_monotone
      hperiod hshiftedQ hshiftedSum hmono
        (fun n => hnonneg (offset + n)) cutoff
    simpa only [shiftedNumerator, shiftedWeight,
      Real.norm_eq_abs, abs_of_nonneg (hnonneg (offset + cutoff))] using hbound
  have hmassNeShifted : ∀ᶠ n in atTop, shiftedMass n ≠ 0 := by
    have h := (tendsto_add_atTop_nat offset).eventually hmassNe
    simpa only [shiftedMass, Nat.add_comm] using h
  have hweightDivMassShifted : Tendsto (fun n =>
      shiftedWeight n / shiftedMass n) atTop (nhds 0) := by
    have h := hweightDivMass.comp (tendsto_add_atTop_nat offset)
    change Tendsto (fun n => weight (n + offset) / mass (n + offset))
      atTop (nhds 0) at h
    simpa only [shiftedWeight, shiftedMass, Nat.add_comm] using h
  have hzeroCompatibility : ∀ᶠ n in atTop,
      shiftedMass n = 0 → shiftedWeight n = 0 := by
    filter_upwards [hmassNeShifted] with n hn
    exact fun hzero => (hn hzero).elim
  have hweightSmall : shiftedWeight =o[atTop] shiftedMass :=
    (Asymptotics.isLittleO_iff_tendsto' hzeroCompatibility).2
      hweightDivMassShifted
  have htailSmall : shiftedNumerator =o[atTop] shiftedMass :=
    htailBig.trans_isLittleO hweightSmall
  have htailRatio : Tendsto (fun cutoff =>
      shiftedNumerator cutoff / shiftedMass cutoff) atTop (nhds 0) :=
    htailSmall.tendsto_div_nhds_zero
  have hinvMassShifted : Tendsto (fun n => (shiftedMass n)⁻¹)
      atTop (nhds 0) := by
    have h := hinvMass.comp (tendsto_add_atTop_nat offset)
    change Tendsto (fun n => (mass (n + offset))⁻¹)
      atTop (nhds 0) at h
    simpa only [shiftedMass, Nat.add_comm] using h
  have hinitialRatio : Tendsto (fun cutoff =>
      initialSum / shiftedMass cutoff) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hinvMassShifted.const_mul initialSum
  have hshiftedRatio := hinitialRatio.add htailRatio
  have hshiftedRatio' : Tendsto (fun cutoff =>
      initialSum / shiftedMass cutoff +
        shiftedNumerator cutoff / shiftedMass cutoff) atTop (nhds 0) := by
    simpa only [zero_add] using hshiftedRatio
  have hshifted : Tendsto (fun cutoff =>
      (∑ n ∈ Finset.range (offset + cutoff), weight n * q n) /
        mass (offset + cutoff)) atTop (nhds 0) := by
    apply hshiftedRatio'.congr'
    filter_upwards with cutoff
    rw [Finset.sum_range_add]
    simp only [initialSum, shiftedNumerator, shiftedWeight, shiftedQ,
      shiftedMass]
    ring
  apply (tendsto_add_atTop_iff_nat offset).mp
  simpa only [Nat.add_comm] using hshifted

def resolventLogCubeWeight (z : ℂ) (n : ℕ) : ℝ :=
  Real.log (n + 1) ^ 3 * resolventWeight z n

theorem resolventLogCubeWeight_nonneg {z : ℂ} (hz : z.im ≠ 0)
    (n : ℕ) : 0 ≤ resolventLogCubeWeight z n := by
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by norm_num)
  exact mul_nonneg (pow_nonneg hlog 3)
    (resolventWeight_pos hz n).le

theorem exists_resolventLogCubeWeight_monotone_natAdd
    {z : ℂ} (hz : z.im ≠ 0) :
    ∃ offset : ℕ,
      Monotone (fun n : ℕ => resolventLogCubeWeight z (offset + n)) := by
  let c : ℝ := z.re ^ 2 + z.im ^ 2
  have hc : 0 ≤ c := by
    simp only [c]
    positivity
  by_cases ha : z.re ≤ 0
  · refine ⟨0, ?_⟩
    intro m n hmn
    let x : ℝ := Real.log (((m + 1 : ℕ) : ℝ))
    let y : ℝ := Real.log (((n + 1 : ℕ) : ℝ))
    have hindex : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hmn 1
    have hxy : x ≤ y := by
      exact Real.strictMonoOn_log.monotoneOn
        (by exact Set.mem_Ioi.mpr (by positivity))
        (by exact Set.mem_Ioi.mpr (by positivity)) hindex
    have hx0 : 0 ≤ x := by
      exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
    have hy0 : 0 ≤ y := hx0.trans hxy
    have hdenX : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by positivity
    have hdenY : 0 < (y - z.re) ^ 2 + z.im ^ 2 := by positivity
    have hineq :
        x ^ 3 / ((x - z.re) ^ 2 + z.im ^ 2) ≤
          y ^ 3 / ((y - z.re) ^ 2 + z.im ^ 2) := by
      rw [div_le_div_iff₀ hdenX hdenY]
      have hfactor :
          y ^ 3 * ((x - z.re) ^ 2 + z.im ^ 2) -
              x ^ 3 * ((y - z.re) ^ 2 + z.im ^ 2) =
            (y - x) *
              (x ^ 2 * y ^ 2 - 2 * z.re * x * y * (x + y) +
                c * (x ^ 2 + x * y + y ^ 2)) := by
        simp only [c]
        ring
      rw [← sub_nonneg, hfactor]
      exact mul_nonneg (sub_nonneg.mpr hxy) (by
        have hxyProduct : 0 ≤ x * y := mul_nonneg hx0 hy0
        have hmain : 0 ≤
            x ^ 2 * y ^ 2 - 2 * z.re * x * y * (x + y) := by
          nlinarith [mul_nonneg hxyProduct (add_nonneg hx0 hy0)]
        have hrest : 0 ≤ c * (x ^ 2 + x * y + y ^ 2) := by positivity
        linarith)
    simp only [resolventLogCubeWeight, zero_add]
    rw [resolventWeight_eq, resolventWeight_eq]
    simpa only [x, y, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hineq
  · have haPos : 0 < z.re := lt_of_not_ge ha
    have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_log_atTop.comp hcast
    obtain ⟨offset, hoffset⟩ :=
      eventually_atTop.1 (hlog.eventually_ge_atTop (4 * z.re))
    refine ⟨offset, ?_⟩
    intro m n hmn
    let x : ℝ := Real.log (((offset + m + 1 : ℕ) : ℝ))
    let y : ℝ := Real.log (((offset + n + 1 : ℕ) : ℝ))
    have hindexNat : offset + m + 1 ≤ offset + n + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left hmn offset) 1
    have hindex : ((offset + m + 1 : ℕ) : ℝ) ≤
        ((offset + n + 1 : ℕ) : ℝ) := by exact_mod_cast hindexNat
    have hxy : x ≤ y := by
      exact Real.strictMonoOn_log.monotoneOn
        (by exact Set.mem_Ioi.mpr (by positivity))
        (by exact Set.mem_Ioi.mpr (by positivity)) hindex
    have hxLarge : 4 * z.re ≤ x := by
      have h := hoffset (offset + m) (Nat.le_add_right offset m)
      simpa only [x, Nat.cast_add, Nat.cast_one] using h
    have hyLarge : 4 * z.re ≤ y := hxLarge.trans hxy
    have hx0 : 0 ≤ x := by nlinarith
    have hy0 : 0 ≤ y := by nlinarith
    have hproduct : 2 * z.re * (x + y) ≤ x * y := by
      have hmul : 0 ≤ (x - 4 * z.re) * (y - 4 * z.re) :=
        mul_nonneg (sub_nonneg.mpr hxLarge) (sub_nonneg.mpr hyLarge)
      nlinarith
    have hdenX : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by positivity
    have hdenY : 0 < (y - z.re) ^ 2 + z.im ^ 2 := by positivity
    have hineq :
        x ^ 3 / ((x - z.re) ^ 2 + z.im ^ 2) ≤
          y ^ 3 / ((y - z.re) ^ 2 + z.im ^ 2) := by
      rw [div_le_div_iff₀ hdenX hdenY]
      have hfactor :
          y ^ 3 * ((x - z.re) ^ 2 + z.im ^ 2) -
              x ^ 3 * ((y - z.re) ^ 2 + z.im ^ 2) =
            (y - x) *
              (x ^ 2 * y ^ 2 - 2 * z.re * x * y * (x + y) +
                c * (x ^ 2 + x * y + y ^ 2)) := by
        simp only [c]
        ring
      rw [← sub_nonneg, hfactor]
      exact mul_nonneg (sub_nonneg.mpr hxy) (by
        have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
        have hmain : 0 ≤
            x ^ 2 * y ^ 2 - 2 * z.re * x * y * (x + y) := by
          nlinarith [mul_nonneg hxy0
            (sub_nonneg.mpr hproduct)]
        have hrest : 0 ≤ c * (x ^ 2 + x * y + y ^ 2) := by positivity
        linarith)
    simp only [resolventLogCubeWeight]
    rw [resolventWeight_eq, resolventWeight_eq]
    simpa only [x, y, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using hineq

theorem tendsto_resolventLogCubeWeight_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogCubeWeight z cutoff / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hstepRatio : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) - Real.log cutoff) /
        resolventMass z cutoff) atTop (nhds 0) := by
    have h := Real.tendsto_log_nat_add_one_sub_log.mul hinvMass
    simpa only [div_eq_mul_inv, zero_mul] using h
  have hlogSuccRatio : Tendsto (fun cutoff : ℕ =>
      Real.log (cutoff + 1) / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_log_div_resolventMass_zero hz).add hstepRatio
    have h' : Tendsto (fun cutoff : ℕ =>
        Real.log cutoff / resolventMass z cutoff +
          (Real.log (cutoff + 1) - Real.log cutoff) /
            resolventMass z cutoff) atTop (nhds 0) := by
      simpa only [zero_add] using h
    apply h'.congr'
    filter_upwards with cutoff
    ring
  have hproduct := hlogSuccRatio.mul
    (tendsto_resolventLogSqWeight_one hz)
  have hlimit : Tendsto (fun cutoff : ℕ =>
      (Real.log (cutoff + 1) / resolventMass z cutoff) *
        (Real.log (cutoff + 1) ^ 2 * resolventWeight z cutoff))
      atTop (nhds 0) := by
    simpa only [resolventLogSqWeight, zero_mul] using hproduct
  apply hlimit.congr'
  filter_upwards with cutoff
  rw [resolventLogCubeWeight]
  ring

theorem tendsto_resolventLogCube_periodicWeightedSum_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) {period : ℕ}
    (hperiod : 0 < period) {q : ℕ → ℝ}
    (hq : Function.Periodic q period)
    (hsum : ∑ r ∈ Finset.range period, q r = 0) :
    Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range cutoff,
        resolventLogCubeWeight z n * q n) / resolventMass z cutoff)
      atTop (nhds 0) := by
  apply tendsto_periodic_weightedSum_div_mass_zero_of_eventually_monotone
    hperiod hq hsum
  · exact resolventLogCubeWeight_nonneg hz
  · exact exists_resolventLogCubeWeight_monotone_natAdd hz
  · exact (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0
  · exact tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  · exact tendsto_resolventLogCubeWeight_div_mass_zero hz

theorem tendsto_log_cube_div_resolventMass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 3 / resolventMass z cutoff) atTop (nhds 0) := by
  have hcastSucc : Tendsto (fun cutoff : ℕ => (cutoff : ℝ) + 1)
      atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hquinticSuccBase : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 5 / ((cutoff : ℝ) + 1))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 5 one_ne_zero).comp hcastSucc
    convert h using 1
    ext cutoff
    simp only [Function.comp_apply, one_mul, add_zero]
  have hsuccRatio : Tendsto (fun cutoff : ℕ =>
      ((cutoff : ℝ) + 1) / cutoff) atTop (nhds 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (1 : ℝ) 0 1 (d := 1) (by norm_num)
    convert h using 1
    · ext cutoff
      ring
    · norm_num
  have hquinticSucc : Tendsto (fun cutoff : ℕ =>
      Real.log ((cutoff : ℝ) + 1) ^ 5 / cutoff) atTop (nhds 0) := by
    have h := hquinticSuccBase.mul hsuccRatio
    have h' : Tendsto (fun cutoff : ℕ =>
        (Real.log ((cutoff : ℝ) + 1) ^ 5 / ((cutoff : ℝ) + 1)) *
          (((cutoff : ℝ) + 1) / cutoff)) atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
    have hcutoffNat : 0 < cutoff :=
      lt_of_lt_of_le Nat.zero_lt_one hcutoff
    have hcutoff0 : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat.ne'
    have hsucc0 : (cutoff : ℝ) + 1 ≠ 0 := by
      exact ne_of_gt (by exact_mod_cast Nat.zero_lt_succ cutoff)
    field_simp [hcutoff0, hsucc0]
  have hlogFactor : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 3 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      exact div_nonneg
        (mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hcutoff)) 3)
          (sq_nonneg _))
        (by exact_mod_cast hcutoffNat.le)
    · filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
      have hcutoffNat : 0 < cutoff :=
        lt_of_lt_of_le Nat.zero_lt_one hcutoff
      have hcutoffPos : (0 : ℝ) < cutoff := by exact_mod_cast hcutoffNat
      have hlog0 : 0 ≤ Real.log (cutoff : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hcutoff)
      have hlogLe : Real.log (cutoff : ℝ) ≤
          Real.log ((cutoff : ℝ) + 1) := by
        exact Real.strictMonoOn_log.monotoneOn
          (by exact Set.mem_Ioi.mpr hcutoffPos)
          (by exact Set.mem_Ioi.mpr (by positivity)) (by linarith)
      exact div_le_div_of_nonneg_right (by
        calc
          Real.log (cutoff : ℝ) ^ 3 *
              Real.log ((cutoff : ℝ) + 1) ^ 2 ≤
            Real.log ((cutoff : ℝ) + 1) ^ 3 *
              Real.log ((cutoff : ℝ) + 1) ^ 2 := by
                gcongr
          _ = Real.log ((cutoff : ℝ) + 1) ^ 5 := by ring) hcutoffPos.le
    · exact hquinticSucc
  have hmassRatio := tendsto_resolventMass_div_nat_div_log_sq_one hz
  have hmassRatioInv := hmassRatio.inv₀ (by norm_num)
  have hproduct := hlogFactor.mul hmassRatioInv
  have hproduct' : Tendsto (fun cutoff : ℕ =>
      (Real.log cutoff ^ 3 * Real.log ((cutoff : ℝ) + 1) ^ 2 / cutoff) *
        (resolventMass z cutoff /
          ((cutoff : ℝ) / Real.log ((cutoff : ℝ) + 1) ^ 2))⁻¹)
      atTop (nhds 0) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [Ici_mem_atTop 1,
      (tendsto_resolventMass_atTop hz).eventually_ne_atTop 0]
    with cutoff hcutoff hmass
  have hcutoffNat : 0 < cutoff :=
    lt_of_lt_of_le Nat.zero_lt_one hcutoff
  have hcutoff0 : (cutoff : ℝ) ≠ 0 := by exact_mod_cast hcutoffNat.ne'
  have hlogSucc : Real.log ((cutoff : ℝ) + 1) ≠ 0 := by
    rw [Real.log_ne_zero]
    refine ⟨ne_of_gt (by linarith), ?_, ?_⟩
    · intro h
      apply hcutoff0
      linarith
    · intro h
      have hpos : (0 : ℝ) < cutoff + 1 := by linarith
      linarith
  field_simp [hcutoff0, hlogSucc, hmass]

theorem tendsto_resolventLogMean_cube_div_mass_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      resolventLogMean z cutoff ^ 3 / resolventMass z cutoff)
      atTop (nhds 0) := by
  have hlogCube := tendsto_log_cube_div_resolventMass_zero hz
  have hdelta := tendsto_resolventLogMean_sub_log hz
  have hlogSq := tendsto_log_sq_div_resolventMass_zero hz
  have hlog := tendsto_log_div_resolventMass_zero hz
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hlimit :=
    (((hlogCube.add ((hdelta.mul hlogSq).const_mul 3)).add
      (((hdelta.pow 2).mul hlog).const_mul 3)).add
        ((hdelta.pow 3).mul hinvMass))
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff ^ 3 / resolventMass z cutoff +
        3 * ((resolventLogMean z cutoff - Real.log cutoff) *
          (Real.log cutoff ^ 2 / resolventMass z cutoff)) +
        3 * ((resolventLogMean z cutoff - Real.log cutoff) ^ 2 *
          (Real.log cutoff / resolventMass z cutoff)) +
        (resolventLogMean z cutoff - Real.log cutoff) ^ 3 *
          (resolventMass z cutoff)⁻¹) atTop (nhds 0) := by
    convert hlimit using 1
    ring
  apply hlimit'.congr'
  filter_upwards with cutoff
  ring

theorem tendsto_resolventCenteredLogCube_periodicResidue_zero
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 *
              (q n - periodMean q period))
      atTop (nhds 0) := by
  let centered : ℕ → ℝ := fun n => q n - periodMean q period
  have hcenteredPeriodic : Function.Periodic centered period := by
    intro n
    simp only [centered]
    rw [hq n]
  have hcenteredSum : ∑ r ∈ Finset.range period, centered r = 0 := by
    simpa only [centered] using sum_period_sub_periodMean (q := q) hperiod
  have hweightBound :=
    isBounded_range_periodic_weightedSum_of_eventually_antitone
      hperiod hcenteredPeriodic hcenteredSum
        (exists_resolventWeight_antitone_natAdd hz)
        (tendsto_resolventWeight_zero z)
  have hlogWeightBound :=
    isBounded_range_periodic_weightedSum_of_eventually_antitone
      hperiod hcenteredPeriodic hcenteredSum
        (exists_resolventLogWeight_antitone_natAdd hz)
        (tendsto_resolventLogWeight_zero hz)
  have hlogSqWeightBound :=
    isBounded_range_periodic_weightedSum_of_eventually_monotone_or_antitone
      hperiod hcenteredPeriodic hcenteredSum
        (exists_resolventLogSqWeight_monotone_or_antitone_natAdd hz)
        (tendsto_resolventLogSqWeight_one hz)
  have hscaleTop := tendsto_nat_const_mul_atTop hscale
  have hweightScaled : IsBoundedUnder (· ≤ ·) atTop
      (fun cutoff : ℕ =>
        ‖∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n * centered n‖) := by
    have h := hscaleTop.isBoundedUnder_comp hweightBound
    change IsBoundedUnder (· ≤ ·) atTop (fun cutoff : ℕ =>
      ‖∑ n ∈ Finset.range (scale * cutoff),
        resolventWeight z n * centered n‖) at h
    exact h
  have hlogWeightScaled : IsBoundedUnder (· ≤ ·) atTop
      (fun cutoff : ℕ =>
        ‖∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n‖) := by
    have h := hscaleTop.isBoundedUnder_comp hlogWeightBound
    change IsBoundedUnder (· ≤ ·) atTop (fun cutoff : ℕ =>
      ‖∑ n ∈ Finset.range (scale * cutoff),
        resolventLogWeight z n * centered n‖) at h
    exact h
  have hlogSqWeightScaled : IsBoundedUnder (· ≤ ·) atTop
      (fun cutoff : ℕ =>
        ‖∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSqWeight z n * centered n‖) := by
    have h := hscaleTop.isBoundedUnder_comp hlogSqWeightBound
    change IsBoundedUnder (· ≤ ·) atTop (fun cutoff : ℕ =>
      ‖∑ n ∈ Finset.range (scale * cutoff),
        resolventLogSqWeight z n * centered n‖) at h
    exact h
  have hcubeBase :=
    tendsto_resolventLogCube_periodicWeightedSum_div_mass_zero
      hz hperiod hcenteredPeriodic hcenteredSum
  have hcubeAtScale := hcubeBase.comp hscaleTop
  have hcubeAtScale' : Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff),
        resolventLogCubeWeight z n * centered n) /
          resolventMass z (scale * cutoff)) atTop (nhds 0) := by
    change Tendsto (fun cutoff : ℕ =>
      (∑ n ∈ Finset.range (scale * cutoff),
        resolventLogCubeWeight z n * centered n) /
          resolventMass z (scale * cutoff)) atTop (nhds 0) at hcubeAtScale
    exact hcubeAtScale
  have hmassRatio := tendsto_resolventMass_nat_mul_div hz hscale
  have hcubeProduct := hcubeAtScale'.mul hmassRatio
  have hcubePart : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n)
      atTop (nhds 0) := by
    have hlimit : Tendsto (fun cutoff : ℕ =>
        ((∑ n ∈ Finset.range (scale * cutoff),
            resolventLogCubeWeight z n * centered n) /
          resolventMass z (scale * cutoff)) *
        (resolventMass z (scale * cutoff) / resolventMass z cutoff))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hcubeProduct
    apply hlimit.congr'
    filter_upwards [Ici_mem_atTop 1] with cutoff hcutoff
    have hcutoffNat : 0 < cutoff :=
      lt_of_lt_of_le Nat.zero_lt_one hcutoff
    have hmass : resolventMass z cutoff ≠ 0 := by
      rw [resolventMass]
      exact ne_of_gt (Finset.sum_pos'
        (fun n _ => (resolventWeight_pos hz n).le)
        ⟨0, Finset.mem_range.mpr hcutoffNat, resolventWeight_pos hz 0⟩)
    have hscaledNat : 0 < scale * cutoff := Nat.mul_pos hscale hcutoffNat
    have hmassScaled : resolventMass z (scale * cutoff) ≠ 0 := by
      rw [resolventMass]
      exact ne_of_gt (Finset.sum_pos'
        (fun n _ => (resolventWeight_pos hz n).le)
        ⟨0, Finset.mem_range.mpr hscaledNat, resolventWeight_pos hz 0⟩)
    field_simp [hmass, hmassScaled]
  have hquadraticCoefficient : Tendsto (fun cutoff : ℕ =>
      3 * resolventLogMean z cutoff / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_div_mass_zero hz).const_mul 3
    simpa only [mul_div_assoc, mul_zero] using h
  have hquadraticPart : Tendsto (fun cutoff : ℕ =>
      (3 * resolventLogMean z cutoff / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogSqWeight z n * centered n) atTop (nhds 0) :=
    hquadraticCoefficient.zero_mul_isBoundedUnder_le hlogSqWeightScaled
  have hlinearCoefficient : Tendsto (fun cutoff : ℕ =>
      3 * resolventLogMean z cutoff ^ 2 / resolventMass z cutoff)
      atTop (nhds 0) := by
    have h := (tendsto_resolventLogMean_sq_div_mass_zero hz).const_mul 3
    simpa only [mul_div_assoc, mul_zero] using h
  have hlinearPart : Tendsto (fun cutoff : ℕ =>
      (3 * resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventLogWeight z n * centered n) atTop (nhds 0) :=
    hlinearCoefficient.zero_mul_isBoundedUnder_le hlogWeightScaled
  have hconstantPart : Tendsto (fun cutoff : ℕ =>
      (resolventLogMean z cutoff ^ 3 / resolventMass z cutoff) *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n * centered n) atTop (nhds 0) :=
    (tendsto_resolventLogMean_cube_div_mass_zero hz).zero_mul_isBoundedUnder_le
      hweightScaled
  have hlimit :=
    ((hcubePart.sub hquadraticPart).add hlinearPart).sub hconstantPart
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogCubeWeight z n * centered n -
        (3 * resolventLogMean z cutoff / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogSqWeight z n * centered n +
        (3 * resolventLogMean z cutoff ^ 2 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventLogWeight z n * centered n -
        (resolventLogMean z cutoff ^ 3 / resolventMass z cutoff) *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n * centered n) atTop (nhds 0) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 * centered n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventLogCubeWeight z n * centered n) -
          3 * resolventLogMean z cutoff *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogSqWeight z n * centered n +
          3 * resolventLogMean z cutoff ^ 2 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventLogWeight z n * centered n -
          resolventLogMean z cutoff ^ 3 *
            ∑ n ∈ Finset.range (scale * cutoff),
              resolventWeight z n * centered n := by
    calc
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 * centered n) =
        ∑ n ∈ Finset.range (scale * cutoff),
          (resolventLogCubeWeight z n * centered n -
            3 * resolventLogMean z cutoff *
              (resolventLogSqWeight z n * centered n) +
            3 * resolventLogMean z cutoff ^ 2 *
              (resolventLogWeight z n * centered n) -
            resolventLogMean z cutoff ^ 3 *
              (resolventWeight z n * centered n)) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [resolventLogCubeWeight, resolventLogSqWeight,
            resolventLogWeight]
          ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
  rw [hsum]
  ring

/-- Periodic averaging for the third centered logarithmic resolvent moment. -/
theorem tendsto_resolventCenteredLogCube_periodicWeightedSum
    {z : ℂ} (hz : z.im ≠ 0) {period scale : ℕ}
    (hperiod : 0 < period) (hscale : 0 < scale)
    {q : ℕ → ℝ} (hq : Function.Periodic q period) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 * q n)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 3 + 3 * Real.log scale - 2)) *
          periodMean q period)) := by
  have hscalar :=
    tendsto_resolventScaledCenteredLogCubeMoment_div_mass hz hscale
  have hmain : Tendsto (fun cutoff : ℕ =>
      (resolventScaledCenteredLogCubeMoment z scale cutoff /
        resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 3 + 3 * Real.log scale - 2)) *
          periodMean q period)) :=
    hscalar.mul_const (periodMean q period)
  have hresidue := tendsto_resolventCenteredLogCube_periodicResidue_zero
    hz hperiod hscale hq
  have hlimit := hresidue.add hmain
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range (scale * cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 *
                (q n - periodMean q period) +
        (resolventScaledCenteredLogCubeMoment z scale cutoff /
          resolventMass z cutoff) * periodMean q period)
      atTop (nhds (((scale : ℝ) *
        (Real.log scale ^ 3 + 3 * Real.log scale - 2)) *
          periodMean q period)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  have hsum :
      (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 * q n) =
        (∑ n ∈ Finset.range (scale * cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 *
              (q n - periodMean q period)) +
          periodMean q period *
            resolventScaledCenteredLogCubeMoment z scale cutoff := by
    rw [resolventScaledCenteredLogCubeMoment, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hsum]
  ring

/-- The shifted periodic camera core with the centered cubic multiplier
converges entrywise to the third centered moment. -/
theorem tendsto_resolvent_shiftedCoreCubicFunctional_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        ∑ n ∈ Finset.range
            (pairCoreLength (camera i) (camera j) cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 *
              realProfileProduct (camera i) (camera j) (n + 1))
      atTop (nhds (thirdCenteredMomentMatrix period camera i j)) := by
  let scale := min (cameraSlope (camera i)) (cameraSlope (camera j))
  let q : ℕ → ℝ := fun n =>
    realProfileProduct (camera i) (camera j) (n + 1)
  have hslope (k : index) : 0 < cameraSlope (camera k) := by
    rw [cameraSlope]
    split_ifs
    · norm_num
    · exact lt_of_lt_of_le (by norm_num) (hcamera k)
  have hscale : 0 < scale := lt_min (hslope i) (hslope j)
  have hproduct : Function.Periodic
      (realProfileProduct (camera i) (camera j)) period :=
    realProfileProduct_periodic (hcamera i) (hcamera j)
      (hcommon i) (hcommon j)
  have hq : Function.Periodic q period := by
    intro n
    simpa only [q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hproduct (n + 1)
  have hmean : periodMean q period =
      periodicProductMean period (camera i) (camera j) := by
    have h := periodMean_natAdd hproduct 1
    rw [periodMean_realProfileProduct] at h
    simpa only [q, Nat.add_comm] using h
  have hlimit := tendsto_resolventCenteredLogCube_periodicWeightedSum
    hz hperiod hscale hq
  rw [hmean] at hlimit
  have htarget :
      (((scale : ℝ) *
          (Real.log scale ^ 3 + 3 * Real.log scale - 2)) *
          periodicProductMean period (camera i) (camera j)) =
        thirdCenteredMomentMatrix period camera i j := by
    rw [thirdCenteredMomentMatrix_apply, periodicGramMatrix_apply]
    simp only [slopeOverlap, scale]
    ring
  rw [htarget] at hlimit
  simpa only [pairCoreLength, scale, q] using hlimit

/-- Cubic multiplier in the finite centered logarithmic coordinate. -/
def centeredCubicMultiplier (z : ℂ) (cutoff n : ℕ) : ℝ :=
  (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3

/-- Product of the resolvent weight with the centered cubic multiplier. -/
def resolventCenteredCubicWeight (z : ℂ) (cutoff n : ℕ) : ℝ :=
  resolventWeight z n * centeredCubicMultiplier z cutoff n

@[simp] theorem centeredPolynomialMultiplier_X_cube
    (z : ℂ) (cutoff n : ℕ) :
    centeredPolynomialMultiplier (Polynomial.X ^ 3) z cutoff n =
      centeredCubicMultiplier z cutoff n := by
  simp [centeredPolynomialMultiplier, centeredCubicMultiplier]

/-- Every fixed literal seed/endpoint term vanishes for the centered
cubic functional weight. -/
theorem tendsto_resolventCenteredCubic_finiteBoundaryTerm_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) (r : ℕ) :
    Tendsto (fun cutoff =>
      finiteBoundaryTerm (resolventCenteredCubicWeight z cutoff)
        cutoff camera₁ camera₂ r) atTop (nhds 0) := by
  let scale := min (cameraSlope camera₁) (cameraSlope camera₂)
  have hslope₁ : 0 < cameraSlope camera₁ := by
    rw [cameraSlope]
    split_ifs
    · norm_num
    · omega
  have hslope₂ : 0 < cameraSlope camera₂ := by
    rw [cameraSlope]
    split_ifs
    · norm_num
    · omega
  have hscale : 0 < scale := lt_min hslope₁ hslope₂
  have hindex : Tendsto (fun cutoff : ℕ => scale * cutoff + r) atTop atTop :=
    (tendsto_add_atTop_nat r).comp (tendsto_nat_const_mul_atTop hscale)
  have hweight : Tendsto (fun cutoff : ℕ =>
      resolventWeight z (scale * cutoff + r)) atTop (nhds 0) :=
    (tendsto_resolventWeight_zero z).comp hindex
  have hlogDilated := tendsto_log_nat_mul_add_sub_log hscale r
  have hlogStep := Real.tendsto_log_nat_add_one_sub_log
  have hmean : Tendsto (fun cutoff : ℕ =>
      Real.log cutoff - resolventLogMean z cutoff) atTop (nhds 1) := by
    have h := (tendsto_resolventLogMean_sub_log hz).neg
    simpa only [neg_sub, neg_neg] using h
  have hcoordinateLinear : Tendsto (fun cutoff : ℕ =>
      Real.log (scale * cutoff + r + 1) - resolventLogMean z cutoff)
      atTop (nhds (Real.log scale + 1)) := by
    have hlimit := (hlogDilated.add hlogStep).add hmean
    have hlimit' : Tendsto (fun cutoff : ℕ =>
        (Real.log (scale * cutoff + r + 1) - Real.log (cutoff + 1)) +
          (Real.log (cutoff + 1) - Real.log cutoff) +
            (Real.log cutoff - resolventLogMean z cutoff))
        atTop (nhds (Real.log scale + 1)) := by
      convert hlimit using 1
      ring
    apply hlimit'.congr'
    filter_upwards with cutoff
    norm_num [Nat.cast_add, Nat.cast_mul]
  have hcoordinate : Tendsto (fun cutoff : ℕ =>
      centeredCubicMultiplier z cutoff (scale * cutoff + r))
      atTop (nhds ((Real.log scale + 1) ^ 3)) := by
    have h := hcoordinateLinear.pow 3
    apply h.congr'
    filter_upwards with cutoff
    rw [centeredCubicMultiplier]
    norm_num [Nat.cast_add, Nat.cast_mul]
  have heffective : Tendsto (fun cutoff : ℕ =>
      resolventCenteredCubicWeight z cutoff (scale * cutoff + r))
      atTop (nhds 0) := by
    simpa only [resolventCenteredCubicWeight, zero_mul] using
      hweight.mul hcoordinate
  have habsEffective : Tendsto (fun cutoff : ℕ =>
      |resolventCenteredCubicWeight z cutoff (scale * cutoff + r)|)
      atTop (nhds 0) := by
    simpa only [abs_zero] using heffective.abs
  let coefficientBound : ℝ := (camera₁ + 4 : ℕ) * (camera₂ + 4 : ℕ)
  have hmajorant : Tendsto (fun cutoff : ℕ =>
      coefficientBound *
        |resolventCenteredCubicWeight z cutoff (scale * cutoff + r)|)
      atTop (nhds 0) := by
    simpa only [mul_zero] using habsEffective.const_mul coefficientBound
  have hdom : ∀ cutoff : ℕ,
      |finiteBoundaryTerm (resolventCenteredCubicWeight z cutoff)
          cutoff camera₁ camera₂ r| ≤
        coefficientBound *
          |resolventCenteredCubicWeight z cutoff (scale * cutoff + r)| := by
    intro cutoff
    rw [finiteBoundaryTerm]
    split_ifs
    · have hbound₁ := abs_finiteCoefficientAt_le
        (cutoff := cutoff) (n := scale * cutoff + r) hcamera₁
      have hbound₂ := abs_finiteCoefficientAt_le
        (cutoff := cutoff) (n := scale * cutoff + r) hcamera₂
      have hproduct :
          |finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)| ≤
            coefficientBound := by
        exact mul_le_mul hbound₁ hbound₂ (abs_nonneg _) (by positivity)
      simp only [pairCoreLength, scale]
      rw [abs_mul, abs_mul]
      calc
        |resolventCenteredCubicWeight z cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
            |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)| =
          (|finiteCoefficientAt camera₁ cutoff (scale * cutoff + r)| *
              |finiteCoefficientAt camera₂ cutoff (scale * cutoff + r)|) *
            |resolventCenteredCubicWeight z cutoff
              (scale * cutoff + r)| := by ring
        _ ≤ coefficientBound *
            |resolventCenteredCubicWeight z cutoff
              (scale * cutoff + r)| :=
          mul_le_mul_of_nonneg_right hproduct (abs_nonneg _)
    · simp only [abs_zero]
      exact mul_nonneg (by positivity) (abs_nonneg _)
  have habs : Tendsto (fun cutoff : ℕ =>
      |finiteBoundaryTerm (resolventCenteredCubicWeight z cutoff)
        cutoff camera₁ camera₂ r|) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hdom) hmajorant
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa only [Real.norm_eq_abs] using habs

/-- The complete fixed-width literal boundary vanishes for the centered
cubic functional weight. -/
theorem tendsto_resolventCenteredCubic_finiteBoundarySum_zero
    {z : ℂ} (hz : z.im ≠ 0)
    {camera₁ camera₂ : ℕ} (hcamera₁ : 2 ≤ camera₁)
    (hcamera₂ : 2 ≤ camera₂) :
    Tendsto (fun cutoff =>
      finiteBoundarySum (resolventCenteredCubicWeight z cutoff)
        cutoff camera₁ camera₂) atTop (nhds 0) := by
  have hsum := tendsto_finsetSum
    (Finset.range (pairBoundaryWidth camera₁ camera₂))
    (fun r _ => tendsto_resolventCenteredCubic_finiteBoundaryTerm_zero
      hz hcamera₁ hcamera₂ r)
  simpa only [finiteBoundarySum, Finset.sum_const_zero] using hsum

/-- Entrywise convergence of the complete literal centered-cubic
coefficient covariance to the third centered camera moment. -/
theorem tendsto_finiteCenteredCubicCoefficientCovariance_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff camera i j)
      atTop (nhds (thirdCenteredMomentMatrix period camera i j)) := by
  have hcore := tendsto_resolvent_shiftedCoreCubicFunctional_apply
    hz hperiod hcamera hcommon i j
  have hboundary := tendsto_resolventCenteredCubic_finiteBoundarySum_zero
    hz (hcamera i) (hcamera j)
  have hinvMass : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_resolventMass_atTop hz)
  have hboundaryNormalized : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
        finiteBoundarySum (resolventCenteredCubicWeight z cutoff)
          cutoff (camera i) (camera j)) atTop (nhds 0) := by
    simpa only [zero_mul] using hinvMass.mul hboundary
  have hlimit := hcore.add hboundaryNormalized
  have hlimit' : Tendsto (fun cutoff : ℕ =>
      (resolventMass z cutoff)⁻¹ *
          ∑ n ∈ Finset.range
              (pairCoreLength (camera i) (camera j) cutoff),
            resolventWeight z n *
              (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 *
                realProfileProduct (camera i) (camera j) (n + 1) +
        (resolventMass z cutoff)⁻¹ *
          finiteBoundarySum (resolventCenteredCubicWeight z cutoff)
            cutoff (camera i) (camera j))
      atTop (nhds (thirdCenteredMomentMatrix period camera i j)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with cutoff
  rw [finiteCenteredPolynomialCoefficientCovariance,
    finiteFunctionalCoefficientCovariance]
  simp only [centeredPolynomialMultiplier_X_cube]
  have hnum :
      (∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventWeight z n * centeredCubicMultiplier z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n) =
        ∑ n ∈ Finset.range (pairFiniteWindow (camera i) (camera j) cutoff),
          resolventCenteredCubicWeight z cutoff n *
            finiteCoefficientAt (camera i) cutoff n *
              finiteCoefficientAt (camera j) cutoff n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredCubicWeight]
  rw [hnum]
  rw [finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary
    (weight := resolventCenteredCubicWeight z cutoff)
      (hcamera i) (hcamera j)]
  have hcoreEq :
      (∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventCenteredCubicWeight z cutoff n *
            realProfileProduct (camera i) (camera j) (n + 1)) =
        ∑ n ∈ Finset.range (pairCoreLength (camera i) (camera j) cutoff),
          resolventWeight z n *
            (Real.log (n + 1) - resolventLogMean z cutoff) ^ 3 *
              realProfileProduct (camera i) (camera j) (n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [resolventCenteredCubicWeight, centeredCubicMultiplier]
  rw [hcoreEq]
  simp only [resolventMass]
  ring

/-- Matrix convergence of the complete literal centered-cubic
coefficient covariance. -/
theorem tendsto_finiteCenteredCubicCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff camera)
      atTop (nhds (thirdCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff camera i j)
    atTop (nhds fun i j => thirdCenteredMomentMatrix period camera i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_finiteCenteredCubicCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j

/-- Finite entry-sup norm convergence of the literal centered-cubic
coefficient covariance. -/
theorem tendsto_norm_finiteCenteredCubicCoefficientCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff camera -
        thirdCenteredMomentMatrix period camera‖) atTop (nhds 0) := by
  have hmatrix := tendsto_finiteCenteredCubicCoefficientCovariance
    hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => thirdCenteredMomentMatrix period camera)
        atTop (nhds (thirdCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- The literal six-camera centered-cubic covariance converges to the
exact documented matrix `sixCameraThirdCenteredMoment`. -/
theorem
    tendsto_norm_sixCamera_finiteCenteredCubicCoefficientCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff : ℕ =>
      ‖finiteCenteredPolynomialCoefficientCovariance
          (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff sixCamera -
        sixCameraThirdCenteredMoment‖) atTop (nhds 0) := by
  rw [← sixCameraThirdCenteredMoment_eq]
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  exact tendsto_norm_finiteCenteredCubicCoefficientCovariance_sub
    hz (by norm_num : 0 < 420) hcamera sixCamera_commonPeriod

/-- Complexification of the third centered periodic camera moment. -/
def complexThirdCenteredMomentMatrix {index : Type*} (period : ℕ)
    (camera : index → ℕ) : Matrix index index ℂ :=
  fun i j => (thirdCenteredMomentMatrix period camera i j : ℂ)

/-- Complexified convergence of the complete literal centered-cubic
coefficient covariance. -/
theorem tendsto_complex_finiteCenteredCubicCoefficientCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff i j =>
      (finiteCenteredPolynomialCoefficientCovariance
        (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff camera i j : ℂ))
      atTop (nhds (complexThirdCenteredMomentMatrix period camera)) := by
  change Tendsto (fun cutoff i j =>
    (finiteCenteredPolynomialCoefficientCovariance
      (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff camera i j : ℂ))
    atTop (nhds fun i j =>
      (thirdCenteredMomentMatrix period camera i j : ℂ))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have hreal := tendsto_finiteCenteredCubicCoefficientCovariance_apply
    hz hperiod hcamera hcommon i j
  exact (Complex.continuous_ofReal.tendsto
    (thirdCenteredMomentMatrix period camera i j)).comp hreal

/-- The normalized direct finite functional covariance for the centered
cubic multiplier converges to the complexified third centered moment. -/
theorem tendsto_normalizedFiniteCenteredCubicDirectCovariance
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalDirectCovariance z cutoff camera
        (centeredPolynomialMultiplier
          (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff))
      atTop (nhds (complexThirdCenteredMomentMatrix period camera)) := by
  apply tendsto_normalizedFiniteFunctionalDirectCovariance_of_coefficients
    hcamera
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredCubicCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of the normalized direct
centered-cubic functional covariance. -/
theorem tendsto_norm_normalizedFiniteCenteredCubicDirectCovariance_sub
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff camera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff) -
        complexThirdCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredCubicDirectCovariance
      hz hperiod hcamera hcommon
  have hconstant :
      Tendsto (fun _ : ℕ => complexThirdCenteredMomentMatrix period camera)
        atTop (nhds (complexThirdCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Every compatible finite return-metric colligation family inherits the
centered-cubic third-moment limit. -/
theorem tendsto_normalizedFiniteCenteredCubicReturnMetricCrossCovariance
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (endpointMap : ∀ cutoff,
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (bulkMap : ∀ cutoff,
      Matrix bulk (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : ℕ → Matrix bulk endpoint ℂ)
    (hpoisson : ∀ cutoff, poisson cutoff * endpointMap cutoff = bulkMap cutoff)
    (hisometry : ∀ cutoff,
      (endpointMap cutoff)ᴴ * endpointMap cutoff +
        (bulkMap cutoff)ᴴ * bulkMap cutoff = 1) :
    Tendsto (fun cutoff =>
      normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff camera
        (centeredPolynomialMultiplier
          (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff)
        (endpointMap cutoff) (poisson cutoff))
      atTop (nhds (complexThirdCenteredMomentMatrix period camera)) := by
  apply
    tendsto_normalizedFiniteFunctionalReturnMetricCrossCovariance_of_coefficients
      hcamera endpointMap bulkMap poisson hpoisson hisometry
  simpa only [finiteCenteredPolynomialCoefficientCovariance] using
    tendsto_complex_finiteCenteredCubicCoefficientCovariance
      hz hperiod hcamera hcommon

/-- Finite entry-sup norm convergence of every compatible centered-cubic
return-metric cross covariance family. -/
theorem
    tendsto_norm_normalizedFiniteCenteredCubicReturnMetricCrossCovariance_sub
    {index endpoint bulk : Type*}
    [Fintype index] [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint]
    {period : ℕ} {camera : index → ℕ} {z : ℂ}
    (hz : z.im ≠ 0) (hperiod : 0 < period)
    (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera)
    (endpointMap : ∀ cutoff,
      Matrix endpoint (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (bulkMap : ∀ cutoff,
      Matrix bulk (Fin (finiteFamilyWindow cutoff camera)) ℂ)
    (poisson : ℕ → Matrix bulk endpoint ℂ)
    (hpoisson : ∀ cutoff, poisson cutoff * endpointMap cutoff = bulkMap cutoff)
    (hisometry : ∀ cutoff,
      (endpointMap cutoff)ᴴ * endpointMap cutoff +
        (bulkMap cutoff)ᴴ * bulkMap cutoff = 1) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff camera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexThirdCenteredMomentMatrix period camera‖)
      atTop (nhds 0) := by
  have hmatrix :=
    tendsto_normalizedFiniteCenteredCubicReturnMetricCrossCovariance
      hz hperiod hcamera hcommon endpointMap bulkMap poisson hpoisson hisometry
  have hconstant :
      Tendsto (fun _ : ℕ => complexThirdCenteredMomentMatrix period camera)
        atTop (nhds (complexThirdCenteredMomentMatrix period camera)) :=
    tendsto_const_nhds
  simpa using (hmatrix.sub hconstant).norm

/-- Complex form of the exact documented six-camera third centered moment. -/
def complexSixCameraThirdCenteredMoment : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (sixCameraThirdCenteredMoment i j : ℂ)

@[simp] theorem complexThirdCenteredMomentMatrix_sixCamera :
    complexThirdCenteredMomentMatrix 420 sixCamera =
      complexSixCameraThirdCenteredMoment := by
  unfold complexThirdCenteredMomentMatrix
    complexSixCameraThirdCenteredMoment
  rw [sixCameraThirdCenteredMoment_eq]

/-- The literal six-camera direct centered-cubic covariance converges in
matrix norm to the exact documented third centered-moment matrix. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredCubicDirectCovariance_sub
    {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalDirectCovariance z cutoff sixCamera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff) -
        complexSixCameraThirdCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexThirdCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredCubicDirectCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod)

/-- Exact passage to the six-camera third centered-moment limit for every
finite colligation family satisfying the Poisson and Pythagorean identities. -/
theorem
    tendsto_norm_sixCamera_normalizedFiniteCenteredCubicReturnMetricCrossCovariance_sub
    {endpoint bulk : Type*} [Fintype endpoint] [Fintype bulk]
    [DecidableEq endpoint] {z : ℂ} (hz : z.im ≠ 0)
    (endpointMap : ∀ cutoff,
      Matrix endpoint (Fin (finiteFamilyWindow cutoff sixCamera)) ℂ)
    (bulkMap : ∀ cutoff,
      Matrix bulk (Fin (finiteFamilyWindow cutoff sixCamera)) ℂ)
    (poisson : ℕ → Matrix bulk endpoint ℂ)
    (hpoisson : ∀ cutoff, poisson cutoff * endpointMap cutoff = bulkMap cutoff)
    (hisometry : ∀ cutoff,
      (endpointMap cutoff)ᴴ * endpointMap cutoff +
        (bulkMap cutoff)ᴴ * bulkMap cutoff = 1) :
    Tendsto (fun cutoff =>
      ‖normalizedFiniteFunctionalReturnMetricCrossCovariance z cutoff sixCamera
          (centeredPolynomialMultiplier
            (Polynomial.X ^ 3 : Polynomial ℝ) z cutoff)
          (endpointMap cutoff) (poisson cutoff) -
        complexSixCameraThirdCenteredMoment‖) atTop (nhds 0) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [complexThirdCenteredMomentMatrix_sixCamera] using
    (tendsto_norm_normalizedFiniteCenteredCubicReturnMetricCrossCovariance_sub
      (period := 420) (camera := sixCamera) hz (by norm_num) hcamera
        sixCamera_commonPeriod endpointMap bulkMap poisson hpoisson hisometry)


end

end NativeCarrySpectralWeyl.Limits
