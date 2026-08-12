import NativeCarrySpectralWeyl.Camera.BracketSeries
import NativeCarrySpectralWeyl.Camera.Factors
import GreenFrame.Concrete.Analysis.GreenStateEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Critical native amplitude in the logarithmic rigged scale

The native critical amplitude has coordinates `n⁻¹ᐟ²`.  Its squared norm is
the harmonic series, so it is not a vector of the unweighted sequence space
`ℓ²(PNat, ℂ)`.  The logarithmically rigged coordinate

`n⁻¹ᐟ² / (1 + log n)`

does belong to `ℓ²`.  This file realizes that weighted coordinate space,
constructs the diagonal logarithmic evolution

`U(t)x(n) = exp(-i t log n) x(n)`,

and proves that it is a strongly continuous group of complex-linear
isometric equivalences.  Pointwise removal of the logarithmic weight from
the distinguished orbit recovers the exact native-line Dirichlet sample.

The underlying Lean type of `LogRiggedState` is the standard sequence
Hilbert space, but its coordinates represent the weighted `H₋₁` realization.
The pointwise map `unriggedCoordinate` is deliberately not bundled as a
bounded operator.  Consequently this module does not place the raw critical
amplitude in the concrete Green state space and does not manufacture the
bounded all-bases camera readout required by `AngularGreenCameraCoupling`.
-/

open scoped ENNReal lp
open Set MeasureTheory

noncomputable section

namespace NativeCarrySpectralWeyl.Boundary

/-- Sequence realization of the logarithmically weighted rigged space
`H₋₁`.  The alias records the intended coordinate interpretation. -/
abbrev LogRiggedState := GreenFrame.Concrete.State

private def logSquareMajorant (x : ℝ) : ℝ :=
  x⁻¹ / (Real.log x) ^ 2

private theorem logSquareMajorant_antitone :
    AntitoneOn logSquareMajorant (Ici 2) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hxone : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hyone : 1 < y := hxone.trans_le hxy
  have hlogin : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hxpos hypos hxy
  have hlogsq : (Real.log x) ^ 2 ≤ (Real.log y) ^ 2 := by
    exact sq_le_sq₀ (Real.log_nonneg hxone.le) (Real.log_nonneg hyone.le) |>.2 hlogin
  rw [logSquareMajorant, logSquareMajorant, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul
    (inv_anti₀ hxpos hxy)
    ((inv_le_inv₀ (sq_pos_of_pos (Real.log_pos hyone))
      (sq_pos_of_pos (Real.log_pos hxone))).2 hlogsq)
    (inv_nonneg.mpr (sq_nonneg _)) (inv_nonneg.mpr hxpos.le)

private theorem logSquareMajorant_summable :
    Summable (fun n : ℕ => logSquareMajorant n) := by
  exact logSquareMajorant_antitone.summable_of_integrableOn_Ioi
    (integrableOn_inv_div_log_sq_Ioi (by norm_num : (1 : ℝ) < 2))
    (by
      intro t ht
      have htpos : 0 < t := (by norm_num : (0 : ℝ) < 2).trans ht
      exact div_nonneg (inv_nonneg.mpr htpos.le) (sq_nonneg _))

private def criticalEnergyNat (k : ℕ) : ℝ :=
  let n : ℝ := k + 1
  n⁻¹ / (1 + Real.log n) ^ 2

private theorem criticalEnergyNat_nonneg (k : ℕ) :
    0 ≤ criticalEnergyNat k := by
  dsimp [criticalEnergyNat]
  positivity

private theorem criticalEnergyNat_summable : Summable criticalEnergyNat := by
  rw [← summable_nat_add_iff 2]
  apply Summable.of_nonneg_of_le
      (fun k => criticalEnergyNat_nonneg (k + 2))
      (fun k => ?_)
      ((summable_nat_add_iff 3).mpr logSquareMajorant_summable)
  show criticalEnergyNat (k + 2) ≤
    logSquareMajorant (((k + 3 : ℕ) : ℝ))
  simp only [criticalEnergyNat, logSquareMajorant, Nat.cast_add,
    Nat.cast_ofNat]
  have hshift : (k : ℝ) + 2 + 1 = (k : ℝ) + 3 := by ring
  rw [hshift]
  let x : ℝ := (k : ℝ) + 3
  have hx : 1 < x := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp [x]
    linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hdenom : (Real.log x) ^ 2 ≤ (1 + Real.log x) ^ 2 := by
    nlinarith [Real.log_nonneg hx.le]
  change x⁻¹ / (1 + Real.log x) ^ 2 ≤ x⁻¹ / (Real.log x) ^ 2
  exact div_le_div_of_nonneg_left (inv_nonneg.mpr (by positivity))
    (sq_pos_of_pos hlog) hdenom

/-- Weighted critical coordinate `n⁻¹ᐟ² / (1 + log n)`. -/
def criticalRiggedCoordinate (n : PNat) : ℂ :=
  (((n : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) /
    (1 + Real.log ((n : ℕ) : ℝ)) : ℝ)

/-- Coordinate energy of the weighted critical vector. -/
def criticalRiggedEnergy (n : PNat) : ℝ :=
  (((n : ℕ) : ℝ))⁻¹ /
    (1 + Real.log ((n : ℕ) : ℝ)) ^ 2

/-- The logarithmically weighted critical energy is summable. -/
theorem criticalRiggedEnergy_summable : Summable criticalRiggedEnergy := by
  have h := Equiv.pnatEquivNat.summable_iff.mpr criticalEnergyNat_summable
  apply h.congr
  intro n
  have hnval : (n.natPred : ℝ) + 1 = (((n : ℕ) : ℝ)) := by
    exact_mod_cast n.natPred_add_one
  change criticalEnergyNat n.natPred = criticalRiggedEnergy n
  simp only [criticalEnergyNat, criticalRiggedEnergy]
  rw [hnval]

/-- Raw native critical amplitude `n⁻¹ᐟ²`. -/
def nativeCriticalAmplitude (n : PNat) : ℂ :=
  ((((n : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

/-- Coordinate energy of the raw critical amplitude. -/
def nativeCriticalEnergy (n : PNat) : ℝ :=
  (((n : ℕ) : ℝ))⁻¹

/-- The raw amplitude has exactly harmonic coordinate energy. -/
theorem nativeCriticalAmplitude_normSq (n : PNat) :
    Complex.normSq (nativeCriticalAmplitude n) = nativeCriticalEnergy n := by
  rw [nativeCriticalAmplitude, nativeCriticalEnergy, Complex.normSq_ofReal]
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.2
  rw [← Real.rpow_add hn]
  have hexp : -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = -1 := by ring
  rw [hexp, Real.rpow_neg_one]

/-- The raw critical-energy sequence is the divergent harmonic series. -/
theorem nativeCriticalEnergy_not_summable :
    ¬ Summable nativeCriticalEnergy := by
  have hnat : ¬ Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ))⁻¹) := by
    intro h
    apply Real.not_summable_natCast_inv
    exact (summable_nat_add_iff 1).mp h
  intro h
  apply hnat
  have hinjective : Function.Injective (fun k : ℕ => k.succPNat) := by
    intro a b hab
    exact Nat.succ.inj (congr_arg Subtype.val hab)
  have hp := h.comp_injective hinjective
  apply hp.congr
  intro k
  have hval : (((k.succPNat : PNat) : ℕ) : ℝ) =
      ((k + 1 : ℕ) : ℝ) := by
    norm_num
  simp only [Function.comp_apply, nativeCriticalEnergy]
  rw [hval]

/-- The raw native critical amplitude is not an unweighted `ℓ²` vector. -/
theorem nativeCriticalAmplitude_not_memLp :
    ¬ Memℓp nativeCriticalAmplitude 2 := by
  intro hmem
  apply nativeCriticalEnergy_not_summable
  have hsummable := (memℓp_gen_iff
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mp hmem
  apply hsummable.congr
  intro n
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    ((Complex.sq_norm (nativeCriticalAmplitude n)).trans
      (nativeCriticalAmplitude_normSq n))

/-- Squared norm of the weighted critical coordinate. -/
theorem criticalRiggedCoordinate_normSq (n : PNat) :
    Complex.normSq (criticalRiggedCoordinate n) = criticalRiggedEnergy n := by
  rw [criticalRiggedCoordinate, criticalRiggedEnergy, Complex.normSq_ofReal]
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.2
  have hw : 0 < 1 + Real.log ((n : ℕ) : ℝ) := by
    have : 1 ≤ ((n : ℕ) : ℝ) := by exact_mod_cast n.2
    linarith [Real.log_nonneg this]
  rw [div_mul_div_comm, ← Real.rpow_add hn]
  congr 1
  · have hexp : -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = -1 := by ring
    rw [hexp, Real.rpow_neg_one]
  · ring

/-- Distinguished critical vector in the weighted coordinate realization. -/
def criticalRiggedState : LogRiggedState :=
  ⟨criticalRiggedCoordinate, by
    apply memℓp_gen
    have h := criticalRiggedEnergy_summable
    apply h.congr
    intro n
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      ((Complex.sq_norm (criticalRiggedCoordinate n)).trans
        (criticalRiggedCoordinate_normSq n)).symm⟩

/-- Coordinates of the distinguished rigged state. -/
@[simp] theorem criticalRiggedState_apply (n : PNat) :
    criticalRiggedState n = criticalRiggedCoordinate n := rfl

/-- Native logarithmic phase `exp(-i t log n)`. -/
def nativeLogPhase (t : ℝ) (n : PNat) : ℂ :=
  Complex.exp (-((t * Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Every native logarithmic phase has unit norm. -/
@[simp] theorem nativeLogPhase_norm (t : ℝ) (n : PNat) :
    ‖nativeLogPhase t n‖ = 1 := by
  rw [nativeLogPhase, Complex.norm_exp]
  have hreal :
      (-((t * Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, Complex.neg_im,
      Complex.ofReal_im, neg_zero, mul_one, sub_zero]
  rw [hreal, Real.exp_zero]

/-- Every native logarithmic phase has squared norm one. -/
@[simp] theorem nativeLogPhase_normSq (t : ℝ) (n : PNat) :
    Complex.normSq (nativeLogPhase t n) = 1 := by
  rw [← Complex.sq_norm, nativeLogPhase_norm]
  norm_num

/-- The native logarithmic phase at time zero. -/
@[simp] theorem nativeLogPhase_zero (n : PNat) :
    nativeLogPhase 0 n = 1 := by
  simp [nativeLogPhase]

/-- Multiplicative group law of the native logarithmic phase. -/
theorem nativeLogPhase_add (s t : ℝ) (n : PNat) :
    nativeLogPhase (s + t) n = nativeLogPhase s n * nativeLogPhase t n := by
  rw [nativeLogPhase, nativeLogPhase, nativeLogPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The native phase is continuous in the angular parameter. -/
theorem continuous_nativeLogPhase (n : PNat) :
    Continuous (fun t : ℝ => nativeLogPhase t n) := by
  unfold nativeLogPhase
  fun_prop

private def riggedAngularEvolutionFunction (t : ℝ)
    (x : LogRiggedState) (n : PNat) : ℂ :=
  nativeLogPhase t n * x n

private def riggedAngularEvolutionValue (t : ℝ)
    (x : LogRiggedState) : LogRiggedState :=
  ⟨riggedAngularEvolutionFunction t x, by
    apply memℓp_gen
    apply (GreenFrame.Concrete.stateEnergy_summable x).congr
    intro n
    simp only [GreenFrame.Concrete.stateEnergy, ENNReal.toReal_ofNat,
      Real.rpow_two, riggedAngularEvolutionFunction]
    rw [Complex.sq_norm, Complex.normSq_mul, nativeLogPhase_normSq, one_mul]⟩

@[simp] private theorem riggedAngularEvolutionValue_apply (t : ℝ)
    (x : LogRiggedState) (n : PNat) :
    riggedAngularEvolutionValue t x n = nativeLogPhase t n * x n := rfl

private theorem riggedAngularEvolutionValue_add (t : ℝ)
    (x y : LogRiggedState) :
    riggedAngularEvolutionValue t (x + y) =
      riggedAngularEvolutionValue t x + riggedAngularEvolutionValue t y := by
  apply lp.ext
  funext n
  simp [mul_add]

private theorem riggedAngularEvolutionValue_smul (t : ℝ) (c : ℂ)
    (x : LogRiggedState) :
    riggedAngularEvolutionValue t (c • x) =
      c • riggedAngularEvolutionValue t x := by
  apply lp.ext
  funext n
  simp [mul_left_comm]

private theorem riggedAngularEvolutionValue_norm (t : ℝ)
    (x : LogRiggedState) :
    ‖riggedAngularEvolutionValue t x‖ = ‖x‖ := by
  have hsq : ‖riggedAngularEvolutionValue t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← GreenFrame.Concrete.stateEnergy_tsum_eq_norm_sq,
      ← GreenFrame.Concrete.stateEnergy_tsum_eq_norm_sq]
    apply tsum_congr
    intro n
    simp [GreenFrame.Concrete.stateEnergy, Complex.normSq_mul]
  nlinarith [norm_nonneg (riggedAngularEvolutionValue t x), norm_nonneg x]

private theorem riggedAngularEvolutionValue_neg_left (t : ℝ)
    (x : LogRiggedState) :
    riggedAngularEvolutionValue (-t) (riggedAngularEvolutionValue t x) = x := by
  apply lp.ext
  funext n
  simp only [riggedAngularEvolutionValue_apply]
  rw [← mul_assoc, ← nativeLogPhase_add]
  simp

private theorem riggedAngularEvolutionValue_neg_right (t : ℝ)
    (x : LogRiggedState) :
    riggedAngularEvolutionValue t (riggedAngularEvolutionValue (-t) x) = x := by
  simpa only [neg_neg] using riggedAngularEvolutionValue_neg_left (-t) x

private def riggedAngularEvolutionLinearEquiv (t : ℝ) :
    LogRiggedState ≃ₗ[ℂ] LogRiggedState where
  toFun := riggedAngularEvolutionValue t
  invFun := riggedAngularEvolutionValue (-t)
  left_inv := riggedAngularEvolutionValue_neg_left t
  right_inv := riggedAngularEvolutionValue_neg_right t
  map_add' := riggedAngularEvolutionValue_add t
  map_smul' := riggedAngularEvolutionValue_smul t

/-- Diagonal logarithmic evolution as a complex-linear isometric
equivalence of the weighted coordinate space. -/
def riggedAngularEvolution (t : ℝ) :
    LogRiggedState ≃ₗᵢ[ℂ] LogRiggedState :=
  LinearIsometryEquiv.mk (riggedAngularEvolutionLinearEquiv t)
    (riggedAngularEvolutionValue_norm t)

/-- Coordinate action of the logarithmic evolution. -/
@[simp] theorem riggedAngularEvolution_apply (t : ℝ)
    (x : LogRiggedState) (n : PNat) :
    riggedAngularEvolution t x n = nativeLogPhase t n * x n := rfl

/-- The logarithmic evolution at time zero is the identity. -/
@[simp] theorem riggedAngularEvolution_zero (x : LogRiggedState) :
    riggedAngularEvolution 0 x = x := by
  apply lp.ext
  funext n
  simp

/-- Additive group law of the logarithmic evolution. -/
theorem riggedAngularEvolution_add (s t : ℝ) (x : LogRiggedState) :
    riggedAngularEvolution (s + t) x =
      riggedAngularEvolution s (riggedAngularEvolution t x) := by
  apply lp.ext
  funext n
  simp only [riggedAngularEvolution_apply]
  rw [nativeLogPhase_add]
  ring

/-- Evolution by `-t` is the inverse of evolution by `t`. -/
@[simp] theorem riggedAngularEvolution_neg_apply (t : ℝ)
    (x : LogRiggedState) :
    riggedAngularEvolution (-t) (riggedAngularEvolution t x) = x := by
  rw [← riggedAngularEvolution_add]
  simp

/-- The logarithmic evolution preserves the rigged Hilbert norm. -/
theorem riggedAngularEvolution_norm (t : ℝ) (x : LogRiggedState) :
    ‖riggedAngularEvolution t x‖ = ‖x‖ :=
  (riggedAngularEvolution t).norm_map x

private def riggedAngularDifferenceEnergy (x : LogRiggedState)
    (t₀ : ℝ) (n : PNat) (t : ℝ) : ℝ :=
  Complex.normSq ((nativeLogPhase t n - nativeLogPhase t₀ n) * x n)

private theorem continuous_riggedAngularDifferenceEnergy
    (x : LogRiggedState) (t₀ : ℝ) (n : PNat) :
    Continuous (riggedAngularDifferenceEnergy x t₀ n) := by
  unfold riggedAngularDifferenceEnergy
  exact Complex.continuous_normSq.comp
    (((continuous_nativeLogPhase n).sub continuous_const).mul continuous_const)

private theorem riggedAngularDifferenceEnergy_le
    (x : LogRiggedState) (t₀ t : ℝ) (n : PNat) :
    riggedAngularDifferenceEnergy x t₀ n t ≤
      4 * GreenFrame.Concrete.stateEnergy x n := by
  rw [riggedAngularDifferenceEnergy, GreenFrame.Concrete.stateEnergy,
    Complex.normSq_mul]
  have hphase : ‖nativeLogPhase t n - nativeLogPhase t₀ n‖ ≤ 2 := by
    calc
      ‖nativeLogPhase t n - nativeLogPhase t₀ n‖ ≤
          ‖nativeLogPhase t n‖ + ‖nativeLogPhase t₀ n‖ := norm_sub_le _ _
      _ = 2 := by simp only [nativeLogPhase_norm]; norm_num
  have hphaseSq :
      Complex.normSq (nativeLogPhase t n - nativeLogPhase t₀ n) ≤ 4 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg (nativeLogPhase t n - nativeLogPhase t₀ n)]
  exact mul_le_mul_of_nonneg_right hphaseSq (Complex.normSq_nonneg _)

private theorem continuous_riggedAngularDifferenceEnergy_tsum
    (x : LogRiggedState) (t₀ : ℝ) :
    Continuous (fun t : ℝ =>
      ∑' n : PNat, riggedAngularDifferenceEnergy x t₀ n t) := by
  apply continuous_tsum
  · exact fun n => continuous_riggedAngularDifferenceEnergy x t₀ n
  · exact (GreenFrame.Concrete.stateEnergy_summable x).mul_left 4
  · intro n t
    rw [Real.norm_eq_abs, riggedAngularDifferenceEnergy,
      abs_of_nonneg (Complex.normSq_nonneg _)]
    exact riggedAngularDifferenceEnergy_le x t₀ t n

private theorem riggedAngularEvolution_norm_sub_sq (x : LogRiggedState)
    (t t₀ : ℝ) :
    ‖riggedAngularEvolution t x - riggedAngularEvolution t₀ x‖ ^ 2 =
      ∑' n : PNat, riggedAngularDifferenceEnergy x t₀ n t := by
  rw [← GreenFrame.Concrete.stateEnergy_tsum_eq_norm_sq]
  apply tsum_congr
  intro n
  rw [GreenFrame.Concrete.stateEnergy, riggedAngularDifferenceEnergy]
  congr 1
  change nativeLogPhase t n * x n - nativeLogPhase t₀ n * x n = _
  ring

/-- Every orbit of the logarithmic isometry group is norm-continuous. -/
theorem continuous_riggedAngularEvolution_orbit (x : LogRiggedState) :
    Continuous (fun t : ℝ => riggedAngularEvolution t x) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hcont : ContinuousAt (fun t : ℝ =>
      ∑' n : PNat, riggedAngularDifferenceEnergy x t₀ n t) t₀ :=
    (continuous_riggedAngularDifferenceEnergy_tsum x t₀).continuousAt
  have hzero :
      (∑' n : PNat, riggedAngularDifferenceEnergy x t₀ n t₀) = 0 := by
    simp [riggedAngularDifferenceEnergy]
  have hepsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hcontrol⟩ := hcont (ε ^ 2) hepsq
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hsum :
      ∑' n : PNat, riggedAngularDifferenceEnergy x t₀ n t < ε ^ 2 := by
    have habs :
        |∑' n : PNat, riggedAngularDifferenceEnergy x t₀ n t| < ε ^ 2 := by
      simpa only [hzero, dist_zero_right, Real.norm_eq_abs] using hcontrol ht
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hnormsq :
      ‖riggedAngularEvolution t x - riggedAngularEvolution t₀ x‖ ^ 2 <
        ε ^ 2 := by
    rw [riggedAngularEvolution_norm_sub_sq]
    exact hsum
  rw [dist_eq_norm]
  nlinarith [norm_nonneg
    (riggedAngularEvolution t x - riggedAngularEvolution t₀ x)]

/-- Distinguished orbit of the critical weighted vector. -/
def criticalRiggedOrbit (t : ℝ) : LogRiggedState :=
  riggedAngularEvolution t criticalRiggedState

/-- The distinguished critical rigged orbit is norm-continuous. -/
theorem continuous_criticalRiggedOrbit : Continuous criticalRiggedOrbit :=
  continuous_riggedAngularEvolution_orbit criticalRiggedState

/-- Coordinates of the distinguished critical orbit. -/
@[simp] theorem criticalRiggedOrbit_apply (t : ℝ) (n : PNat) :
    criticalRiggedOrbit t n =
      nativeLogPhase t n * criticalRiggedCoordinate n := rfl

/-- The distinguished critical orbit has constant rigged norm. -/
theorem criticalRiggedOrbit_norm (t : ℝ) :
    ‖criticalRiggedOrbit t‖ = ‖criticalRiggedState‖ :=
  riggedAngularEvolution_norm t criticalRiggedState

/-- Pointwise removal of the logarithmic rigging weight.  No bounded-operator
claim is attached to this coordinate map. -/
def unriggedCoordinate (x : LogRiggedState) (n : PNat) : ℂ :=
  (1 + Real.log ((n : ℕ) : ℝ) : ℝ) * x n

/-- Removing the weight from the critical orbit recovers the raw amplitude
times its logarithmic phase. -/
theorem unriggedCoordinate_criticalRiggedOrbit (t : ℝ) (n : PNat) :
    unriggedCoordinate (criticalRiggedOrbit t) n =
      nativeLogPhase t n *
        (((n : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) := by
  have hn : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast n.2
  have hw : (1 + Real.log ((n : ℕ) : ℝ) : ℝ) ≠ 0 := by
    positivity
  let weight : ℝ := 1 + Real.log ((n : ℕ) : ℝ)
  let amplitude : ℝ := ((n : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)
  rw [unriggedCoordinate, criticalRiggedOrbit_apply, criticalRiggedCoordinate]
  change (weight : ℂ) *
      (nativeLogPhase t n * ((amplitude / weight : ℝ) : ℂ)) =
    nativeLogPhase t n * (amplitude : ℂ)
  have hdiv : ((amplitude / weight : ℝ) : ℂ) =
      (amplitude : ℂ) / (weight : ℂ) := by norm_cast
  rw [hdiv]
  have hwC : (weight : ℂ) ≠ 0 := by exact_mod_cast hw
  field_simp [hwC]

/-- Phase times raw critical amplitude is exactly the existing native-line
Dirichlet sample. -/
theorem nativeLogPhase_mul_amplitude_eq_dirichletValue
    (t : ℝ) (n : PNat) :
    nativeLogPhase t n *
        ((((n : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) =
      Camera.dirichletValue (Camera.nativeLine t) (n : ℕ) := by
  have hn : (0 : ℕ) < (n : ℕ) := n.2
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Camera.dirichletValue, Camera.nativeLine]
  rw [show -((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      ((-(1 : ℝ) / 2 : ℝ) : ℂ) + (-(t : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [Complex.cpow_add _ _ hnC]
  have hamp :
      ((n : ℕ) : ℂ) ^ (((-(1 : ℝ) / 2 : ℝ) : ℂ)) =
        ((((n : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_cpow (x := ((n : ℕ) : ℝ))
        (by positivity) (-(1 : ℝ) / 2)).symm
  have hphase :
      ((n : ℕ) : ℂ) ^ (-(t : ℂ) * Complex.I) = nativeLogPhase t n := by
    rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
    unfold nativeLogPhase
    congr 1
    push_cast
    ring
  rw [hamp, hphase]
  ring

/-- Exact bridge from the weighted critical orbit to the native-line
Dirichlet value after pointwise removal of the rigging weight. -/
theorem unriggedCoordinate_eq_dirichletValue (t : ℝ) (n : PNat) :
    unriggedCoordinate (criticalRiggedOrbit t) n =
      Camera.dirichletValue (Camera.nativeLine t) (n : ℕ) := by
  rw [unriggedCoordinate_criticalRiggedOrbit,
    nativeLogPhase_mul_amplitude_eq_dirichletValue]

end NativeCarrySpectralWeyl.Boundary
