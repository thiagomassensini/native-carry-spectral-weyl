import NativeCarrySpectralWeyl.Infinite.Naimark
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Exact divisibility realization of the existing all-bases native Gram.
The three coefficient slots retain every cross term, including aligned C2
and the antipodal even-camera channel. No infinite arithmetic measure is used. -/

open scoped BigOperators Matrix
noncomputable section
namespace NativeCarrySpectralWeyl.Finite.Relational
open NativeCarrySpectralWeyl.Camera NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Limits

/-- Arithmetic overlap kernel on positive resolutions. -/
def divisibilityKernel (d e : ℕ) : ℝ := (Nat.lcm d e : ℝ)⁻¹

theorem divisibilityKernel_comm (d e : ℕ) :
    divisibilityKernel d e = divisibilityKernel e d := by
  simp [divisibilityKernel, Nat.lcm_comm]

private theorem indicator_period_sum {d : ℕ} (hd : 0 < d) :
    ∑ n ∈ Finset.range d, (dvdIndicator d n : ℝ) = 1 := by
  rw [Finset.sum_eq_single 0]
  · simp [dvdIndicator]
  · intro n hn hne
    have hnot : ¬ d ∣ n := by
      intro h
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h
      have := Finset.mem_range.mp hn
      omega
    simp [dvdIndicator, hnot]
  · simp [hd.ne']

/-- Exact multiple count, including residue zero, on a complete period. -/
theorem indicator_sum_commonPeriod {d L : ℕ} (hd : 0 < d) (hdiv : d ∣ L) :
    ∑ n ∈ Finset.range L, (dvdIndicator d n : ℝ) = (L : ℝ) / d := by
  obtain ⟨k, rfl⟩ := hdiv
  have hp : Function.Periodic (fun n => (dvdIndicator d n : ℝ)) d := by
    intro n
    change (dvdIndicator d (n + d) : ℝ) = dvdIndicator d n
    rw [dvdIndicator_add_of_dvd (dvd_refl d)]
  rw [Nat.mul_comm d k, sum_range_mul_period hp, indicator_period_sum hd]
  simp [nsmul_eq_mul, hd.ne']

/-- Divisibility intersection is exactly divisibility by the least common multiple. -/
theorem indicator_mul (d e n : ℕ) :
    (dvdIndicator d n : ℝ) * dvdIndicator e n = dvdIndicator (Nat.lcm d e) n := by
  simp only [dvdIndicator, Int.cast_ite, Int.cast_one, Int.cast_zero]
  simp only [Nat.lcm_dvd_iff]
  split_ifs <;> simp_all

/-- Periodic inner product determined solely by divisibility relations. -/
theorem divisibility_inner {d e L : ℕ} (hd : 0 < d) (he : 0 < e)
    (hL : 0 < L) (hdL : d ∣ L) (heL : e ∣ L) :
    (L : ℝ)⁻¹ * ∑ n ∈ Finset.range L,
      (dvdIndicator d n : ℝ) * dvdIndicator e n = divisibilityKernel d e := by
  simp_rw [indicator_mul]
  rw [indicator_sum_commonPeriod (Nat.lcm_pos hd he) (Nat.lcm_dvd hdL heL)]
  simp [divisibilityKernel, div_eq_mul_inv, hL.ne']

/-- Every admissible common period gives the same arithmetic inner product. -/
theorem divisibility_period_independent {d e L M : ℕ} (hd : 0 < d) (he : 0 < e)
    (hL : 0 < L) (hM : 0 < M) (hdL : d ∣ L) (heL : e ∣ L)
    (hdM : d ∣ M) (heM : e ∣ M) :
    (L : ℝ)⁻¹ * ∑ n ∈ Finset.range L,
      (dvdIndicator d n : ℝ) * dvdIndicator e n =
    (M : ℝ)⁻¹ * ∑ n ∈ Finset.range M,
      (dvdIndicator d n : ℝ) * dvdIndicator e n := by
  rw [divisibility_inner hd he hL hdL heL, divisibility_inner hd he hM hdM heM]

/-- Finite arithmetic kernel restrictions are positive semidefinite. -/
theorem divisibilityKernel_posSemidef {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) :
    Matrix.PosSemidef (fun i j => divisibilityKernel (d i) (d j) : Matrix ι ι ℝ) := by
  classical
  let L := ∏ i, d i
  have hL : 0 < L := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ L := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq : (fun i j => divisibilityKernel (d i) (d j) : Matrix ι ι ℝ) =
      (L : ℝ)⁻¹ • ∑ n ∈ Finset.range L,
        Matrix.vecMulVec (fun i => (dvdIndicator (d i) n : ℝ))
          (star (fun i => (dvdIndicator (d i) n : ℝ))) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      star_trivial, smul_eq_mul]
    exact (divisibility_inner (hd i) (hd j) hL (hdiv i) (hdiv j)).symm
  rw [heq]
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_sum _ fun n _ => Matrix.posSemidef_vecMulVec_self_star _
  · positivity

/-- Three finite slots; the odd-camera third slot has zero coefficient. -/
def resolution (b : ℕ) : Fin 3 → ℕ :=
  if b = 2 then ![1, 2, 4] else if Odd b then ![1, b, 1] else ![1, b / 2, b]

/-- Literal coefficients of the native profile, with no fitted normalization. -/
def coefficient (b : ℕ) : Fin 3 → ℝ :=
  if b = 2 then ![1, -1, -2] else if Odd b then ![1, -(b : ℝ), 0]
  else ![1, 1, -((b + 2 : ℕ) : ℝ)]

/-- Finitely supported resolution coefficients; repeated resolutions are merged exactly. -/
def profileCoefficients (b : ℕ) : ℕ →₀ ℝ :=
  ∑ i : Fin 3, Finsupp.single (resolution b i) (coefficient b i)

/-- The finite relation synthesis is the original profile for every camera. -/
theorem profile_relational (b n : ℕ) :
    (profile b n : ℝ) = ∑ i : Fin 3, coefficient b i * dvdIndicator (resolution b i) n := by
  by_cases h2 : b = 2
  · subst b
    simp [resolution, coefficient, profile, c2Profile, dvdIndicator, Fin.sum_univ_succ]; split_ifs <;> ring
  · by_cases ho : Odd b
    · simp [resolution, coefficient, profile, h2, ho, oddProfile, dvdIndicator,
        Fin.sum_univ_succ]; split_ifs <;> ring

    · simp [resolution, coefficient, profile, h2, ho, evenProfile, dvdIndicator,
        Fin.sum_univ_succ]; split_ifs <;> ring

/-- Native profiles are literal `Finsupp` combinations of divisibility relations. -/
theorem profile_finsupp (b n : ℕ) :
    (profile b n : ℝ) = (profileCoefficients b).sum
      (fun d a => a * (dvdIndicator d n : ℝ)) := by
  change (profile b n : ℝ) = Finsupp.linearCombination ℝ
    (fun d => (dvdIndicator d n : ℝ)) (profileCoefficients b)
  simp only [profileCoefficients, map_sum, Finsupp.linearCombination_single, smul_eq_mul]
  exact profile_relational b n

theorem resolution_pos {b : ℕ} (hb : 2 ≤ b) (i : Fin 3) : 0 < resolution b i := by
  by_cases h2 : b = 2
  · subst b; fin_cases i <;> norm_num [resolution]
  · by_cases ho : Odd b
    · fin_cases i <;> simp [resolution, h2, ho]
      all_goals omega
    · fin_cases i <;> simp [resolution, h2, ho]
      all_goals omega

theorem resolution_dvd_slope {b : ℕ} (hb : 2 ≤ b) (i : Fin 3) :
    resolution b i ∣ cameraSlope b := by
  by_cases h2 : b = 2
  · subst b; fin_cases i <;> norm_num [resolution]
  · by_cases ho : Odd b
    · fin_cases i <;> simp [resolution, cameraSlope, h2, ho]
    · have he := Nat.not_odd_iff_even.mp ho
      obtain ⟨k, hk⟩ := he
      have hh : b / 2 = k := by omega
      fin_cases i <;> simp [resolution, cameraSlope, h2, ho, hh]
      exact hk ▸ dvd_add (dvd_refl k) (dvd_refl k)

/-- Full double synthesis, retaining all nine ordered cross channels. -/
def relationalMean (b c : ℕ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    coefficient b i * coefficient c j * divisibilityKernel (resolution b i) (resolution c j)

/-- The full bilinear arithmetic form on finitely supported resolution data. -/
def relationalForm (A B : ℕ →₀ ℝ) : ℝ :=
  Finsupp.linearCombination ℝ
    (fun d => Finsupp.linearCombination ℝ (fun e => divisibilityKernel d e) B) A

theorem relationalForm_profileCoefficients (b c : ℕ) :
    relationalForm (profileCoefficients b) (profileCoefficients c) = relationalMean b c := by
  simp only [relationalForm, profileCoefficients, map_sum,
    Finsupp.linearCombination_single, smul_eq_mul, Finset.mul_sum, relationalMean]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Relational factorization on any positive common native-profile period. -/
theorem periodicProductMean_relational {b c L : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hL : 0 < L) (hbL : cameraSlope b ∣ L) (hcL : cameraSlope c ∣ L) :
    periodicProductMean L b c = relationalMean b c := by
  simp only [periodicProductMean, periodicProductSum, Int.cast_sum, Int.cast_mul]
  have hprod (n : ℕ) : (profile b n : ℝ) * profile c n =
      ∑ i : Fin 3, ∑ j : Fin 3, coefficient b i * coefficient c j *
        ((dvdIndicator (resolution b i) n : ℝ) * dvdIndicator (resolution c j) n) := by
    rw [profile_relational, profile_relational, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hprod]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  unfold relationalMean
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hinner := divisibility_inner (resolution_pos hb i) (resolution_pos hc j) hL
    ((resolution_dvd_slope hb i).trans hbL) ((resolution_dvd_slope hc j).trans hcL)
  rw [← hinner]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Identification with the official all-bases mean kernel. -/
theorem periodicMeanKernel_relational (b c : CameraIndex) :
    periodicMeanKernel b c = relationalMean (cameraLabel b) (cameraLabel c) := by
  exact periodicProductMean_relational b.property c.property (pairPeriod_pos b c)
    (cameraSlope_dvd_pairPeriod_left b c) (cameraSlope_dvd_pairPeriod_right b c)

/-- Identification with the official all-bases native Gram, for arbitrary supported cameras. -/
theorem gramKernel_relational (b c : CameraIndex) :
    gramKernel b c = (min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) *
      relationalMean (cameraLabel b) (cameraLabel c) := by
  rw [gramKernel, periodicMeanKernel_relational]

/-- Full resolution-indexed double `Finsupp` formula for the official native Gram. -/
theorem gramKernel_finsupp (b c : CameraIndex) :
    gramKernel b c = (min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) *
      (profileCoefficients (cameraLabel b)).sum (fun d a =>
        (profileCoefficients (cameraLabel c)).sum (fun e z =>
          a * z * divisibilityKernel d e)) := by
  rw [gramKernel_relational, ← relationalForm_profileCoefficients]
  simp only [relationalForm, Finsupp.linearCombination_apply, smul_eq_mul,
    Finsupp.sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- Six-camera specialization reuses the existing exact rational certificate. -/
theorem sixCamera_relational_certificate :
    (fun i j : Fin 6 => (min (cameraSlope (sixCamera i)) (cameraSlope (sixCamera j)) : ℕ) *
      relationalMean (sixCamera i) (sixCamera j)) = sixCameraGram := by
  rw [← sixCameraGram_eq]
  ext i j
  rw [periodicGramMatrix_apply, periodicProductMean_relational]
  · exact (by simp [sixCamera])
  · exact (by simp [sixCamera])
  · norm_num
  · exact sixCamera_commonPeriod i
  · exact sixCamera_commonPeriod j

/-- Rational coefficients used only for the exact six-camera entry certificate. -/
def coefficientRat (b : ℕ) : Fin 3 → ℚ :=
  if b = 2 then ![1, -1, -2] else if Odd b then ![1, -(b : ℚ), 0]
  else ![1, 1, -((b + 2 : ℕ) : ℚ)]

/-- Rational form of the same finite relational synthesis. -/
def relationalMeanRat (b c : ℕ) : ℚ :=
  ∑ i : Fin 3, ∑ j : Fin 3, coefficientRat b i * coefficientRat c j /
    (Nat.lcm (resolution b i) (resolution c j) : ℚ)

theorem relationalMeanRat_cast (b c : ℕ) :
    (relationalMeanRat b c : ℝ) = relationalMean b c := by
  have hc (b : ℕ) (i : Fin 3) : (coefficientRat b i : ℝ) = coefficient b i := by
    unfold coefficientRat coefficient
    split_ifs <;> fin_cases i <;> simp
  simp [relationalMeanRat, hc, relationalMean, divisibilityKernel, div_eq_mul_inv]

/-- All 36 entries are certified over the rationals using only nine resolution crosses. -/
theorem sixCamera_relational_rational_certificate :
    (fun i j : Fin 6 => (min (cameraSlope (sixCamera i)) (cameraSlope (sixCamera j)) : ℚ) *
      relationalMeanRat (sixCamera i) (sixCamera j)) = sixCameraGramRat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCamera, cameraSlope, relationalMeanRat, coefficientRat, resolution,
      sixCameraGramRat, Fin.sum_univ_succ]

/-- The existing completed camera Hilbert space realizes the relational Gram. -/
theorem inner_cameraVector_relational (b c : CameraIndex) :
    inner ℝ (cameraVector b) (cameraVector c) =
      (min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) *
        relationalMean (cameraLabel b) (cameraLabel c) := by
  rw [inner_cameraVector, gramKernel_relational]

/-- The existing Naimark isometry realizes the very same relational Gram. -/
theorem inner_naimarkCameraVector_relational (b c : CameraIndex) :
    inner ℝ (naimarkCameraVector b) (naimarkCameraVector c) =
      (min (cameraSlope (cameraLabel b)) (cameraSlope (cameraLabel c)) : ℕ) *
        relationalMean (cameraLabel b) (cameraLabel c) := by
  rw [inner_naimarkCameraVector, gramKernel_relational]

/-- Symmetric unit second difference on the finite period-420 carrier. -/
def periodicSecondDifference (q : Fin 420 → ℝ) (n : Fin 420) : ℝ :=
  2 * q n - q ⟨(n.val + 1) % 420, Nat.mod_lt _ (by norm_num)⟩ -
    q ⟨(n.val + 419) % 420, Nat.mod_lt _ (by norm_num)⟩

/-- The six-camera profile span is not invariant under the unit second difference.
Residues 1 and 13 agree in every camera, but the C5 second difference separates them. -/
theorem secondDifference_c5_not_in_sixCamera_span :
    ¬ ∃ a : Fin 6 → ℝ, ∀ n : Fin 420,
      periodicSecondDifference (fun n => (profile 5 n.val : ℝ)) n =
        ∑ i : Fin 6, a i * (profile (sixCamera i) n.val : ℝ) := by
  rintro ⟨a, ha⟩
  have h1 := ha ⟨1, by norm_num⟩
  have h13 := ha ⟨13, by norm_num⟩
  have hprofiles (i : Fin 6) : profile (sixCamera i) 1 = profile (sixCamera i) 13 := by
    fin_cases i <;> norm_num [sixCamera, profile, c2Profile, oddProfile, evenProfile,
      dvdIndicator]
  simp_rw [hprofiles] at h1
  have hsame := h1.trans h13.symm
  norm_num [periodicSecondDifference, profile, oddProfile, dvdIndicator] at hsame

end NativeCarrySpectralWeyl.Finite.Relational
