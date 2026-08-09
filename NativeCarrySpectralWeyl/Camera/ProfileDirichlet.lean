import NativeCarrySpectralWeyl.Camera.NaturalInteriorProfile
import NativeCarrySpectralWeyl.Camera.Factors
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.PNat.Basic

open scoped BigOperators

/-!
# Absolutely convergent Dirichlet series of camera profiles

For `1 < re s`, this module proves that the positive-index Dirichlet series of
every supported periodic camera profile is its explicit camera factor times a
single base series.  The base series is also identified with Mathlib's
`riemannZeta` in precisely that half-plane.

This is only the absolutely convergent profile calculation.  It does not
define the normally convergent bracket characteristic on `re s > -1`, perform
analytic continuation, or assert any common-zero statement.
-/

namespace NativeCarrySpectralWeyl.Camera

noncomputable section

private def pnatMulEquivDvd (divisor : ℕ+) :
    ℕ+ ≃ ↥({n : ℕ+ | divisor ∣ n} : Set ℕ+) where
  toFun n := ⟨divisor * n, dvd_mul_right divisor n⟩
  invFun n := PNat.divExact n divisor
  left_inv n := by
    exact mul_left_cancel (PNat.mul_div_exact (dvd_mul_right divisor n))
  right_inv n := by
    apply Subtype.ext
    exact PNat.mul_div_exact n.property

/-- The positive-index Dirichlet monomial `n⁻ˢ`. -/
def positiveDirichletTerm (s : ℂ) (n : ℕ+) : ℂ :=
  (n : ℂ) ^ (-s)

/-- The common positive-index Dirichlet series used by every camera profile. -/
def positiveDirichletSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ+, positiveDirichletTerm s n

/-- The positive-index Dirichlet monomials are summable when `1 < re s`. -/
theorem positiveDirichletTerm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (positiveDirichletTerm s) := by
  exact (summable_pnat_iff_summable_succ
    (f := fun m : ℕ => (m : ℂ) ^ (-s))).mpr (by
      simpa [positiveDirichletTerm, Function.comp_def, Complex.cpow_neg, one_div] using
        (Complex.summable_one_div_nat_cpow.mpr hs).comp_injective Nat.succ_injective)

/-- In its convergence half-plane, the base series is Mathlib's `riemannZeta`. -/
theorem positiveDirichletSeries_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    positiveDirichletSeries s = riemannZeta s := by
  unfold positiveDirichletSeries
  calc
    (∑' n : ℕ+, positiveDirichletTerm s n) =
        ∑' n : ℕ, (n + 1 : ℂ) ^ (-s) := by
          simpa [positiveDirichletTerm] using
            (tsum_pnat_eq_tsum_succ
              (f := fun m : ℕ => (m : ℂ) ^ (-s)))
    _ = riemannZeta s := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
      apply tsum_congr
      intro n
      simp [Complex.cpow_neg, one_div]

/-- Reindexing the Dirichlet series on positive multiples of a divisor. -/
theorem dvdIndicatorDirichletSeries (divisor : ℕ) (hdivisor : 0 < divisor)
    (s : ℂ) :
    ∑' n : ℕ+, ((dvdIndicator divisor n : ℤ) : ℂ) * positiveDirichletTerm s n =
      (divisor : ℂ) ^ (-s) * positiveDirichletSeries s := by
  let divisorPos : ℕ+ := ⟨divisor, hdivisor⟩
  let multiples : Set ℕ+ := {n | divisorPos ∣ n}
  have hindicator :
      (fun n : ℕ+ => ((dvdIndicator divisor n : ℤ) : ℂ) * positiveDirichletTerm s n) =
        multiples.indicator (positiveDirichletTerm s) := by
    funext n
    by_cases hmultiple : divisor ∣ (n : ℕ)
    · have hpnat : divisorPos ∣ n := PNat.dvd_iff.mpr hmultiple
      simp [multiples, dvdIndicator, hmultiple, hpnat]
    · have hpnat : ¬divisorPos ∣ n := fun h => hmultiple (PNat.dvd_iff.mp h)
      simp [multiples, dvdIndicator, hmultiple, hpnat]
  rw [hindicator]
  rw [← tsum_subtype]
  dsimp [multiples]
  rw [← (pnatMulEquivDvd divisorPos).tsum_eq]
  change (∑' n : ℕ+, ((divisor * (n : ℕ) : ℕ) : ℂ) ^ (-s)) =
    (divisor : ℂ) ^ (-s) * positiveDirichletSeries s
  have hterm :
      (fun n : ℕ+ => ((divisor * (n : ℕ) : ℕ) : ℂ) ^ (-s)) =
        fun n : ℕ+ => (divisor : ℂ) ^ (-s) * ((n : ℕ) : ℂ) ^ (-s) := by
    funext n
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  rw [hterm]
  rw [tsum_mul_left]
  rfl

private theorem dvdIndicator_mul_term_eq_indicator (divisor : ℕ) (hdivisor : 0 < divisor)
    (s : ℂ) :
    (fun n : ℕ+ => ((dvdIndicator divisor n : ℤ) : ℂ) * positiveDirichletTerm s n) =
      ({n : ℕ+ | (⟨divisor, hdivisor⟩ : ℕ+) ∣ n} : Set ℕ+).indicator
        (positiveDirichletTerm s) := by
  funext n
  by_cases hmultiple : divisor ∣ (n : ℕ)
  · have hpnat : (⟨divisor, hdivisor⟩ : ℕ+) ∣ n := PNat.dvd_iff.mpr hmultiple
    simp [dvdIndicator, hmultiple, hpnat]
  · have hpnat : ¬(⟨divisor, hdivisor⟩ : ℕ+) ∣ n :=
      fun h => hmultiple (PNat.dvd_iff.mp h)
    simp [dvdIndicator, hmultiple, hpnat]

/-- A divisibility-indicator subseries is summable when the base series is. -/
theorem dvdIndicatorDirichletTerm_summable (divisor : ℕ) (hdivisor : 0 < divisor)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ+ =>
      ((dvdIndicator divisor n : ℤ) : ℂ) * positiveDirichletTerm s n) := by
  rw [dvdIndicator_mul_term_eq_indicator divisor hdivisor s]
  exact (positiveDirichletTerm_summable hs).indicator _

/-- One integer coefficient multiplied by its positive-index Dirichlet monomial. -/
def coefficientDirichletTerm (coeff : ℕ → ℤ) (s : ℂ) (n : ℕ+) : ℂ :=
  (coeff n : ℂ) * positiveDirichletTerm s n

/-- Dirichlet series attached to an integer coefficient profile. -/
def coefficientDirichletSeries (coeff : ℕ → ℤ) (s : ℂ) : ℂ :=
  ∑' n : ℕ+, coefficientDirichletTerm coeff s n

/-- The aligned C2 profile series is summable for `1 < re s`. -/
theorem c2ProfileDirichletTerm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (coefficientDirichletTerm c2Profile s) := by
  have hbase := positiveDirichletTerm_summable hs
  have htwo := dvdIndicatorDirichletTerm_summable 2 (by omega) hs
  have hfour := dvdIndicatorDirichletTerm_summable 4 (by omega) hs
  have hsum := (hbase.sub htwo).sub (hfour.mul_left (2 : ℂ))
  refine hsum.congr ?_
  intro n
  simp [coefficientDirichletTerm, c2Profile]
  ring

/-- Every positive odd-camera profile series is summable for `1 < re s`. -/
theorem oddProfileDirichletTerm_summable {camera : ℕ} (hcamera : 0 < camera)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (coefficientDirichletTerm (oddProfile camera) s) := by
  have hbase := positiveDirichletTerm_summable hs
  have hdvd := dvdIndicatorDirichletTerm_summable camera hcamera hs
  have hsum := hbase.sub (hdvd.mul_left (camera : ℂ))
  refine hsum.congr ?_
  intro n
  simp [coefficientDirichletTerm, oddProfile]
  ring

/-- Every supported even-camera profile series is summable for `1 < re s`. -/
theorem evenProfileDirichletTerm_summable {camera : ℕ} (hcamera : 4 ≤ camera)
    (heven : Even camera) {s : ℂ} (hs : 1 < s.re) :
    Summable (coefficientDirichletTerm (evenProfile camera) s) := by
  obtain ⟨half, rfl⟩ := heven
  have hhalf : 0 < half := by omega
  have hcameraPos : 0 < half + half := by omega
  have hdiv : (half + half) / 2 = half := by omega
  have hbase := positiveDirichletTerm_summable hs
  have hhalfDvd := dvdIndicatorDirichletTerm_summable half hhalf hs
  have hcameraDvd := dvdIndicatorDirichletTerm_summable
    (half + half) hcameraPos hs
  have hsum := (hbase.add hhalfDvd).sub
    (hcameraDvd.mul_left ((half + half + 2 : ℕ) : ℂ))
  refine hsum.congr ?_
  intro n
  simp [coefficientDirichletTerm, evenProfile, hdiv]
  ring

/-- The aligned C2 profile series is `c2Factor` times the common base series. -/
theorem c2ProfileDirichletSeries_factorization {s : ℂ} (hs : 1 < s.re) :
    coefficientDirichletSeries c2Profile s =
      c2Factor s * positiveDirichletSeries s := by
  have hbase := positiveDirichletTerm_summable hs
  have htwo := dvdIndicatorDirichletTerm_summable 2 (by omega) hs
  have hfour := dvdIndicatorDirichletTerm_summable 4 (by omega) hs
  have hpowOne : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show 1 - s = 1 + (-s) by ring, Complex.cpow_add]
    · simp
    · norm_num
  have hpowFour : (4 : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (-s) := by
    convert Complex.natCast_mul_natCast_cpow 2 2 (-s) using 1 <;> norm_num
  calc
    coefficientDirichletSeries c2Profile s =
        ∑' n : ℕ+, ((positiveDirichletTerm s n -
          ((dvdIndicator 2 n : ℤ) : ℂ) * positiveDirichletTerm s n) -
          2 * (((dvdIndicator 4 n : ℤ) : ℂ) * positiveDirichletTerm s n)) := by
            apply tsum_congr
            intro n
            simp [coefficientDirichletTerm, c2Profile]
            ring
    _ = positiveDirichletSeries s -
          (2 : ℂ) ^ (-s) * positiveDirichletSeries s -
          2 * ((4 : ℂ) ^ (-s) * positiveDirichletSeries s) := by
            rw [Summable.tsum_sub (hbase.sub htwo) (hfour.mul_left (2 : ℂ)),
              Summable.tsum_sub hbase htwo, tsum_mul_left,
              dvdIndicatorDirichletSeries 2 (by omega) s,
              dvdIndicatorDirichletSeries 4 (by omega) s]
            rfl
    _ = c2Factor s * positiveDirichletSeries s := by
      rw [c2Factor, hpowOne, hpowFour]
      ring

/-- An odd-camera profile series is `oddFactor` times the common base series. -/
theorem oddProfileDirichletSeries_factorization {camera : ℕ} (hcamera : 0 < camera)
    {s : ℂ} (hs : 1 < s.re) :
    coefficientDirichletSeries (oddProfile camera) s =
      oddFactor camera s * positiveDirichletSeries s := by
  have hbase := positiveDirichletTerm_summable hs
  have hdvd := dvdIndicatorDirichletTerm_summable camera hcamera hs
  have hpow : (camera : ℂ) ^ (1 - s) =
      (camera : ℂ) * (camera : ℂ) ^ (-s) := by
    rw [show 1 - s = 1 + (-s) by ring, Complex.cpow_add]
    · simp
    · exact_mod_cast hcamera.ne'
  calc
    coefficientDirichletSeries (oddProfile camera) s =
        ∑' n : ℕ+, (positiveDirichletTerm s n -
          (camera : ℂ) *
            (((dvdIndicator camera n : ℤ) : ℂ) * positiveDirichletTerm s n)) := by
              apply tsum_congr
              intro n
              simp [coefficientDirichletTerm, oddProfile]
              ring
    _ = positiveDirichletSeries s -
          (camera : ℂ) * ((camera : ℂ) ^ (-s) * positiveDirichletSeries s) := by
            rw [Summable.tsum_sub hbase (hdvd.mul_left (camera : ℂ)),
              tsum_mul_left, dvdIndicatorDirichletSeries camera hcamera s]
            rfl
    _ = oddFactor camera s * positiveDirichletSeries s := by
      rw [oddFactor, hpow]
      ring

/-- An even-camera profile series is `evenFactor` times the common base series. -/
theorem evenProfileDirichletSeries_factorization {camera : ℕ} (hcamera : 4 ≤ camera)
    (heven : Even camera) {s : ℂ} (hs : 1 < s.re) :
    coefficientDirichletSeries (evenProfile camera) s =
      evenFactor camera s * positiveDirichletSeries s := by
  obtain ⟨half, rfl⟩ := heven
  have hhalf : 0 < half := by omega
  have hcameraPos : 0 < half + half := by omega
  have hdiv : (half + half) / 2 = half := by omega
  have hbase := positiveDirichletTerm_summable hs
  have hhalfDvd := dvdIndicatorDirichletTerm_summable half hhalf hs
  have hcameraDvd := dvdIndicatorDirichletTerm_summable
    (half + half) hcameraPos hs
  calc
    coefficientDirichletSeries (evenProfile (half + half)) s =
        ∑' n : ℕ+, (positiveDirichletTerm s n +
          ((dvdIndicator half n : ℤ) : ℂ) * positiveDirichletTerm s n -
          ((half + half + 2 : ℕ) : ℂ) *
            (((dvdIndicator (half + half) n : ℤ) : ℂ) * positiveDirichletTerm s n)) := by
              apply tsum_congr
              intro n
              simp [coefficientDirichletTerm, evenProfile, hdiv]
              ring
    _ = (positiveDirichletSeries s +
          (half : ℂ) ^ (-s) * positiveDirichletSeries s) -
          ((half + half + 2 : ℕ) : ℂ) *
            (((half + half : ℕ) : ℂ) ^ (-s) * positiveDirichletSeries s) := by
              rw [Summable.tsum_sub (hbase.add hhalfDvd)
                (hcameraDvd.mul_left ((half + half + 2 : ℕ) : ℂ)),
                Summable.tsum_add hbase hhalfDvd, tsum_mul_left,
                dvdIndicatorDirichletSeries half hhalf s,
                dvdIndicatorDirichletSeries (half + half) hcameraPos s]
              simp only [positiveDirichletSeries]
    _ = evenFactor (half + half) s * positiveDirichletSeries s := by
      rw [evenFactor, hdiv]
      ring

/-- Dirichlet series of the unified periodic profile for a camera. -/
def profileDirichletSeries (camera : ℕ) (s : ℂ) : ℂ :=
  coefficientDirichletSeries (profile camera) s

/-- Every supported unified camera-profile series is summable for `1 < re s`. -/
theorem profileDirichletTerm_summable {camera : ℕ} (hcamera : 2 ≤ camera)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (coefficientDirichletTerm (profile camera) s) := by
  by_cases htwo : camera = 2
  · subst camera
    rw [show profile 2 = c2Profile from funext profile_two]
    exact c2ProfileDirichletTerm_summable hs
  · rcases Nat.even_or_odd camera with heven | hodd
    · have hcameraEven : 4 ≤ camera := by
        obtain ⟨half, hhalf⟩ := heven
        omega
      rw [show profile camera = evenProfile camera from
        funext (profile_of_even htwo heven)]
      exact evenProfileDirichletTerm_summable hcameraEven heven hs
    · rw [show profile camera = oddProfile camera from
        funext (profile_of_odd htwo hodd)]
      exact oddProfileDirichletTerm_summable
        (lt_of_lt_of_le (by omega) hcamera) hs

/-- Every supported unified camera-profile series is absolutely summable for `1 < re s`. -/
theorem profileDirichletTerm_norm_summable {camera : ℕ} (hcamera : 2 ≤ camera)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖coefficientDirichletTerm (profile camera) s n‖) :=
  summable_norm_iff.mpr (profileDirichletTerm_summable hcamera hs)

/-- Every supported profile series factors through its explicit camera multiplier. -/
theorem profileDirichletSeries_factorization {camera : ℕ} (hcamera : 2 ≤ camera)
    {s : ℂ} (hs : 1 < s.re) :
    profileDirichletSeries camera s =
      factor camera s * positiveDirichletSeries s := by
  by_cases htwo : camera = 2
  · subst camera
    unfold profileDirichletSeries
    rw [show profile 2 = c2Profile from funext profile_two, factor_two]
    exact c2ProfileDirichletSeries_factorization hs
  · rcases Nat.even_or_odd camera with heven | hodd
    · have hcameraEven : 4 ≤ camera := by
        obtain ⟨half, hhalf⟩ := heven
        omega
      unfold profileDirichletSeries
      rw [show profile camera = evenProfile camera from
        funext (profile_of_even htwo heven), factor_of_even htwo heven]
      exact evenProfileDirichletSeries_factorization hcameraEven heven hs
    · unfold profileDirichletSeries
      rw [show profile camera = oddProfile camera from
        funext (profile_of_odd htwo hodd), factor_of_odd htwo hodd]
      exact oddProfileDirichletSeries_factorization
        (lt_of_lt_of_le (by omega) hcamera) hs

/-- The profile factorization written using Mathlib's zeta function on `re s > 1`. -/
theorem profileDirichletSeries_eq_factor_mul_riemannZeta {camera : ℕ}
    (hcamera : 2 ≤ camera) {s : ℂ} (hs : 1 < s.re) :
    profileDirichletSeries camera s = factor camera s * riemannZeta s := by
  rw [profileDirichletSeries_factorization hcamera hs,
    positiveDirichletSeries_eq_riemannZeta hs]

end

end NativeCarrySpectralWeyl.Camera
