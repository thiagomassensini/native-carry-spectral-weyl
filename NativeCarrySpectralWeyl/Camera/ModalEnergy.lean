import NativeCarrySpectralWeyl.Camera.ZeroMultiplicity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Native modal energies and doubled real zero order

The source notes define five limiting modal energies on the native line.  Four
come from the pure sectors `3`, `4`, `5`, and `7`; the sector `4` is the
canonical aggregate of its rank-two eigenspace and carries only the binary
defect factor `1 - 2^(1-s)`.  The mixed sector uses that binary factor times
`A₃`.  In every case the energy is a positive constant times the squared
complex norm of a holomorphic modal amplitude.

The order statement requires care: the amplitude has a complex analytic order
at `s₀ = 1/2 + it₀`, while its energy is a real-analytic function of `t` and is
not holomorphic in `s`.  This module proves the bridge to the real line and
then proves that `Complex.normSq` doubles every finite zero order.  A positive
analytic weight has order zero, so it does not alter the resulting order
`2m`.
-/

open Filter
open scoped Topology

namespace NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## Generic real-energy lemmas -/

/-- The squared complex norm of a real-analytic complex amplitude is
real-analytic. -/
theorem normSq_analyticAt {amplitude : ℝ → ℂ} {t : ℝ}
    (hamplitude : AnalyticAt ℝ amplitude t) :
    AnalyticAt ℝ (fun x => Complex.normSq (amplitude x)) t := by
  have heq : (fun x => Complex.normSq (amplitude x)) =
      (Complex.reCLM ∘ amplitude) * (Complex.reCLM ∘ amplitude) +
        (Complex.imCLM ∘ amplitude) * (Complex.imCLM ∘ amplitude) := by
    funext x
    simp [Complex.normSq_apply]
  rw [heq]
  exact (((Complex.reCLM.analyticAt (amplitude t)).comp hamplitude).mul
    ((Complex.reCLM.analyticAt (amplitude t)).comp hamplitude)).add
      (((Complex.imCLM.analyticAt (amplitude t)).comp hamplitude).mul
        ((Complex.imCLM.analyticAt (amplitude t)).comp hamplitude))

/-- Restricting a holomorphic function to the real axis preserves every
finite analytic zero order. -/
theorem analyticOrderAt_realRestriction_eq {f : ℂ → ℂ} {t : ℝ} {order : ℕ}
    (hf : AnalyticAt ℂ f (t : ℂ))
    (horder : analyticOrderAt f (t : ℂ) = (order : ℕ∞)) :
    analyticOrderAt (fun x : ℝ => f (x : ℂ)) t = (order : ℕ∞) := by
  have hfReal : AnalyticAt ℝ (fun x : ℝ => f (x : ℂ)) t :=
    hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
  rw [hfReal.analyticOrderAt_eq_natCast]
  obtain ⟨g, hg, hgne, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp horder
  refine ⟨fun x : ℝ => g (x : ℂ),
    hg.restrictScalars.comp (Complex.ofRealCLM.analyticAt t), ?_, ?_⟩
  · simpa using hgne
  · have hfgReal := Complex.continuous_ofReal.tendsto t |>.eventually hfg
    filter_upwards [hfgReal] with x hx
    simpa [smul_eq_mul] using hx

/-- Squared complex norm doubles the finite analytic order of a real-analytic
complex amplitude. -/
theorem normSq_analyticOrderAt_eq_two_mul {amplitude : ℝ → ℂ} {t : ℝ}
    {order : ℕ} (hamplitude : AnalyticAt ℝ amplitude t)
    (horder : analyticOrderAt amplitude t = (order : ℕ∞)) :
    analyticOrderAt (fun x => Complex.normSq (amplitude x)) t =
      (2 * order : ℕ) := by
  have henergy := normSq_analyticAt hamplitude
  rw [henergy.analyticOrderAt_eq_natCast]
  obtain ⟨g, hg, hgne, hfg⟩ :=
    hamplitude.analyticOrderAt_eq_natCast.mp horder
  refine ⟨fun x => Complex.normSq (g x), normSq_analyticAt hg, ?_, ?_⟩
  · simpa only [ne_eq, Complex.normSq_eq_zero] using hgne
  · filter_upwards [hfg] with x hx
    rw [hx]
    simp only [Complex.normSq_apply, Complex.smul_re, Complex.smul_im,
      smul_eq_mul]
    ring

/-- Multiplication by a nonzero real-analytic weight preserves the doubled
order of a squared complex amplitude. -/
theorem weightedNormSq_analyticOrderAt_eq_two_mul {weight : ℝ → ℝ}
    {amplitude : ℝ → ℂ} {t : ℝ} {order : ℕ}
    (hweight : AnalyticAt ℝ weight t) (hweightNe : weight t ≠ 0)
    (hamplitude : AnalyticAt ℝ amplitude t)
    (horder : analyticOrderAt amplitude t = (order : ℕ∞)) :
    analyticOrderAt
        (fun x => weight x * Complex.normSq (amplitude x)) t =
      (2 * order : ℕ) := by
  have hnormSq := normSq_analyticAt hamplitude
  change analyticOrderAt (weight * fun x => Complex.normSq (amplitude x)) t = _
  rw [analyticOrderAt_mul hweight hnormSq,
    hweight.analyticOrderAt_eq_zero.mpr hweightNe,
    normSq_analyticOrderAt_eq_two_mul hamplitude horder, zero_add]

/-! ## The native-line bridge -/

/-- Complex-affine extension of the real native-line parametrization. -/
def nativeLineComplex (z : ℂ) : ℂ := (1 / 2 : ℂ) + z * Complex.I

@[simp] theorem nativeLineComplex_ofReal (t : ℝ) :
    nativeLineComplex (t : ℂ) = nativeLine t := by
  simp [nativeLineComplex, nativeLine, mul_comm]

/-- The complex-affine native-line parametrization has derivative `I`. -/
theorem hasDerivAt_nativeLineComplex (z : ℂ) :
    HasDerivAt nativeLineComplex Complex.I z := by
  change HasDerivAt (fun w : ℂ => (1 / 2 : ℂ) + w * Complex.I)
    Complex.I z
  exact (hasDerivAt_mul_const Complex.I).const_add (1 / 2 : ℂ)

/-- The complex-affine native-line parametrization is entire. -/
theorem analyticAt_nativeLineComplex (z : ℂ) :
    AnalyticAt ℂ nativeLineComplex z := by
  change AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w * Complex.I) z
  fun_prop

/-- A holomorphic amplitude remains real-analytic after restriction to the
native line. -/
theorem analyticAt_comp_nativeLine {f : ℂ → ℂ} {t : ℝ}
    (hf : AnalyticAt ℂ f (nativeLine t)) :
    AnalyticAt ℝ (fun x : ℝ => f (nativeLine x)) t := by
  have hline : AnalyticAt ℂ nativeLineComplex (t : ℂ) :=
    analyticAt_nativeLineComplex (t : ℂ)
  have hfcomp : AnalyticAt ℂ (f ∘ nativeLineComplex) (t : ℂ) := by
    exact hf.comp_of_eq hline (nativeLineComplex_ofReal t)
  have hrestricted :
      AnalyticAt ℝ (fun x : ℝ => (f ∘ nativeLineComplex) (x : ℂ)) t :=
    hfcomp.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
  simpa [Function.comp_def] using hrestricted

/-- Restriction to the native line preserves every finite holomorphic zero
order because the affine parametrization has nonzero derivative `I`. -/
theorem analyticOrderAt_comp_nativeLine_eq {f : ℂ → ℂ} {t : ℝ}
    {order : ℕ} (hf : AnalyticAt ℂ f (nativeLine t))
    (horder : analyticOrderAt f (nativeLine t) = (order : ℕ∞)) :
    analyticOrderAt (fun x : ℝ => f (nativeLine x)) t =
      (order : ℕ∞) := by
  have hline : AnalyticAt ℂ nativeLineComplex (t : ℂ) :=
    analyticAt_nativeLineComplex (t : ℂ)
  have hderiv : deriv nativeLineComplex (t : ℂ) ≠ 0 := by
    rw [(hasDerivAt_nativeLineComplex (t : ℂ)).deriv]
    exact Complex.I_ne_zero
  have hcompOrder :
      analyticOrderAt (f ∘ nativeLineComplex) (t : ℂ) =
        analyticOrderAt f (nativeLineComplex (t : ℂ)) :=
    analyticOrderAt_comp_of_deriv_ne_zero hline hderiv
  have hfcomp : AnalyticAt ℂ (f ∘ nativeLineComplex) (t : ℂ) := by
    exact hf.comp_of_eq hline (nativeLineComplex_ofReal t)
  have hrestricted := analyticOrderAt_realRestriction_eq hfcomp
    (hcompOrder.trans (by simpa using horder))
  simpa [Function.comp_def] using hrestricted

/-! ## Five limiting modal sectors -/

/-- The five limiting spectral sectors in the source decomposition.  `mode4`
denotes the canonical aggregate of the rank-two `log 4` eigenspace. -/
inductive ModalSector where
  | mode3
  | mode4
  | mode5
  | mode7
  | mixed
  deriving DecidableEq, Fintype, Repr

/-- Positive normalization constant in each closed modal-energy formula. -/
def modalCoefficient : ModalSector → ℝ
  | .mode3 => 1 / 6
  | .mode4 => 1 / 2
  | .mode5 => 1 / 20
  | .mode7 => 1 / 42
  | .mixed => 8 / 139

/-- The binary defect factor left after the canonical rank-two mode-4 Gram
aggregation.  It is the second factor of the exceptional C2 camera factor. -/
def binaryDefectFactor (s : ℂ) : ℂ :=
  1 - (2 : ℂ) ^ (1 - s)

/-- Holomorphic local factor carried by each modal amplitude.  The rank-two
sector uses the binary defect factor; the mixed sector uses its product with
`A₃`. -/
def modalFactor : ModalSector → ℂ → ℂ
  | .mode3 => factor 3
  | .mode4 => binaryDefectFactor
  | .mode5 => factor 5
  | .mode7 => factor 7
  | .mixed => fun s => binaryDefectFactor s * factor 3 s

/-- Limiting holomorphic modal amplitude after common scalarization. -/
def modalAmplitude (sector : ModalSector) (s : ℂ) : ℂ :=
  modalFactor sector s * nativeScalar s

/-- Positive native-line modal weight `Q_j(t)`. -/
def modalWeight (sector : ModalSector) (t : ℝ) : ℝ :=
  modalCoefficient sector * Complex.normSq (modalFactor sector (nativeLine t))

/-- Limiting modal energy as a real function of the native-line parameter. -/
def modalEnergy (sector : ModalSector) (t : ℝ) : ℝ :=
  modalCoefficient sector *
    Complex.normSq (modalAmplitude sector (nativeLine t))

theorem modalCoefficient_pos (sector : ModalSector) :
    0 < modalCoefficient sector := by
  cases sector <;> norm_num [modalCoefficient]

/-- The binary defect factor is entire. -/
theorem binaryDefectFactor_analyticAt (s : ℂ) :
    AnalyticAt ℂ binaryDefectFactor s := by
  change AnalyticAt ℂ (oddFactor 2) s
  exact (oddFactor_differentiable (by omega : 0 < 2)).analyticAt s

/-- The binary defect factor is nonzero on the native line. -/
theorem binaryDefectFactor_nativeLine_ne_zero (t : ℝ) :
    binaryDefectFactor (nativeLine t) ≠ 0 := by
  have hc2 : c2Factor (nativeLine t) ≠ 0 := by
    simpa [factor_two] using
      (factor_nativeLine_ne_zero (by omega : 2 ≤ 2) t)
  exact (c2Factor_ne_zero_iff (nativeLine t)).mp hc2 |>.2

/-- Every modal factor is entire. -/
theorem modalFactor_analyticAt (sector : ModalSector) (s : ℂ) :
    AnalyticAt ℂ (modalFactor sector) s := by
  cases sector with
  | mode3 => exact (factor_differentiable (by omega : 2 ≤ 3)).analyticAt s
  | mode4 => exact binaryDefectFactor_analyticAt s
  | mode5 => exact (factor_differentiable (by omega : 2 ≤ 5)).analyticAt s
  | mode7 => exact (factor_differentiable (by omega : 2 ≤ 7)).analyticAt s
  | mixed =>
      exact (binaryDefectFactor_analyticAt s).mul
        ((factor_differentiable (by omega : 2 ≤ 3)).analyticAt s)

/-- Every modal factor is nonzero on the native line. -/
theorem modalFactor_nativeLine_ne_zero (sector : ModalSector) (t : ℝ) :
    modalFactor sector (nativeLine t) ≠ 0 := by
  cases sector with
  | mode3 => exact factor_nativeLine_ne_zero (by omega : 2 ≤ 3) t
  | mode4 => exact binaryDefectFactor_nativeLine_ne_zero t
  | mode5 => exact factor_nativeLine_ne_zero (by omega : 2 ≤ 5) t
  | mode7 => exact factor_nativeLine_ne_zero (by omega : 2 ≤ 7) t
  | mixed =>
      exact mul_ne_zero
        (binaryDefectFactor_nativeLine_ne_zero t)
        (factor_nativeLine_ne_zero (by omega : 2 ≤ 3) t)

/-- Each modal amplitude is holomorphic at every native-line point. -/
theorem modalAmplitude_nativeLine_analyticAt (sector : ModalSector) (t : ℝ) :
    AnalyticAt ℂ (modalAmplitude sector) (nativeLine t) := by
  have hdomain : nativeLine t ∈ nativeScalarDomain := by
    simp [nativeScalarDomain]
    norm_num
  exact (modalFactor_analyticAt sector (nativeLine t)).mul
    (nativeScalar_analyticAt hdomain)

/-- Every modal amplitude has exactly the native scalar's complex analytic
order on the native line. -/
theorem modalAmplitude_nativeLine_analyticOrderAt_eq_nativeScalar
    (sector : ModalSector) (t : ℝ) :
    analyticOrderAt (modalAmplitude sector) (nativeLine t) =
      analyticOrderAt nativeScalar (nativeLine t) := by
  have hdomain : nativeLine t ∈ nativeScalarDomain := by
    simp [nativeScalarDomain]
    norm_num
  change analyticOrderAt (modalFactor sector * nativeScalar) (nativeLine t) = _
  rw [analyticOrderAt_mul (modalFactor_analyticAt sector (nativeLine t))
    (nativeScalar_analyticAt hdomain)]
  rw [(modalFactor_analyticAt sector (nativeLine t)).analyticOrderAt_eq_zero.mpr
    (modalFactor_nativeLine_ne_zero sector t), zero_add]

/-- The mode-3 amplitude is the camera-3 characteristic on the native scalar
domain. -/
theorem modalAmplitude_mode3_eq_bracketCharacteristic {s : ℂ}
    (hs : s ∈ nativeScalarDomain) :
    modalAmplitude .mode3 s = bracketCharacteristic 3 s := by
  simpa [modalAmplitude, modalFactor] using
    (bracketCharacteristic_eq_factor_mul_nativeScalar
      (by omega : 2 ≤ 3) hs).symm

/-- The canonical rank-two mode-4 aggregate carries exactly the binary defect
factor, without the extra first factor of the exceptional C2 camera. -/
theorem modalAmplitude_mode4_eq_binaryDefectFactor_mul_nativeScalar (s : ℂ) :
    modalAmplitude .mode4 s = binaryDefectFactor s * nativeScalar s := by
  rfl

/-- The mode-5 amplitude is the camera-5 characteristic on the native scalar
domain. -/
theorem modalAmplitude_mode5_eq_bracketCharacteristic {s : ℂ}
    (hs : s ∈ nativeScalarDomain) :
    modalAmplitude .mode5 s = bracketCharacteristic 5 s := by
  simpa [modalAmplitude, modalFactor] using
    (bracketCharacteristic_eq_factor_mul_nativeScalar
      (by omega : 2 ≤ 5) hs).symm

/-- The mode-7 amplitude is the camera-7 characteristic on the native scalar
domain. -/
theorem modalAmplitude_mode7_eq_bracketCharacteristic {s : ℂ}
    (hs : s ∈ nativeScalarDomain) :
    modalAmplitude .mode7 s = bracketCharacteristic 7 s := by
  simpa [modalAmplitude, modalFactor] using
    (bracketCharacteristic_eq_factor_mul_nativeScalar
      (by omega : 2 ≤ 7) hs).symm

/-- The mixed modal amplitude carries exactly the product of the binary defect
factor and the mode-3 camera factor. -/
theorem modalAmplitude_mixed_eq_binaryDefectFactor_mul_factor_three_mul_nativeScalar
    (s : ℂ) :
    modalAmplitude .mixed s =
      (binaryDefectFactor s * factor 3 s) * nativeScalar s := by
  rfl

/-- Every modal weight is strictly positive on the native line. -/
theorem modalWeight_pos (sector : ModalSector) (t : ℝ) :
    0 < modalWeight sector t := by
  exact mul_pos (modalCoefficient_pos sector)
    (Complex.normSq_pos.mpr (modalFactor_nativeLine_ne_zero sector t))

/-- Exact source factorization `E_j(t) = Q_j(t) |Z_nat(s)|²`. -/
theorem modalEnergy_eq_modalWeight_mul_nativeScalar_normSq
    (sector : ModalSector) (t : ℝ) :
    modalEnergy sector t =
      modalWeight sector t * Complex.normSq (nativeScalar (nativeLine t)) := by
  unfold modalEnergy modalWeight modalAmplitude
  rw [Complex.normSq_mul]
  ring

/-- Every limiting modal energy is nonnegative. -/
theorem modalEnergy_nonneg (sector : ModalSector) (t : ℝ) :
    0 ≤ modalEnergy sector t := by
  exact mul_nonneg (modalCoefficient_pos sector).le
    (Complex.normSq_nonneg _)

/-- Each limiting modal energy vanishes exactly at a native-scalar zero. -/
theorem modalEnergy_eq_zero_iff_nativeScalar_eq_zero
    (sector : ModalSector) (t : ℝ) :
    modalEnergy sector t = 0 ↔ nativeScalar (nativeLine t) = 0 := by
  rw [modalEnergy_eq_modalWeight_mul_nativeScalar_normSq,
    mul_eq_zero, Complex.normSq_eq_zero]
  exact or_iff_right (ne_of_gt (modalWeight_pos sector t))

/-- All five limiting modal energies have the same zero set. -/
theorem modalEnergy_common_zero (sector₁ sector₂ : ModalSector) (t : ℝ) :
    modalEnergy sector₁ t = 0 ↔ modalEnergy sector₂ t = 0 := by
  rw [modalEnergy_eq_zero_iff_nativeScalar_eq_zero,
    modalEnergy_eq_zero_iff_nativeScalar_eq_zero]

/-- Every modal weight is real-analytic on the native line. -/
theorem modalWeight_analyticAt (sector : ModalSector) (t : ℝ) :
    AnalyticAt ℝ (modalWeight sector) t := by
  have hfactorLine :
      AnalyticAt ℝ (fun x : ℝ => modalFactor sector (nativeLine x)) t :=
    analyticAt_comp_nativeLine (modalFactor_analyticAt sector (nativeLine t))
  change AnalyticAt ℝ
    (fun x => modalCoefficient sector *
      Complex.normSq (modalFactor sector (nativeLine x))) t
  exact analyticAt_const.mul (normSq_analyticAt hfactorLine)

/-- Every limiting modal energy is real-analytic in the native-line
parameter. -/
theorem modalEnergy_analyticAt (sector : ModalSector) (t : ℝ) :
    AnalyticAt ℝ (modalEnergy sector) t := by
  have hamplitudeLine :
      AnalyticAt ℝ (fun x : ℝ => modalAmplitude sector (nativeLine x)) t :=
    analyticAt_comp_nativeLine (modalAmplitude_nativeLine_analyticAt sector t)
  change AnalyticAt ℝ
    (fun x => modalCoefficient sector *
      Complex.normSq (modalAmplitude sector (nativeLine x))) t
  exact analyticAt_const.mul (normSq_analyticAt hamplitudeLine)

/-- Source multiplicity theorem: a native-scalar zero of finite complex order
`m` gives every real modal energy the exact order `2m`. -/
theorem modalEnergy_analyticOrderAt_eq_two_mul
    (sector : ModalSector) (t : ℝ) {order : ℕ}
    (horder : analyticOrderAt nativeScalar (nativeLine t) = (order : ℕ∞)) :
    analyticOrderAt (modalEnergy sector) t = (2 * order : ℕ) := by
  have hamplitudeComplex := modalAmplitude_nativeLine_analyticAt sector t
  have hamplitudeOrder :
      analyticOrderAt (modalAmplitude sector) (nativeLine t) =
        (order : ℕ∞) :=
    (modalAmplitude_nativeLine_analyticOrderAt_eq_nativeScalar sector t).trans horder
  have hamplitudeReal := analyticAt_comp_nativeLine hamplitudeComplex
  have hamplitudeRealOrder :=
    analyticOrderAt_comp_nativeLine_eq hamplitudeComplex hamplitudeOrder
  have hcoefficientNe : modalCoefficient sector ≠ 0 :=
    ne_of_gt (modalCoefficient_pos sector)
  change analyticOrderAt
    (fun x => modalCoefficient sector *
      Complex.normSq (modalAmplitude sector (nativeLine x))) t = _
  exact weightedNormSq_analyticOrderAt_eq_two_mul
      (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => modalCoefficient sector) t)
      hcoefficientNe hamplitudeReal hamplitudeRealOrder

/-- If the native scalar has a zero of finite order `m`, then `m` is positive
and every modal energy has exact real order `2m`. -/
theorem modalEnergy_zero_order_transfer
    (sector : ModalSector) (t : ℝ) {order : ℕ}
    (hzero : nativeScalar (nativeLine t) = 0)
    (horder : analyticOrderAt nativeScalar (nativeLine t) = (order : ℕ∞)) :
    0 < order ∧ analyticOrderAt (modalEnergy sector) t = (2 * order : ℕ) := by
  have hdomain : nativeLine t ∈ nativeScalarDomain := by
    simp [nativeScalarDomain]
    norm_num
  have horderNe : (order : ℕ∞) ≠ 0 := by
    rw [← horder]
    exact (nativeScalar_analyticAt hdomain).analyticOrderAt_ne_zero.mpr hzero
  constructor
  · exact Nat.pos_of_ne_zero (by
      intro hzeroOrder
      subst order
      exact horderNe rfl)
  · exact modalEnergy_analyticOrderAt_eq_two_mul sector t horder

/-- Camera-facing form: a finite positive zero order proved for any supported
camera transfers to the exact real energy order `2m` in every modal sector. -/
theorem modalEnergy_zero_order_of_bracketCharacteristic
    {camera order : ℕ} (hcamera : 2 ≤ camera) (sector : ModalSector) (t : ℝ)
    (hzero : bracketCharacteristic camera (nativeLine t) = 0)
    (horder : analyticOrderAt (bracketCharacteristic camera) (nativeLine t) =
      (order : ℕ∞)) :
    0 < order ∧ analyticOrderAt (modalEnergy sector) t = (2 * order : ℕ) := by
  have hscalarZero : nativeScalar (nativeLine t) = 0 :=
    (bracketCharacteristic_nativeLine_eq_zero_iff hcamera t).mp hzero
  have hscalarOrder :
      analyticOrderAt nativeScalar (nativeLine t) = (order : ℕ∞) := by
    rw [← bracketCharacteristic_nativeLine_analyticOrderAt_eq_nativeScalar
      hcamera t]
    exact horder
  exact modalEnergy_zero_order_transfer sector t hscalarZero hscalarOrder

end

end NativeCarrySpectralWeyl.Camera
