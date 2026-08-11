import GreenFrame
import FiniteNativeCarryOperator
import NativeCarrySpectralWeyl.Camera.NativeLineFloor
import NativeCarrySpectralWeyl.Camera.FiniteCoefficientBridge
import NativeCarrySpectralWeyl.Camera.C2InteriorProfile
import NativeCarrySpectralWeyl.Camera.NaturalInteriorProfile
import NativeCarrySpectralWeyl.Camera.ProfileDirichlet
import NativeCarrySpectralWeyl.Camera.HigherDerivativeTail
import NativeCarrySpectralWeyl.Camera.ZeroMultiplicity
import NativeCarrySpectralWeyl.Camera.ModalEnergy
import NativeCarrySpectralWeyl.Finite.Gram
import NativeCarrySpectralWeyl.Finite.Moments
import NativeCarrySpectralWeyl.Finite.Whitening
import NativeCarrySpectralWeyl.Finite.StepDensity
import NativeCarrySpectralWeyl.Finite.StepPOVM
import NativeCarrySpectralWeyl.Finite.ReturnMetric
import NativeCarrySpectralWeyl.Finite.FunctionalReturnMetric
import NativeCarrySpectralWeyl.Limits.PeriodicMean
import NativeCarrySpectralWeyl.Limits.CameraCovariance
import NativeCarrySpectralWeyl.Limits.ResolventWeight
import NativeCarrySpectralWeyl.Limits.FiniteDefectCovariance
import NativeCarrySpectralWeyl.Limits.ResolventLogMean
import NativeCarrySpectralWeyl.Limits.ScalarFunctionalMoment
import NativeCarrySpectralWeyl.Limits.FiniteFunctionalCovariance

/-!
# Native Carry Spectral Weyl public API

Public import surface for the spectral/Weyl layer.  It exports the exact
periodic profiles and finite-camera coefficient bridge, explicit factors and
their uniform native-line floor, normally convergent bracket characteristics
on `re s > -1`, their initial profile/zeta factorization on `re s > 1`, the
analytically continued cross-factor identity, and the common native-line zero
set of every supported camera.  It also exports the explicit
`O(M⁻³ᐟ²)` cutoff and stable cross-residual estimates, plus every fixed-order
native-line derivative rate `O(M⁻³ᐟ² log(M)^k)`, and equality of analytic zero
multiplicities between all supported cameras on the native line.  It also
exports the five limiting modal energies, their positive scalar weights and
common zero set, and the exact doubling from complex amplitude order `m` to
real energy order `2m`.  The finite spectral surface includes periodic product
means, the slope-weighted Gram kernel, finite-family positive semidefiniteness,
and the exact positive-definite Gram matrix for cameras `2, ..., 7`.  It also
exports the first and second centered logarithmic moment matrices, their
generic self-adjointness, and their exact six-camera forms.  The whitening
surface constructs the canonical positive inverse square root, proves exact
Gram normalization, defines the whitened moments and variance, and identifies
variance positivity with the moment-block Schur condition.  The continuous
step-density layer proves that condition from an integral Gram representation,
recovers the exact moment block by a Schur product with the periodic profile
mean, and proves the concrete six-camera variance positive semidefinite.  The
finite POVM layer realizes the positive step density as a vector measure,
proves total mass `G`, normalizes it by congruence with `G⁻¹/²`, and pushes it
to the centered-log spectral coordinate; the canonical six-camera POVM has
positive effects and total effect `I`.  Its Cauchy transform and the
operator-valued Weyl layers remain outside this surface.  The Phase 4 limit
layer proves vector-valued periodic Cesàro convergence and Dirichlet--Abel
weighted periodic means, including weights that become antitone after a
finite prefix.  For the concrete weight `|z - log(n+1)|⁻²`, it proves
positivity, decay, eventual monotonicity, divergent mass,
`A_M(z) ~ M / log(M+1)^2`, and `A_(L M)(z) / A_M(z) → L`.  Consequently the
genuine slope-scaled cutoff covariance converges in finite-matrix norm to the
camera Gram, with the exact six-camera limit `sixCameraGram`.  Finally, the
literal finite camera stencils—including the corrected even endpoint—are
realized as a common-window camera matrix.  The endpoint return metric cancels
exactly under `P E = B` and `Eᴴ E + Bᴴ B = I`, and the resulting normalized
finite defect covariance converges in matrix norm to the exact six-camera
Gram.  The functional extension inserts an arbitrary spectral observable in
one probe leg, proves exact return-metric cancellation to the complete literal
coefficient sum, and specializes this identity to every real polynomial in
the finite centered logarithmic coordinate.  Any limit of those coefficient
sums transfers automatically to both the direct matrix product and every
compatible finite colligation family; proving the polynomial coefficient-sum
limit itself remains the next analytic obligation.  The scalar second-order
layer proves the exact telescoping identity for the centered logarithmic
numerator and the asymptotic `μ_M(z) - log M → -1` for every fixed nonreal
resolvent parameter.  The first scalar functional-moment layer then proves,
for every fixed positive natural `ℓ`, the normalized limits
`sum_(n<ℓM) (log(n+1)-log M)w_z(n)/A_M → ℓ(log ℓ-1)` and
`sum_(n<ℓM) (log(n+1)-μ_M(z))w_z(n)/A_M → ℓ log ℓ`.
-/

namespace NativeCarrySpectralWeyl

end NativeCarrySpectralWeyl
