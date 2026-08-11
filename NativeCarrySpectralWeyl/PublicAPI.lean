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
import NativeCarrySpectralWeyl.Limits.LinearFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarSecondFunctionalMoment
import NativeCarrySpectralWeyl.Limits.QuadraticFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarThirdFunctionalMoment
import NativeCarrySpectralWeyl.Limits.CubicFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarFourthFunctionalMoment
import NativeCarrySpectralWeyl.Limits.QuarticFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarFifthFunctionalMoment
import NativeCarrySpectralWeyl.Limits.QuinticFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarSixthFunctionalMoment
import NativeCarrySpectralWeyl.Limits.SexticFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarSeventhFunctionalMoment
import NativeCarrySpectralWeyl.Limits.SeventhFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.ScalarEighthFunctionalMoment
import NativeCarrySpectralWeyl.Limits.EighthFunctionalCovariance
import NativeCarrySpectralWeyl.Limits.GeneralMomentHierarchy
import NativeCarrySpectralWeyl.Infinite.GramKernel
import NativeCarrySpectralWeyl.Infinite.CameraCompletion

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
    compatible finite colligation family.  For the linear polynomial, the
    zero-mean periodic residue and fixed literal boundary are eliminated, so
    the complete coefficient covariance, direct product and every compatible
    return-metric family converge in matrix norm to the first camera moment,
    with exact six-camera target `sixCameraFirstMoment`.  The scalar second-order
layer proves the exact telescoping identity for the centered logarithmic
numerator and the asymptotic `μ_M(z) - log M → -1` for every fixed nonreal
resolvent parameter.  The first scalar functional-moment layer then proves,
    for every fixed positive natural `ℓ`, the normalized limits
    `sum_(n<ℓM) (log(n+1)-log M)w_z(n)/A_M → ℓ(log ℓ-1)` and
    `sum_(n<ℓM) (log(n+1)-μ_M(z))w_z(n)/A_M → ℓ log ℓ`.  The second
    scalar functional-moment layer uses another exact discrete recurrence to
    prove
    `sum_(n<ℓM) (log(n+1)-μ_M(z))²w_z(n)/A_M → ℓ(1+log(ℓ)²)`.
    The quadratic covariance layer then controls the log-squared periodic
    residue and fixed literal boundary, proving convergence of the complete
    coefficient covariance, direct product and every compatible return-metric
    family to `secondCenteredMomentMatrix`, with exact six-camera target
    `sixCameraSecondCenteredMoment`.
    The third scalar functional-moment layer proves by an exact cubic
    recurrence that
    `sum_(n<ℓM) (log(n+1)-μ_M(z))³w_z(n)/A_M →
    ℓ(log(ℓ)³+3log(ℓ)-2)`.
    Finally, discrete Abel summation controls the unbounded log-cubed
    periodic weight, the centered cubic residue and every fixed literal
    boundary vanish after normalization, and the complete coefficient,
    direct and compatible return-metric covariances converge to
    `thirdCenteredMomentMatrix`, with exact six-camera target
    `sixCameraThirdCenteredMoment`.
    The fourth scalar functional-moment layer continues the exact recurrence
    and proves
    `sum_(n<ℓM) (log(n+1)-μ_M(z))⁴w_z(n)/A_M →
    ℓ(log(ℓ)⁴+6log(ℓ)²-8log(ℓ)+9)`.
    Finally, discrete Abel summation controls the log-fourth periodic weight,
    the centered fourth-power residue and every fixed literal boundary vanish,
    and the complete coefficient, direct and compatible return-metric
    covariances converge to `fourthCenteredMomentMatrix`, with exact
    six-camera target `sixCameraFourthCenteredMoment`.
    The fifth scalar functional-moment layer then proves by the next exact
    recurrence that
    `sum_(n<ℓM) (log(n+1)-μ_M(z))⁵w_z(n)/A_M →
    ℓ(log(ℓ)⁵+10log(ℓ)³-20log(ℓ)²+45log(ℓ)-44)`.
    Finally, discrete Abel summation controls the log-fifth periodic weight.
    The two new mixed terms are closed using
    `μ_M(z)/log(M+1) → 1`, the centered quintic residue and every fixed
    literal boundary vanish, and the complete coefficient, direct and
    compatible return-metric covariances converge to
    `fifthCenteredMomentMatrix`, with exact six-camera target
    `sixCameraFifthCenteredMoment`.
    The sixth scalar functional-moment layer continues the recurrence and
    proves
    `sum_(n<ℓM) (log(n+1)-μ_M(z))⁶w_z(n)/A_M →
    ℓ(log(ℓ)⁶+15log(ℓ)⁴-40log(ℓ)³+135log(ℓ)²-264log(ℓ)+265)`.
    Finally, discrete Abel summation controls the log-sixth periodic weight.
    The three critical mixed terms are closed using
    `μ_M(z)/log(M+1) → 1`; the centered sextic residue and every fixed
    literal boundary vanish, and the complete coefficient, direct and
    compatible return-metric covariances converge to
    `sixthCenteredMomentMatrix`, with exact six-camera target
    `sixCameraSixthCenteredMoment`.
    The seventh scalar functional-moment layer then proves by the next exact
    recurrence that
    `sum_(n<ℓM) (log(n+1)-μ_M(z))⁷w_z(n)/A_M →
    ℓ(log(ℓ)⁷+21log(ℓ)⁵-70log(ℓ)⁴+315log(ℓ)³-
    924log(ℓ)²+1855log(ℓ)-1854)`.
    Finally, discrete Abel summation controls the log-seventh periodic weight.
    The four critical mixed terms are closed using
    `μ_M(z)/log(M+1) → 1`; the centered seventh-power residue and every fixed
    literal boundary vanish, and the complete coefficient, direct and
    compatible return-metric covariances converge to
    `seventhCenteredMomentMatrix`, with exact six-camera target
    `sixCameraSeventhCenteredMoment`.
    The eighth scalar functional-moment layer then continues the exact
    recurrence and proves
    `sum_(n<ℓM) (log(n+1)-μ_M(z))⁸w_z(n)/A_M →
    ℓ(log(ℓ)⁸+28log(ℓ)⁶-112log(ℓ)⁵+630log(ℓ)⁴-
    2464log(ℓ)³+7420log(ℓ)²-14832log(ℓ)+14833)`.
    Finally, discrete Abel summation controls the log-eighth periodic weight.
    The five critical mixed terms are closed using
    `μ_M(z)/log(M+1) → 1`; the centered eighth-power residue and every fixed
    literal boundary vanish, and the complete coefficient, direct and
    compatible return-metric covariances converge to
    `eighthCenteredMomentMatrix`, with exact six-camera target
    `sixCameraEighthCenteredMoment`.
    The general moment hierarchy then defines a single polynomial family
    `P₀ = 1`, `Pₖ = (1+X)ᵏ-kPₖ₋₁`, proves that `Pₖ` is monic of degree `k`,
    and packages every algebraic camera target as
    `G(i,j)Pₖ(log(ell(i,j)))`.  Degrees zero through eight recover the
    previously checked concrete matrices, while cameras `2,...,7` have one
    exact self-adjoint literal matrix in every degree.  This algebraic
    hierarchy does not by itself extend the analytic covariance limits beyond
    degree eight.  Finally, the first all-bases layer defines the countable
    camera index, evaluates each pairwise profile mean over the least common
    multiple of its slopes, proves independence from every larger positive
    common period, and recovers the old periodic Gram matrix on every finite
    principal restriction.  Its exact level/residue sum-of-squares formula,
    including the exceptional positive-definite C2/C4 slope-four block, proves
    every finite principal Gram matrix positive definite and the induced
    `Finsupp` Gram form strictly positive.  Finally, that form equips `c₀₀`
    with its intrinsic real inner product and norm, and its canonical Mathlib
    completion produces the all-bases camera Hilbert space.  The completion
    embedding is isometric with dense range, canonical camera-vector inner
    products recover the Gram kernel, and the compatible finite-label levels
    have dense union.  Kolmogorov/Naimark and operator-valued spectral layers
    remain subsequent obligations.
-/

namespace NativeCarrySpectralWeyl

end NativeCarrySpectralWeyl
