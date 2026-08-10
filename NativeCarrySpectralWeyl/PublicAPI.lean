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
generic self-adjointness, and their exact six-camera forms.  Whitening,
variance, the finite POVM/Cauchy package and operator-valued Weyl layers remain
outside this surface.
-/

namespace NativeCarrySpectralWeyl

end NativeCarrySpectralWeyl
