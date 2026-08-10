# Native Carry Spectral Weyl

Lean 4 formalization of the spectral/Weyl layer associated with the native
carry cameras.

## Current status

The v0.17 resolvent-weight-limit milestone contains **404 public kernel-checked Lean
theorems**.  It builds against the exact Green Frame v2.1 commit and the exact
finite native-carry operator commit.  The current public surface proves:

- the bridge from spectral slope/radius counts to the pinned finite-camera
  geometry;
- exact aligned-C2, odd and even periodic coefficient profiles;
- exact periodicity and zero coefficient mean over one camera period;
- the explicit complex factors `A_b(s)` and the native line `s = 1/2 + i t`;
- a simultaneous positive lower bound for every `b >= 2`, hence
  `A_b(1/2 + i t) != 0`;
- a free integer stencil whose scalar coefficients are literal and whose
  evaluation is exactly the pinned `finiteNativeOperator`;
- the complete aligned-C2 formula: finite coefficients equal `c2Profile` on
  `1 <= n <= 4 * cutoff + 1` and vanish outside that window.
- the complete odd natural-camera formula: finite coefficients equal
  `oddProfile` on the full emitted window;
- the complete even natural-camera formula: finite coefficients equal
  `evenProfile` on the strict interior, while the final antipodal coefficient
  is exactly `1 = 2 - 1`, with the correction stated explicitly in Lean.
- absolute summability of every supported periodic-profile Dirichlet series
  on `1 < re s`, and the exact identity
  `profileDirichletSeries b s = factor b s * riemannZeta s` there.
- literal finite and infinite bracket characteristics from the aligned camera
  geometry, with absolute summability for `-1 < re s`;
- normal convergence on compact subsets of `-1 < re s`, locally uniform
  convergence of finite cutoffs, and holomorphy of every limit characteristic;
- exact complex evaluation of the free finite stencil as C2, odd and even
  profile Dirichlet prefixes, including the final even antipodal correction;
- equality of the bracket characteristic with the profile series, hence with
  `factor b s * riemannZeta s`, on the common half-plane `1 < re s`;
- analytic continuation of the cross-factor identity
  `factor 3 s * chi_b(s) = factor b s * chi_3(s)` to `-1 < re s`;
- a holomorphic native scalar `chi_3 / factor 3` on `-1 < re s < 1`, through
  which every supported camera factors, and the common zero set of every
  camera characteristic on `s = 1/2 + i t`.
- the literal `M`-block cutoff identity and explicit native-line remainder
  `O(M^(-3/2))`, obtained from the centered-block `m^(-5/2)` majorant;
- the numerically stable cross residual
  `factor 3 * chi_(b,M) - factor b * chi_(3,M) = O(M^(-3/2))`, without
  division near a common zero;
- termwise differentiation of the centered bracket series and the explicit
  first-derivative estimate
  `C(b,t) * ((2/3) * log M + 10/9) * M^(-3/2)`;
- the source-form native-line parameter result
  `d/dt (chi_b(1/2 + it) - chi_(b,M)(1/2 + it)) =
  O(M^(-3/2) * log M)`.
- the general off-line tail estimate on `re s > -1` and its uniform form on a
  Cauchy circle of radius `1 / log M` around the native line;
- Cauchy's estimate for every fixed complex derivative order `k`, yielding
  `O(M^(-3/2) * log(M)^k)` without expanding higher differentiated summands;
- the exact chain rule along `s = 1/2 + it`, where the `k`-th real derivative
  is the `k`-th complex derivative multiplied by `I^k`, and hence the same
  `O(M^(-3/2) * log(M)^k)` rate for the actual `t` derivative.
- the analytic local-unit statement `ord_s A_b = 0` whenever the camera factor
  is nonzero at `s`, together with equality of germs
  `chi_b = A_b * Z_nat` on the native-scalar strip;
- equality of `analyticOrderAt` for every pair of supported camera
  characteristics at every native-line point, including exact transfer of any
  finite positive zero order.
- the five limiting modal sectors `3`, `4`, `5`, `7` and mixed, with the
  rank-two `log 4` sector represented by its canonical aggregate carrying
  `1 - 2^(1-s)`, and the mixed amplitude carrying its product with `A_3`;
- strictly positive real-analytic modal weights, nonnegative real-analytic
  energies, the exact factorization
  `E_j(t) = Q_j(t) * normSq(Z_nat(1/2 + i t))`, and their common zero set;
- the real/complex analytic bridge proving that a finite amplitude zero of
  complex order `m` gives every modal energy exact real order `2m`.
- periodic product means over a chosen common camera period, realized as
  normalized sums of rank-one matrices and therefore positive semidefinite;
- the positive-semidefinite slope-minimum kernel and, by the Schur product
  theorem, the positive-semidefinite weighted Gram matrix for every finite
  camera family;
- the exact period-`420` Gram matrix for cameras `2,...,7`, including its
  integer profile-product certificate, determinant `4_981_760`, and strict
  positive definiteness.
- a generic slope-weighted moment construction whose real matrices are
  Hermitian and self-adjoint for every finite camera package;
- the exact first centered logarithmic moment
  `H_bc = G_bc * log(min(ell_b,ell_c))` and second centered moment
  `J_bc = G_bc * (1 + log(min(ell_b,ell_c))^2)`;
- literal recovery and self-adjointness of both documented moment matrices for
  cameras `2,...,7` at common period `420`.
- the canonical positive inverse square root `R = (sqrt G)⁻¹ = sqrt(G⁻¹)` for
  every positive-definite finite Gram matrix, including positivity,
  Hermitianity and self-adjointness;
- the exact identities `R * R = G⁻¹` and `R * G * R = I`, together with
  preservation of Hermitianity and positive semidefiniteness under whitening;
- the whitened operators `L = R H R`, `M₂ = R J R` and `V = M₂ - L²`, with
  the exact Schur identity `V = R (J - H G⁻¹ H) R`;
- equivalence between positivity of the Hermitian moment block
  `[[G,H],[H,J]]` and its Schur complement, hence positivity of `V` under that
  kernel-checked hypothesis;
- the canonical six-camera inverse square root, logarithmic operator, second
  moment and variance, recovered from the period-`420` source constructions
  and proved self-adjoint where applicable.
- the endpoint-sensitive identities
  `integral 0..ell (1 + log x) = ell * log ell` and
  `integral 0..ell (1 + log x)^2 = ell * (1 + log(ell)^2)`;
- the full two-level slope moment block as an integral Gram matrix of the
  truncated features `1` and `1 + log x`, hence positive semidefinite;
- exact factorization of `[[G,H],[H,J]]` as the Hadamard product of that step
  Gram block with the repeated periodic product-mean block;
- unconditional positive semidefiniteness of the exact period-`420`
  six-camera moment block and canonical variance operator.
- the pointwise positive continuous step density
  `dΣ(x) = D(x) M₀ D(x) dx`, its Bochner integrability, positivity on every
  measurable set and exact total mass `Σ(ℝ) = G`;
- normalization by the continuous congruence
  `A ↦ G⁻¹/² A G⁻¹/²`, giving a finite matrix-valued POVM with total effect
  `E(ℝ) = I` for every positive-definite camera Gram matrix;
- pushforward by the centered-log coordinate `y = 1 + log x`, with the
  canonical period-`420` six-camera spectral POVM proved positive and
  normalized.
- exact block/remainder formulas for periodic vector-valued prefix sums,
  uniform boundedness of centered prefixes and convergence of ordinary
  Cesàro means to the one-period average;
- a Dirichlet--Abel weighted periodic-mean theorem for antitone weights that
  tend to zero and have divergent total mass;
- finite-prefix stability of that theorem, so eventual antitonicity is enough;
- an explicit `HasAsymptoticallyLinearMass` interface isolating the scalar
  regular-variation input `A_(L M) / A_M -> L` from camera arithmetic;
- entrywise and finite-matrix norm convergence of the genuine pairwise cutoff
  covariance, whose `(b,c)` entry runs to
  `min(ell_b,ell_c) * M`, to the periodic camera Gram matrix under those
  weight hypotheses;
- specialization of that norm limit to cameras `2,...,7`, with target exactly
  the documented positive-definite matrix `sixCameraGram`.
- the concrete resolvent weight
  `resolventWeight z n = |z - log(n+1)|^-2`, with positivity for nonreal `z`,
  decay to zero, eventual antitonicity and divergent partial mass;
- the scalar asymptotics
  `A_M(z) ~ M / log(M+1)^2` and `A_(L M)(z) / A_M(z) -> L` for every fixed
  positive natural `L`;
- direct finite-matrix norm convergence of the concrete resolvent-weighted
  pairwise cutoff covariance to the periodic Gram matrix, including cameras
  `2,...,7` converging to the exact matrix `sixCameraGram`.

The scalar regular-variation obligation left open in v0.16 is now discharged,
and the abstract periodic covariance theorem is instantiated by the concrete
resolvent weight.  Identifying this periodic-profile covariance with every
literal finite defect-probe formula still requires the documented finite
seed/endpoint bridge and exact return-metric cancellation.  The finite
normalized POVM is not upgraded to a projection-valued measure, and its
Cauchy transform and the operator-valued Weyl family remain separate
obligations.  No Parseval or Poisson statement is used to infer these new
spectral limits.

Pinned foundations:

- Lean `4.32.0`;
- Mathlib `v4.32.0`, inherited through the pinned dependencies;
- Green Frame commit `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`
  (`v2.1.0`);
- Finite Native Carry Operator commit
  `00e9d6beb17226545abf5ddf90bbfede6c7146b0` (`v0.1.0`).

## Intended theorem boundary

The formalization will proceed from exact camera arithmetic to finite spectral
objects, then to the countable camera completion, Cauchy transform and an
unbounded Weyl inverse.  Boundary relations and the coupling to the Green
state/port layer come only after their domain and maximality statements are
proved independently.

Three parameters remain permanently distinct:

```text
t       angular parameter of the native orbit
z0      auxiliary non-real defect-probe anchor
lambda  spectral parameter of the Cauchy/Weyl family
```

No equality among them is assumed.  The project does not infer a zeta theorem,
the Riemann hypothesis, a primality criterion, or a zero-selection law from the
existence of a Weyl family.

## Repository map

- `NativeCarrySpectralWeyl/`: Lean source and public import surface;
- `docs/00_SCOPE.md`: semantic and trust boundary;
- `docs/10_FORMALIZATION_PLAN.md`: dependency-ordered implementation plan;
- `research/SOURCE_CATALOG.md`: source inventory and provenance findings;
- `audit/theorem-registry.json`: ordered registry of all 404 public theorems;
- `audit/claim-ledger.json`: exact theorem-to-claim mapping;
- `NativeCarrySpectralWeyl/Audit.lean`: one `#print axioms` report per theorem;
- `.github/workflows/lean-audit.yml`: exact-checkout Lean audit.

## Build

```bash
lake update
lake build --wfail NativeCarrySpectralWeyl
```

The theorem registry and claim ledger are active.  A release tag is created
only after the exact candidate SHA passes the remote audit on `main`.
