# Formalization plan

## 1. Audit findings

The GitHub repository began at commit
`39cb245d0b612c4cd213a664a8b7730660254aa9` with only `LICENSE`.

The local research directory `carry-lab/Wayl` contains 67 source files (about
1.5 MB):

- 27 Markdown derivations;
- 18 Python laboratories;
- 22 JSON ledgers.

The source set is not yet a release-grade corpus:

- five exact duplicate families were found;
- `three_color_creation_operator_audit.json` originally had a trailing `t`;
  the compact ledger was corrected and a separate full ledger was regenerated
  by its script with every assertion enabled;
- several laboratories import historical `carry-lab` scripts rather than
  self-contained local modules;
- `native_carry_camera_second_centered_moment_lab.py` was initially absent, then
  recovered from `/tmp`, syntax-checked and copied into `carry-lab/Wayl` with
  SHA-256 `d13feb6c04ff58d8660f85a5547d901c33ed091c8d6d31d879278382c95c2f9c`;
- `native_carry_primitive_real_operator_all_bases_fixed.py` was supplied at the
  `carry-lab` root, matched the primitive SHA recorded in the common-zero JSON,
  and was moved byte-for-byte into `carry-lab/Wayl` with SHA-256
  `c68d4bb274f36eb4dc5572afe64394787876f64bc8f2e50573654f2ab712ecee`;
- the `carry-lab` worktree is heavily dirty and `Wayl/` itself is untracked.

Therefore sources must be copied by an explicit manifest and SHA-256, without
mutating or treating the dirty worktree as authoritative.

Mathlib 4.32 has useful infrastructure for bounded operators, Hilbert-space
completions, Bochner integration and partially defined linear maps
(`LinearPMap`).  It does not expose a ready-made POVM/boundary-relation API
matching the notes.  Those abstractions must be introduced minimally and only
when their theorem obligations are clear.

## 2. Dependency graph

```text
finite camera geometry
        |
        v
periodic profiles and camera factors
        |
        +----------------------+
        |                      |
        v                      v
common-zero analytic bridge   periodic mean kernel
                               |
                               v
                         finite Gram/moments
                               |
                         finite POVM/Cauchy
                               |
                               v
                 all-bases Gram completion
                               |
                     explicit Naimark isometry
                               |
                  bounded Cauchy compression
                               |
                  closed unbounded Weyl inverse
                               |
            boundary relation / gamma-field layer
                               |
                  Green state-port coupling
```

The holonomic tau, Painlevé and three-color creation algebra form a separate
downstream track.  They are not prerequisites for the spectral/Weyl core.

## 3. Phase 0 — audit foundation

Deliverables:

- preserve a canonical, deduplicated source bundle with exact hashes;
- record missing dependencies rather than silently reconstructing them;
- introduce JSON and Markdown claim ledgers;
- add an ordered public theorem registry and `#print axioms` file once the
  first theorem exists;
- port the Green seven-gate audit with project-specific counts and source
  hashes.

Exit criterion: an exact clean SHA can prove that the theorem count is zero and
that no research source is being presented as kernel evidence.

## 4. Phase 1 — native camera arithmetic

### Milestone progress

Kernel checked in the first camera-arithmetic candidate:

- exact supported-camera slope and radius-count bridge to
  `FiniteNativeCarryOperator`;
- aligned C2, odd natural and even natural profile formulas;
- exact periodicity and mean zero over one spectral period;
- explicit `A_b(s)` definitions for all three camera classes;
- exact complex-power norms on `s = 1/2 + i t`;
- the uniform positive all-camera floor and nonvanishing theorem.

Added in the v0.2 finite-coefficient milestone:

- a free integer stencil for atoms, centered brackets, seed blocks, center
  blocks and finite camera cutoffs;
- literal scalar coefficient formulas and cutoff recurrences;
- exact evaluation theorems identifying every formal block, and the whole
  stencil, with the pinned real-plane finite operator.

Added in the v0.3 aligned-C2 milestone:

- a complete coefficient formula at every natural position and cutoff;
- equality with `c2Profile` throughout `1 <= n <= 4 * cutoff + 1`;
- exact vanishing outside the emitted C2 window.

Added in the v0.4 natural-camera milestone:

- generic interval-counting formulas for every odd and even natural-camera
  seed and aligned center block;
- equality with `oddProfile` throughout the complete odd emitted window;
- equality with `evenProfile` throughout the strict even interior;
- the exact final even antipodal correction: the finite coefficient is `1`,
  the periodic value is `2`, and the corrected window formula subtracts one
  unit only at that endpoint;
- a unified natural-camera theorem on the common strict interior window.

Added in the v0.5 profile-Dirichlet milestone:

- exact reindexing of a divisibility-indicator series onto positive multiples;
- absolute summability of the aligned C2, odd, even and unified profile series
  throughout `1 < re s`;
- exact factorization of all three profile classes by the explicit factors
  already defined in `Camera/Factors.lean`;
- the unified identity
  `profileDirichletSeries b s = factor b s * riemannZeta s` in the absolutely
  convergent half-plane;
- an explicit firewall separating this result from bracket-series normal
  convergence, analytic continuation and common-zero claims.

Closed in v0.6: the alternate closed form
`(sqrt 2 - 1)^2 / sqrt 2` for the universal constant is now kernel checked.

Suggested modules:

```text
NativeCarrySpectralWeyl/Camera/Geometry.lean
NativeCarrySpectralWeyl/Camera/Profile.lean
NativeCarrySpectralWeyl/Camera/PeriodicMean.lean
NativeCarrySpectralWeyl/Camera/Factor.lean
NativeCarrySpectralWeyl/Camera/NativeLineFloor.lean
```

Theorem ladder:

1. define the aligned `C2` camera and natural saturated cameras `b >= 3`;
2. express profiles by divisibility indicators:

   ```text
   a2(n)     = 1 - 1_[2|n] - 2 * 1_[4|n]
   a_odd(n)  = 1 - b * 1_[b|n]
   a_even(n) = 1 + 1_[b/2|n] - (b+2) * 1_[b|n]
   ```

3. prove exact periodic mean zero;
4. prove the finite coefficient/profile bridge to
   `FiniteNativeCarryOperator`;
5. define the explicit complex factors `A_b(s)`;
6. prove, for `s = 1/2 + it`, the uniform floor
   `‖A_b(s)‖ >= ((sqrt 2 - 1)^2 / sqrt 2) > 0`.

This phase is mostly finite arithmetic and elementary complex inequalities.  It
should be the first release because it is independent of unbounded-operator
infrastructure.

## 5. Phase 2 — analytic camera bridge

Suggested modules:

```text
NativeCarrySpectralWeyl/Camera/BracketSeries.lean
NativeCarrySpectralWeyl/Camera/NormalConvergence.lean
NativeCarrySpectralWeyl/Camera/BracketProfileBridge.lean
NativeCarrySpectralWeyl/Camera/BracketProfileFactorization.lean
NativeCarrySpectralWeyl/Camera/CrossFactorization.lean
NativeCarrySpectralWeyl/Camera/CommonZeroSet.lean
NativeCarrySpectralWeyl/Camera/QuantitativeTail.lean
NativeCarrySpectralWeyl/Camera/DerivativeTail.lean
NativeCarrySpectralWeyl/Camera/HigherDerivativeTail.lean
NativeCarrySpectralWeyl/Camera/ZeroMultiplicity.lean
NativeCarrySpectralWeyl/Camera/ModalEnergy.lean
```

Kernel checked in the v0.6 analytic-camera milestone:

- a quantitative second-derivative bound for centered differences;
- pointwise absolute and compact-normal convergence on `re s > -1`;
- locally uniform cutoff convergence and holomorphy of the bracket limits;
- exact complex finite-stencil/profile-prefix formulas for C2, odd and even
  cameras, including the even endpoint correction;
- bracket/profile/factor-zeta equality on `re s > 1`;
- the cross-factor identity on `re s > 1` and its extension to `re s > -1` by
  the holomorphic identity theorem;
- native-scalar recovery through camera 3 on `-1 < re s < 1`;
- common zero sets of all supported camera characteristics on the native line.

Kernel checked in the v0.7 quantitative-tail milestone:

- the cutoff is literally the number `M` of aligned center blocks in
  `finiteBracketCharacteristic`;
- every native-line center block is bounded by an explicit multiple of
  `(m+1)^(-5/2)`, and the shifted integral test gives the exact exponent drop
  `5/2 -> 3/2`;
- each supported characteristic has an explicit `O(M^(-3/2))` cutoff tail;
- the stable finite-camera cross residual has the same `O(M^(-3/2))` rate,
  stated without division by a factor near a common zero;
- differentiation in the complex exponent preserves the centered cancellation
  and adds one logarithmic weight;
- the differentiated series is summable and equals the derivative of the
  infinite characteristic on the native line;
- both the complex-exponent derivative and the actual derivative in
  `t` along `s = 1/2 + it` satisfy the explicit bound
  `C(b,t) * ((2/3) log M + 10/9) * M^(-3/2)`, hence
  `O(M^(-3/2) log M)`.

Kernel checked in the v0.8 higher-derivative-tail milestone:

- a general integral-test tail bound for every shifted real power with
  exponent below `-1`;
- an explicit order-zero cutoff estimate throughout the bracket half-plane,
  uniform on a complex circle around `s = 1/2 + it`;
- the dynamic Cauchy radius `1 / log M`, which keeps that circle inside the
  holomorphy domain and turns the order-zero rate into
  `O(M^(-3/2) log(M)^k)` for every fixed complex derivative order `k`;
- an exact all-orders chain rule along the native line, multiplying the
  complex derivative by `I^k` and therefore preserving the norm;
- the source-form actual `t`-derivative remainder
  `O(M^(-3/2) log(M)^k)` for every fixed order `k`.

Kernel checked in the v0.9 zero-multiplicity milestone:

- a nonvanishing supported camera factor has `analyticOrderAt = 0`, the precise
  local-unit statement used in the source notes;
- the strip factorization `chi_b = A_b * Z_nat` holds as an equality of
  analytic germs at every point of the native-scalar domain;
- multiplication by the local camera unit preserves `analyticOrderAt`;
- every pair of supported camera characteristics has the same analytic order
  at every native-line point;
- if one characteristic has a finite zero of order `m`, then `m > 0` and every
  other supported characteristic has exactly the same order `m`.

This closes the scalar analytic obligations identified in Phase 2.

Kernel checked in the v0.10 modal-energy milestone:

- the five limiting sectors `3`, `4`, `5`, `7` and mixed, with exact
  coefficients and holomorphic factors from the source formulas;
- the canonical rank-two mode-4 aggregate through the binary defect factor
  `1 - 2^(1-s)`, and the mixed sector through its product with `A_3`;
- strictly positive real-analytic weights and nonnegative real-analytic modal
  energies satisfying `E_j(t) = Q_j(t) * normSq(Z_nat(1/2 + i t))`;
- a proved bridge from complex holomorphic order to real analytic order along
  the native line, whose complex-affine parametrization has derivative `I`;
- exact order doubling under `Complex.normSq` and preservation under a
  nonzero real-analytic weight;
- common modal-energy zero sets and the source statement that a camera zero
  of finite complex order `m` gives every limiting modal energy exact real
  order `2m`.

This closes the multiplicity-and-transverse-opening statement in section 10
of the dynamic sector-limit notes.  It does not construct the finite spectral
projectors used in the numerical gate; those begin in Phase 3.

The quantitative tail theorems are explicit consequences of the centered
block majorants and integral tests; they are not inferred from pointwise
convergence alone.

## 6. Phase 3 — finite camera spectral package

Kernel checked in the v0.11 finite-Gram milestone:

- a common-period predicate and invariance of every supported camera profile
  under a period divisible by its exact spectral slope;
- the periodic product-mean matrix as a normalized finite sum of rank-one
  profile matrices, hence positive semidefinite;
- the slope-minimum kernel as a finite sum of rank-one level indicators, hence
  positive semidefinite for every finite slope family;
- the weighted Gram formula
  `G(b,c) = min(ell_b,ell_c) * m(b,c)` and its positive semidefiniteness by the
  Schur product theorem;
- the exact common period `420` and integer product-sum certificate for cameras
  `2,...,7`;
- literal recovery of the documented rational Gram matrix, its exact
  determinant `4_981_760`, and strict positive definiteness.

This closed the Gram portion of Phase 3 at v0.11.  Moment matrices are the next
layer; whitening, the step POVM and its Cauchy/Weyl transforms remain later
milestones.

Kernel checked in the v0.12 finite-moments milestone:

- a generic real shared-slope weight matrix and its Hermitian proof;
- a generic weighted-moment construction over the periodic Gram, Hermitian and
  self-adjoint for every finite camera package;
- the exact source formulas
  `H(b,c) = G(b,c) * log(min(ell_b,ell_c))` and
  `J(b,c) = G(b,c) * (1 + log(min(ell_b,ell_c))^2)`;
- Hermitian and self-adjoint first and second centered logarithmic moments;
- literal recovery of both documented period-`420` matrices for cameras
  `2,...,7`, together with their self-adjointness.

This closes the unwhitened moment portion of Phase 3.  The positive inverse
square root, the whitened logarithmic operator, the variance Schur complement
and the step POVM remain subsequent milestones.

Kernel checked in the v0.13 finite-whitening milestone:

- the canonical positive inverse square root
  `R = (CFC.sqrt G)⁻¹ = CFC.sqrt(G⁻¹)` for every positive-definite finite Gram
  matrix;
- positive definiteness, Hermitianity and self-adjointness of `R`;
- the exact inverse-square and normalization identities
  `R² = G⁻¹` and `R G R = I`;
- congruence whitening and preservation of Hermitianity, self-adjointness and
  positive semidefiniteness;
- the whitened first and second moments `L = R H R` and `M₂ = R J R`;
- the variance `V = M₂ - L²` and its exact identity
  `V = R (J - H G⁻¹ H) R`;
- equivalence between positivity of the Hermitian block `[[G,H],[H,J]]` and
  positivity of its Schur complement, yielding a reusable conditional
  positivity theorem for `V`;
- canonical instantiation of `R`, `L`, `M₂` and `V` for cameras `2,...,7`,
  including exact recovery from the period-`420` constructions and
  self-adjointness.

This closed the algebraic whitening portion of Phase 3.  At that milestone,
the next obligation was to realize the moment block as a positive continuous
step-density integral, discharging the remaining hypothesis for concrete
variance positivity and providing the normalization input for the step POVM.

Kernel checked in the v0.14 step-density milestone:

- right-endpoint control of `x * log(x)^2` at zero and the exact identities
  `integral 0..ell (1 + log x) = ell log ell` and
  `integral 0..ell (1 + log x)^2 = ell (1 + log(ell)^2)`;
- a general finite interval-Gram matrix and its positive-semidefinite proof by
  rewriting every quadratic form as the integral of a square;
- the two-level truncated slope features `1` and `1 + log x`, their exact
  Gram entries and positivity;
- the repeated periodic product-mean block as a normalized sum of rank-one
  matrices;
- exact Hadamard factorization of the documented moment block
  `[[G,H],[H,J]]` into the two positive-semidefinite factors;
- unconditional positive semidefiniteness of the period-`420` six-camera
  moment block and variance operator.

This closes the moment-block positivity obligation.  The next Phase 3
milestone is normalization of the step density into a finite POVM, followed
by its Cauchy transform and finite Weyl family.

Kernel checked in the v0.15 finite-POVM milestone:

- the step cutoff `1_{(0,ell]}` and pointwise positive density
  `D(x) M₀ D(x)` for every finite camera family;
- Bochner integrability of the pair-indexed matrix coordinates and the exact
  total-density identity `∫ D(x) M₀ D(x) dx = G`;
- positivity of the unnormalized vector measure on every measurable set and
  exact total mass `Σ(ℝ) = G`;
- continuity of matrix congruence and normalization by the canonical positive
  inverse square root, giving `E(ℝ) = I` whenever `G` is positive definite;
- a reusable finite matrix-POVM structure and measurable pushforward;
- pushforward under the centered-log coordinate `y = 1 + log x` and concrete
  positivity/normalization of the period-`420` six-camera POVM.

This closes the finite measure-normalization portion of Phase 3.  The next
milestone is its finite Cauchy transform, including analyticity, the Herglotz
sign identity and the first two centered-log moment recoveries.  Projection
effects are not assumed: the constructed object is a POVM, not a PVM.

Suggested modules:

```text
NativeCarrySpectralWeyl/Finite/Gram.lean
NativeCarrySpectralWeyl/Finite/Moments.lean
NativeCarrySpectralWeyl/Finite/Whitening.lean
NativeCarrySpectralWeyl/Finite/StepDensity.lean
NativeCarrySpectralWeyl/Finite/StepPOVM.lean
NativeCarrySpectralWeyl/Finite/Cauchy.lean
NativeCarrySpectralWeyl/Finite/Weyl.lean
```

Core results:

- for a finite camera set, define
  `m(b,c) = mean (a_b * a_c)` using a common period;
- prove positive semidefiniteness as an average of squared absolute values;
- define `G(b,c) = min(ell_b,ell_c) * m(b,c)`;
- prove the exact `2,...,7` Gram matrix is positive definite;
- construct the first and second moment matrices and their self-adjointness;
- formalize whitening by the positive inverse square root;
- define the finite step-density operator measure and prove normalization;
- define its Cauchy transform by the integral representation;
- prove the anti-Herglotz identity, injectivity and invertibility in finite
  dimension.

The exponential-integral `E1` closed form is optional.  The integral formula is
the authoritative definition and is sufficient for the operator theory.

## 7. Phase 4 — defect probes and functional limits

This phase connects the camera package to the Green/state layer without
identifying static Poisson with spectral Weyl.

Kernel checked through the v0.37 general moment-hierarchy milestone:

- exact complete-block plus remainder decomposition for periodic
  vector-valued sums and a uniform norm bound for zero-mean prefixes;
- ordinary Cesàro convergence to the one-period mean in every real normed
  vector space;
- a Dirichlet--Abel weighted periodic-mean theorem under the explicit
  hypotheses that the weight is antitone, tends to zero and has divergent
  partial mass;
- the predicate `HasAsymptoticallyLinearMass`, which isolates precisely the
  remaining scalar input `A_(L M) / A_M -> L`;
- convergence of the genuine camera covariance with pairwise cutoff
  `min(ell_i,ell_j) M` to the periodic Gram matrix, both entrywise and in the
  finite entry-sup matrix norm;
- specialization to cameras `2,...,7`, with limit exactly the documented
  positive-definite matrix `sixCameraGram`.
- finite-prefix stability of the Dirichlet--Abel theorem, permitting weights
  that are only eventually antitone;
- the concrete zero-indexed form
  `w_z(n) = |z - log(n+1)|^-2`, with positivity for `Im z != 0`, decay,
  eventual antitonicity and divergent mass;
- the exact asymptotic package `A_M(z) ~ M/log(M+1)^2` and
  `A_(L M)(z)/A_M(z) -> L` for fixed positive natural `L`;
- matrix-norm convergence of the concrete resolvent-weighted pairwise cutoff
  covariance, including the exact six-camera Gram limit.
- exact finite return-metric cancellation: `P E = B` and
  `Eᴴ E + Bᴴ B = I` imply `Eᴴ (I + PᴴP) E = I` and therefore
  `S (I + PᴴP) Sᴴ = C R Rᴴ Cᴴ` for `S = C R Eᴴ`;
- exact common-window realization of every literal finite camera coefficient,
  including finite seeds, zero support beyond the emitted window and the
  corrected final even-camera endpoint;
- exact equality between the normalized finite camera/resolvent matrix product
  and the literal coefficient covariance;
- decomposition into a shifted periodic core plus a uniformly finite boundary
  sum, followed by vanishing of that boundary for the concrete resolvent;
- matrix-norm convergence of the literal finite covariance, the direct matrix
  product and every cutoff-indexed compatible finite colligation family;
- specialization to cameras `2,...,7`, with target the exact complexification
  of `sixCameraGram`.
- insertion of an arbitrary spectral observable in one defect-probe leg and
  exact cancellation of the return-metric cross covariance to the direct
  observable-resolvent covariance;
- exact equality of the normalized functional matrix product with the complete
  literal finite coefficient sum for every real multiplier;
- specialization to every real polynomial in
  `log(n+1) - μ_M(z)`, with the finite resolvent-weighted logarithmic center
  `μ_M(z)` defined explicitly and the constant polynomial proved to recover
  the order-zero covariance;
- convergence-transfer theorems reducing both the direct functional matrix
  product and every compatible return-metric colligation family to the same
  literal coefficient-sum limit.
- the exact telescoping identity for the centered logarithmic numerator and
  the asymptotic `μ_M(z) - log M -> -1`, obtained from
  `A_M(z)/(M w_z(M)) -> 1`, `M(log(M+1)-log M) -> 1` and summation of a
  little-o increment.
- fixed-displacement endpoint asymptotics for every positive natural `ell`
  and fixed `r`: `w_z(ell*M+r)/w_z(M) -> 1` and
  `log(ell*M+r+1)-log(M+1) -> log ell`;
- an exact discrete increment for the first scalar logarithmic moment below
  `ell*M`, with the little-o summation limits
  `A_M^-1 sum_(n<ell*M) (log(n+1)-log M)w_z(n) -> ell(log ell-1)` and
  `A_M^-1 sum_(n<ell*M) (log(n+1)-μ_M(z))w_z(n) -> ell log ell`;
- eventual antitonicity and decay of `log(n+1)w_z(n)`, and boundedness of its
  Dirichlet prefixes against every zero-mean periodic residue;
- elimination of the centered linear periodic residue and every fixed-width
  literal seed/endpoint boundary after normalization by `A_M`;
- entrywise and finite-matrix norm convergence of the complete centered-linear
  coefficient covariance to `firstMomentMatrix`, including the exact target
  `sixCameraFirstMoment` for cameras `2,...,7`;
- transfer of the same first-moment limit to the direct functional matrix
  product and every compatible return-metric colligation family;
- the exact quadratic increment below `ell*M`, split into a squared boundary
  block, the first logarithmic moment and a negligible squared
  change-of-center correction;
- little-o summation of that increment, giving the raw second scalar limit
  `ell(log(ell)^2-2log(ell)+2)` and the weighted-mean-centered limit
  `ell(1+log(ell)^2)`.
- eventual tail monotonicity in one of the two directions for the
  log-squared resolvent weight, and bounded Dirichlet sums against every
  zero-mean periodic residue;
- elimination of the centered quadratic periodic residue and every
  fixed-width literal boundary term;
- entrywise and finite-matrix norm convergence of the complete
  centered-quadratic coefficient covariance to `secondCenteredMomentMatrix`,
  with exact target `sixCameraSecondCenteredMoment` for cameras `2,...,7`;
- transfer of the same second-moment limit to the direct functional matrix
  product and every compatible return-metric colligation family.
- the exact cubic increment below `ell*M`, with its cubic boundary, second-
  and first-moment binomial terms and negligible cubic change of center;
- little-o summation of that increment, giving the raw third scalar limit
  `ell(log(ell)^3-3log(ell)^2+6log(ell)-6)` and the
  weighted-mean-centered limit `ell(log(ell)^3+3log(ell)-2)`.
- discrete Abel summation for nonnegative monotone weights against zero-mean
  periodic profiles, bounding the unbounded log-cubed weighted sum by its
  endpoint size;
- eventual monotonicity of `log(n+1)^3 w_z(n)`, its `O(log M)` endpoint
  growth and the normalized decay `log(M)/A_M(z) -> 0`;
- elimination of the centered cubic periodic residue and every fixed-width
  literal boundary term;
- entrywise and finite-matrix norm convergence of the complete
  centered-cubic coefficient covariance to `thirdCenteredMomentMatrix`, with
  exact target `sixCameraThirdCenteredMoment` for cameras `2,...,7`;
- transfer of the same third-moment limit to the direct functional matrix
  product and every compatible return-metric colligation family.
- the exact quartic increment below `ell*M`, with its fourth-power boundary,
  cubic-, quadratic- and first-moment binomial terms and fourth-power change
  of center;
- endpoint-weight negligibility of every quartic correction except the
  logarithmic step times the already proved raw cubic moment;
- little-o summation of that increment, giving the raw fourth scalar limit
  `ell(log(ell)^4-4log(ell)^3+12log(ell)^2-24log(ell)+24)` and the
  weighted-mean-centered limit
  `ell(log(ell)^4+6log(ell)^2-8log(ell)+9)`.
- discrete Abel summation for the log-fourth resolvent weight, whose endpoint
  grows as `O(log(M)^2)`, and the normalized decay
  `log(M)^2/A_M(z) -> 0`;
- slow variation of `μ_M(z)` under every fixed positive natural dilation,
  followed by elimination of all terms in the centered quartic periodic
  residue and every fixed-width literal boundary;
- entrywise and finite-matrix norm convergence of the complete
  centered-quartic coefficient covariance to `fourthCenteredMomentMatrix`,
  with exact target `sixCameraFourthCenteredMoment` for cameras `2,...,7`;
- transfer of the same fourth-moment limit to the direct functional matrix
  product and every compatible return-metric colligation family.
- the exact quintic increment below `ell*M`, with its fifth-power boundary,
  fourth-, cubic-, quadratic- and first-moment binomial terms and fifth-power
  change of center;
- endpoint-weight negligibility of every quintic correction except the
  logarithmic step times the already proved raw fourth moment;
- little-o summation of that increment, giving the raw fifth scalar limit
  `ell(log(ell)^5-5log(ell)^4+20log(ell)^3-60log(ell)^2+
  120log(ell)-120)` and the weighted-mean-centered limit
  `ell(log(ell)^5+10log(ell)^3-20log(ell)^2+45log(ell)-44)`.
- discrete Abel summation for the log-fifth resolvent weight, its endpoint
  growth `O(log(M)^3)` and the normalized decay `log(M)^3/A_M(z) → 0`;
- the auxiliary asymptotic `μ_M(z)/log(M+1) → 1`, which closes the new
  `μ_M log^4` and `μ_M^2 log^3` periodic terms;
- elimination of the centered quintic periodic residue and every fixed-width
  literal boundary term;
- entrywise and finite-matrix norm convergence of the complete centered-
  quintic coefficient covariance to `fifthCenteredMomentMatrix`, with exact
  target `sixCameraFifthCenteredMoment` for cameras `2,...,7`;
- transfer of the same fifth-moment limit to the direct functional matrix
  product and every compatible return-metric colligation family.
- the exact sextic increment below `ell*M`, with its sixth-power boundary,
  fifth- through first-moment binomial terms and positive sixth-power mass
  correction;
- endpoint-weight negligibility of every sextic correction except the
  logarithmic step times the already proved raw fifth moment;
- little-o summation of that increment, giving the raw sixth scalar limit
  `ell(log(ell)^6-6log(ell)^5+30log(ell)^4-120log(ell)^3+
  360log(ell)^2-720log(ell)+720)` and the weighted-mean-centered limit
  `ell(log(ell)^6+15log(ell)^4-40log(ell)^3+135log(ell)^2-
  264log(ell)+265)`.
- discrete Abel summation for the log-sixth resolvent weight, its endpoint
  growth `O(log(M)^4)` and the normalized decay `log(M)^4/A_M(z) → 0`;
- reduction of the critical `μ_M log^5`, `μ_M^2 log^4` and
  `μ_M^3 log^3` periodic terms using `μ_M(z)/log(M+1) → 1`;
- elimination of the centered sextic periodic residue and every fixed-width
  literal boundary term;
- entrywise and finite-matrix norm convergence of the complete centered-
  sextic coefficient covariance to `sixthCenteredMomentMatrix`, with exact
  target `sixCameraSixthCenteredMoment` for cameras `2,...,7`;
- transfer of the same sixth-moment limit to the direct functional matrix
  product and every compatible return-metric colligation family.
- the exact seventh-power increment below `ell*M`, with its seventh-power
  boundary, sixth- through first-moment binomial terms and negative
  seventh-power mass correction;
- endpoint-weight negligibility of every seventh-power correction except the
  logarithmic step times the already proved raw sixth moment;
- little-o summation of that increment, giving the raw seventh scalar limit
  `ell(log(ell)^7-7log(ell)^6+42log(ell)^5-210log(ell)^4+
  840log(ell)^3-2520log(ell)^2+5040log(ell)-5040)` and the
  weighted-mean-centered limit
  `ell(log(ell)^7+21log(ell)^5-70log(ell)^4+315log(ell)^3-
  924log(ell)^2+1855log(ell)-1854)`.
- discrete Abel summation for the log-seventh resolvent weight, its endpoint
  growth `O(log(M)^5)` and normalized decay `log(M)^5/A_M(z) → 0`;
- reduction of the critical `μ_M log^6`, `μ_M^2 log^5`, `μ_M^3 log^4` and
  `μ_M^4 log^3` periodic terms using `μ_M(z)/log(M+1) → 1`;
- elimination of the centered seventh-power periodic residue and every
  fixed-width literal boundary term;
- entrywise and finite-matrix norm convergence of the complete centered-
  seventh coefficient covariance to `seventhCenteredMomentMatrix`, with exact
  target `sixCameraSeventhCenteredMoment` for cameras `2,...,7`;
- transfer of the same seventh-moment limit to the direct functional matrix
  product and every compatible return-metric colligation family.
- the exact eighth-power increment below `ell*M`, with its eighth-power
  boundary, seventh- through first-moment binomial terms and positive
  eighth-power mass correction;
- endpoint-weight negligibility of every eighth-power correction except the
  logarithmic step times the already proved raw seventh moment;
- little-o summation of that increment, giving the raw eighth scalar limit
  `ell(log(ell)^8-8log(ell)^7+56log(ell)^6-336log(ell)^5+
  1680log(ell)^4-6720log(ell)^3+20160log(ell)^2-
  40320log(ell)+40320)` and the weighted-mean-centered limit
  `ell(log(ell)^8+28log(ell)^6-112log(ell)^5+630log(ell)^4-
  2464log(ell)^3+7420log(ell)^2-14832log(ell)+14833)`.
- discrete Abel summation for the log-eighth resolvent weight, its endpoint
  growth `O(log(M)^6)` and normalized decay `log(M)^6/A_M(z) → 0`;
- reduction of the critical `μ_M log^7`, `μ_M^2 log^6`, `μ_M^3 log^5`,
  `μ_M^4 log^4` and `μ_M^5 log^3` periodic terms using
  `μ_M(z)/log(M+1) → 1`;
- elimination of the centered eighth-power periodic residue and every
  fixed-width literal boundary term;
- entrywise and finite-matrix norm convergence of the complete centered-
  eighth coefficient covariance to `eighthCenteredMomentMatrix`, with exact
  target `sixCameraEighthCenteredMoment` for cameras `2,...,7`;
- transfer of the same eighth-moment limit to the direct functional matrix
  product and every compatible return-metric colligation family.
- the single polynomial recurrence `P_0=1`, `P_k=(1+X)^k-kP_(k-1)` for all
  natural degrees, with `P_k` monic of natural degree exactly `k`;
- the general algebraic camera target
  `M_k(i,j)=G(i,j)P_k(log(min(ell_i,ell_j)))`, Hermitian and self-adjoint for
  every finite camera family;
- exact bridges recovering degrees zero through eight and an exact literal
  self-adjoint moment matrix for cameras `2,...,7` in every degree.

The exact finite polynomial layer, logarithmic centering asymptotic, first
eight scalar centered moments and complete linear through eighth-power
functional covariance limits are complete.  The next Phase 4 target is to
lift the scalar recurrence, Abel estimates and periodic-residue elimination to
a degree-generic induction over `functionalMomentPolynomial`.  The algebraic
targets exist in every degree, while analytic convergence remains checked
through degree eight.  The existing transfer theorems lift future generic
coefficient-sum results to the direct and return-metric formulations.  Locally uniform
Cauchy-transform convergence off the real axis follows afterward.

Targets:

- degree-generic scalar and covariance limits for the moment hierarchy;
- locally uniform Cauchy-transform convergence off the real axis.

The Green v2.1 strong Parseval and finite-Poisson limits may be reused through
their public API, but every new spectral generator/domain statement remains a
new proof obligation here.

## 8. Phase 5 — countable all-bases camera atlas

Suggested modules:

```text
NativeCarrySpectralWeyl/Infinite/GramKernel.lean
NativeCarrySpectralWeyl/Infinite/CameraCompletion.lean
NativeCarrySpectralWeyl/Infinite/Kolmogorov.lean
NativeCarrySpectralWeyl/Infinite/Naimark.lean
NativeCarrySpectralWeyl/Infinite/LogarithmicMultiplication.lean
NativeCarrySpectralWeyl/Infinite/Cauchy.lean
NativeCarrySpectralWeyl/Infinite/ComplexifiedCauchy.lean
NativeCarrySpectralWeyl/Infinite/WeylInverse.lean
NativeCarrySpectralWeyl/Infinite/WeylUnbounded.lean
```

Proof order:

1. prove strict positivity of the Gram form on `Finsupp` (including the special
   two-camera slope-4 block);
2. complete that pre-Hilbert space rather than imposing standard camera `l2`;
3. build a Kolmogorov realization of the periodic kernel;
4. extend the explicit step-function map to a Naimark isometry;
5. construct the logarithmic multiplication operator on its natural domain,
   prove that domain dense, and identify the original operator with its
   Hilbert-space adjoint;
6. compress the resolvent to obtain a bounded Cauchy family;
7. prove strict imaginary sign, injectivity and dense range;
8. define the inverse as a `LinearPMap`, prove it closed and densely defined;
9. use normalized single-camera vectors to prove the inverse is not bounded.

Kernel checked through the v0.53 closed rigged-port milestone:

- the countable index of all camera labels `b >= 2` and the pair period given
  by the least common multiple of their slopes;
- invariance of the normalized product mean under every positive common
  multiple and exact recovery of the prior finite Gram on each finite support;
- the exact C2/C4 slope-four mean block with determinant `2`;
- a level/residue sum-of-squares identity, strict positive definiteness of
  every finite principal restriction, and strict positivity of the resulting
  `Finsupp` Gram form.
- all bilinear inner-product laws for that Gram form and the induced intrinsic
  real norm on finitely supported camera coefficients;
- the canonical Mathlib completion, its explicit completeness, dense
  isometric embedding and canonical camera vectors with Gram-kernel inner
  products;
- monotone compatible finite-label inclusions and density of their union in
  the all-bases completion.
- exact identification of every finite periodic-mean kernel restriction with
  its common-period profile-mean matrix and positive semidefiniteness;
- the intrinsic periodic-mean pre-inner product on a type-distinct finitely
  supported core and its canonical complete Kolmogorov space `K₀`;
- canonical vectors `r_b` with inner products exactly `m_bc`, explicit finite
  linear-combination generation of the dense completion image, and density of
  their algebraic span.
- Lebesgue measure restricted to `(0,∞)`, measurable finite intervals
  `(0,ell_b]`, and the exact overlap identity
  `measure((0,ell_b] ∩ (0,ell_c]) = min(ell_b,ell_c)`;
- explicit vectors `1_(0,ell_b] r_b` in `L²((0,∞),K₀)`, including their
  almost-everywhere indicator representatives and exact full-Gram inner
  products;
- the finite linear-combination map from the intrinsic camera `Finsupp` core,
  with exact Gram-form, norm and single-camera identities;
- its continuous extension along the dense camera-completion embedding and
  the resulting linear isometry
  `CameraHilbert →ₗᵢ[ℝ] L²((0,∞),K₀)`, preserving all inner products and
  sending each canonical camera vector to its indicator vector.
- the measurable spectral coordinate `y(x)=1+log x`, its maximal
  square-integrability domain `{f ∈ L² : y f ∈ L²}`, and the corresponding
  multiplication operator bundled as a Mathlib `LinearPMap` with literal
  almost-everywhere action;
- membership of every camera indicator and every finite camera-core
  combination in that domain, using the exact integrability of `y²` at zero;
- the bounded positive regularizer `(1+|y|)⁻¹`, whose multiplication map is
  symmetric and injective with dense range contained in the maximal domain,
  hence density of the logarithmic domain in the full Naimark space;
- symmetry and closability of logarithmic multiplication and closedness of
  its canonical graph closure;
- the bounded transfer multiplier `y/(1+|y|)`, obtained by applying the
  logarithmic operator after regularization, and its real symmetry;
- the almost-everywhere adjoint action obtained from
  `(yR)g = R(Y†g)` and cancellation of the strictly positive regularizer;
- equality of the adjoint domain with the natural maximal multiplication
  domain, `Y†=Y`, self-adjointness and closedness of `Y`, and equality of its
  canonical graph closure with `Y` itself.
- the measurable real and imaginary scalar parts of `(lambda-y)⁻¹`, their
  exact inverse and reciprocal-denominator identities, conjugation laws and
  `|Im lambda|⁻¹` bounds for every nonreal `lambda`;
- bounded self-adjoint resolvent multipliers on the Naimark space with literal
  almost-everywhere action and the corresponding operator-norm bounds;
- compression by `V†(·)V` to two bounded self-adjoint real operators on the
  camera Hilbert space, canonically representing the real and imaginary parts
  of the all-bases Cauchy family;
- conjugate symmetry, strict upper/lower half-plane quadratic-form signs, and
  injectivity with dense range of the compressed imaginary component.
- the underlying real Hilbert space
  `WithLp 2 (CameraHilbert × CameraHilbert)` of the canonical
  complexification and the standard real block
  `(x,y) ↦ (Ax-By,Bx+Ay)` for the complete Cauchy operator;
- the exact skew quadratic-form identity, strict sign on every nonzero
  doubled vector and injectivity of the complete Cauchy block;
- identification of the block adjoint with the Cauchy block at the conjugate
  spectral parameter and dense range of the complete block;
- the bounded Cauchy block as an everywhere-defined `LinearPMap`, with
  unchanged range, trivial kernel and closed graph;
- the inverse on that exact range as `allBasesWeylInverse`, with dense domain,
  graph obtained by coordinate swap, closedness, both exact inverse laws and
  surjectivity onto the whole realified complexification.
- the exact centered interval variance
  `integral 0..ell (1+log x-log ell)^2 = ell` and equality of centered and
  uncentered camera-vector norms;
- exact scalar and ambient-operator resolvent-shift identities, compression
  estimates and the explicit full-block bound
  `(abs(Re (lambda-mu)⁻¹)+abs(Im (lambda-mu)⁻¹)) *
  (1+2 abs(Im lambda)⁻¹)`;
- vanishing of that bound as `mu -> +infinity`, including the explicit
  supported camera sequence with labels `n+3` and logarithmic centers
  `log(n+3)`;
- normalized realified unit camera vectors whose complete Cauchy images
  converge to zero;
- failure of every positive lower bound for the Cauchy block and failure of
  every global norm bound for the closed densely defined Weyl inverse.

All nine Phase 5 steps are now checked.  An independent complex scalar action
and an explicit projection-valued measure remain open, but neither is needed
for the realified unboundedness theorem.  The v0.46 construction uses the
exact direct multiplication model and does not introduce a standard
unweighted camera `l2` space.

This phase must not represent the all-bases inverse as an everywhere-defined
continuous linear map.

## 9. Phase 6 — boundary relation and Green coupling

Only after Phase 5:

```text
NativeCarrySpectralWeyl/Boundary/GreenRelation.lean
NativeCarrySpectralWeyl/Boundary/SourceRelation.lean
NativeCarrySpectralWeyl/Infinite/ComplexifiedResolvent.lean
NativeCarrySpectralWeyl/Boundary/GammaField.lean
NativeCarrySpectralWeyl/Boundary/GreenCameraCoupling.lean
NativeCarrySpectralWeyl/Boundary/AngularReadout.lean
NativeCarrySpectralWeyl/Boundary/RiggedAngularOrbit.lean
NativeCarrySpectralWeyl/Boundary/RiggedBoundaryPort.lean
```

- define linear relations as submodules of a product Hilbert space;
- formalize the symplectic Green identity and maximality;
- define the reference self-adjoint extension and rotated impedance chart;
- construct the gamma field and show its Weyl family equals the compressed-
  resolvent inverse;
- prove any strong-star to strong-graph passage through graph projections;
- connect external Green ports and spectral camera ports by an explicit map;
- construct and bound the research-specific infinite state readout needed to
  instantiate that interface without an external hypothesis;
- construct the logarithmically rigged native angular family when the raw
  amplitude does not belong to the Green state Hilbert space itself;
- separate canonical maximal unrigging and strong-dual rigged evaluation from
  the research-specific Green/Haar-to-camera synthesis;
- formulate that remaining camera synthesis as a typed mixed-order boundary
  form/port rather than assuming bounded unrigging.

The old finite maximal-isotropic calculation remains useful motivation, but
the infinite adjoint/domain theorem is discharged independently by the v0.43
regularizer argument above.

Kernel checked through v0.53:

- linear relations represented as submodules of the product Hilbert space;
- the documented skew-Hermitian Green form and its exact symplectic
  orthogonal via Mathlib's submodule adjoint;
- preservation of that form by the Weyl/impedance chart rotation
  `(Gamma_0,Gamma_1) ↦ (-Gamma_1,Gamma_0)`;
- equivalence of graph Green-isotropy with formal symmetry and, for dense
  domains, equivalence of maximal Green-isotropy with self-adjointness;
- the graph of maximal logarithmic multiplication as a closed maximal Green
  reference relation;
- the source-extended relation `T_C={(f,Yf+Vu)}` as the range of an explicit
  linear parameterization, with exact membership and uniqueness whenever the
  bounded port `V` is injective;
- reference and Weyl charts `(u,-V^*f)` and `(V^*f,u)` as well-defined linear
  maps on the relation, and their exact symplectic quarter-turn relation;
- the Green identity in both charts for every formally symmetric `Y`;
- maximal coupled Green-isotropy of the Weyl boundary graph for every
  self-adjoint `Y`, proved by recovering both the boundary coordinate and the
  adjoint-domain condition from symplectic test vectors;
- the concrete all-bases instance with maximal logarithmic multiplication,
  the injective Naimark isometry and its adjoint compression map;
- rectangular real `2 × 2` blocks for the ambient Naimark port, its adjoint,
  complex scalar multiplication and `(lambda-Y)⁻¹`, with exact compression
  equal to the complete all-bases Cauchy block;
- maximal-domain membership of both resolvent components and the exact
  realified resolvent equation;
- injectivity of `lambda-Y` from the imaginary-part energy identity,
  two-sided inverse laws with the domain-valued resolvent, and bijectivity for
  every nonreal `lambda`;
- the bounded injective source gamma map `u ↦ (lambda-Y)⁻¹Vu`, its exact defect
  equation and uniqueness in the maximal domain;
- source boundary values `Gamma_0=M_infinity(lambda)u`, `Gamma_1=u`, and the
  defect space as the exact range of the injective source parametrization;
- the trace-parametrized partial gamma field on the exact dense Cauchy range,
  with `Gamma_0 gamma(lambda)xi=xi` and
  `Gamma_1 gamma(lambda)xi=M_infinity(lambda)⁻¹xi`;
- identification of the boundary Weyl family with the existing closed,
  densely defined and non-norm-bounded `LinearPMap` inverse.
- a generic `GreenCameraCoupling T` whose only new analytic datum is an
  explicitly supplied bounded real-linear state readout from the Green state
  space to the realified all-bases camera space;
- the induced external camera port obtained from canonical ambient synthesis,
  with the operator identity
  `externalPort ∘ normalizedExternal = stateReadout`;
- the independent static Poisson component and the joint camera/bulk output,
  recovering `(stateReadout x, normalizedBulk x)` on coherent external data;
- pullback of the source gamma field to external Green data, membership of
  every resulting state in the carry defect subspace, the exact defect
  equation and uniqueness on the maximal logarithmic domain;
- induced Cauchy traces in the exact Weyl domain and the transport identities
  `gamma(trace(e)) = gammaSource(externalPort(e))` and
  `W(lambda)(trace(e)) = externalPort(e)`;
- the concrete specialization to `concreteAnalysisOperator omega` and its
  kernel-checked split bounds;
- `AngularGreenCameraCoupling`, which adds a supplied family `t ↦ x(t)` to the
  bounded-readout interface without assuming a group law, continuity or a
  rigged-state realization;
- exact coherent recovery of the angular camera readout and the separate
  normalized bulk through external synthesis;
- angular source-gamma evaluation for every independently chosen nonreal
  `lambda`, including the exact defect equation, uniqueness on the maximal
  logarithmic domain and Cauchy-trace law
  `W(lambda)(trace(t,lambda)) = stateReadout(x(t))`;
- equivalence of angular readout, gamma and Weyl zero tests, and explicit
  equality of the recovered outputs and zero tests for arbitrary nonreal
  probes `z0` and `lambda`, without identifying either with `t`;
- exact harmonic energy of the raw critical amplitude and its resulting
  nonmembership in unweighted `ℓ²(PNat, ℂ)`;
- summability of `n⁻¹/(1+log n)²` and construction of the canonical weighted
  critical vector in `LogRiggedState`;
- diagonal evolution by `exp(-it log n)` as a complex-linear isometric
  equivalence group with exact zero, addition, inverse and norm laws;
- norm continuity of every rigged orbit via a summable energy majorant, and
  continuity plus constant norm of the distinguished critical orbit;
- exact pointwise recovery of `dirichletValue (nativeLine t) n` after removal
  of the logarithmic rigging weight;
- bounded injective logarithmic rigging with dense range and exact range equal
  to the maximal unrigging domain;
- maximal unrigging as multiplication by `1+log n` on the explicit proper
  dense square-summability domain, with exact two-sided inverse laws and full
  range;
- closedness, closability, self-adjointness and equality with the canonical
  graph closure;
- invariance of that domain under angular evolution and the exact
  intertwining law;
- nonmembership of every critical-orbit vector in the unrigging domain;
- the canonical global Fréchet--Riesz port into the strong dual of the `H₁`
  test-coordinate realization, with a continuous constant-norm critical dual
  orbit.

The v0.53 interface deliberately does not manufacture the research-specific
bounded `stateReadout` or claim that the raw amplitude lies in the Green state
Hilbert space.  It instead proves that canonical unrigging is a closed
self-adjoint partial operator and that the critical orbit is outside its exact
domain; the orbit belongs globally to the canonical strong dual.  The missing
object is therefore the separate mixed-order Green/Haar-to-all-bases camera
synthesis, not closure of diagonal unrigging.

The post-v0.53 gate selects a form-first interface.  The generic completion
theorem now extends every bounded real functional from `CameraFinsupp` to
`CameraHilbert`, preserves its exact norm, gives the same bound on every
isometrically embedded atlas and proves compatibility of the finite-label
restrictions.  The Naimark model supplies the canonical constant-one target
pairing for a unit source.  The next analytic input is therefore sharply
localized: define the research-specific Green/Haar core functional and prove
its single atlas-independent Gram-norm estimate, then establish the required
source/intertwining realization.  Strong-resolvent or strong-graph passage
remains unused; if a future construction requires it, its topology and domains
must be stated explicitly.  The current realified representation remains
deliberate: no independent complex scalar action, bounded vector synthesis,
everywhere-defined inverse or ordinary boundary triple is inferred.

## 10. Phase 7 — optional holonomic track

After the Weyl core has a release:

- mixed `3-4-6` scalar measure and Jacobi coefficients;
- Hankel determinants and positivity;
- two-jump Toda identities;
- constant-coefficient tau annihilator;
- three-color creation algebra and resultant dressing.

Painlevé literature specializations remain `SOURCE_DERIVATION` until every
normalization and hypothesis has a Lean proof.  No scalar JMO-`P_V` collapse is
claimed.

## 11. Release gates

Each milestone must reproduce the Green publication discipline:

1. exact clean checkout identity;
2. `lake build --wfail`;
3. repository scan rejecting `sorry`, `admit`, local `axiom` and `unsafe`;
4. complete public import reachability;
5. ordered theorem registry and one named `#print axioms` report per theorem;
6. foundational allowlist limited to the explicitly approved Mathlib axioms;
7. claim ledger matching exact theorem IDs;
8. byte-for-byte source provenance;
9. release tag and assets bound to the successful audited SHA.

No milestone is tagged while a cited source claim lacks a corresponding kernel
declaration or an honest non-kernel status.
