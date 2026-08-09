# Formalization plan

## 1. Audit findings

The GitHub repository began at commit
`39cb245d0b612c4cd213a664a8b7730660254aa9` with only `LICENSE`.

The local research directory `carry-lab/Wayl` contains 66 files (about 1.2 MB):

- 27 Markdown derivations;
- 17 Python laboratories;
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

### v0.1 progress

Kernel checked in the first camera-arithmetic candidate:

- exact supported-camera slope and radius-count bridge to
  `FiniteNativeCarryOperator`;
- aligned C2, odd natural and even natural profile formulas;
- exact periodicity and mean zero over one spectral period;
- explicit `A_b(s)` definitions for all three camera classes;
- exact complex-power norms on `s = 1/2 + i t`;
- the uniform positive all-camera floor and nonvanishing theorem.

Still open before Phase 1 is fully closed:

- extract the interior scalar coefficients directly from the finite operator
  sums and identify them with `profile`;
- connect the period profiles to the Dirichlet multiplier formulas in an
  absolutely convergent domain;
- record the alternate closed form
  `(sqrt 2 - 1)^2 / sqrt 2` for the universal constant.

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
NativeCarrySpectralWeyl/Camera/CrossFactorization.lean
NativeCarrySpectralWeyl/Camera/CommonZeroSet.lean
```

Obligations:

- bound centered second differences using the integral/Taylor remainder;
- prove normal convergence on compact subsets of `re s > -1`;
- establish the factorization first in the absolutely convergent half-plane;
- extend the cross identity by the holomorphic identity theorem;
- define the native scalar through camera 3 only where its factor is nonzero;
- prove common zero sets on the native line;
- handle analytic multiplicity separately through local zero order.

The `O(M^(-3/2))` tail and derivative bounds are separate quantitative
theorems, not implicit consequences of pointwise convergence.

## 6. Phase 3 — finite camera spectral package

Suggested modules:

```text
NativeCarrySpectralWeyl/Finite/Gram.lean
NativeCarrySpectralWeyl/Finite/Moments.lean
NativeCarrySpectralWeyl/Finite/Whitening.lean
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

Targets:

- finite resolvent-weighted defect analysis;
- exact return-metric covariance cancellation;
- periodic weighted-mean lemma;
- operator-norm convergence of normalized finite covariance to the camera
  Gram;
- polynomial functional moments;
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
NativeCarrySpectralWeyl/Infinite/Cauchy.lean
NativeCarrySpectralWeyl/Infinite/WeylInverse.lean
```

Proof order:

1. prove strict positivity of the Gram form on `Finsupp` (including the special
   two-camera slope-4 block);
2. complete that pre-Hilbert space rather than imposing standard camera `l2`;
3. build a Kolmogorov realization of the periodic kernel;
4. extend the explicit step-function map to a Naimark isometry;
5. construct the logarithmic multiplication operator on its natural domain;
6. compress the resolvent to obtain a bounded Cauchy family;
7. prove strict imaginary sign, injectivity and dense range;
8. define the inverse as a `LinearPMap`, prove it closed and densely defined;
9. use normalized single-camera vectors to prove the inverse is not bounded.

This phase must not represent the all-bases inverse as an everywhere-defined
continuous linear map.

## 9. Phase 6 — boundary relation and Green coupling

Only after Phase 5:

- define linear relations as submodules of a product Hilbert space;
- formalize the symplectic Green identity and maximality;
- define the reference self-adjoint extension and rotated impedance chart;
- construct the gamma field and show its Weyl family equals the compressed-
  resolvent inverse;
- prove any strong-star to strong-graph passage through graph projections;
- connect external Green ports and spectral camera ports by an explicit map;
- state the angular readout theorem with `t` independent from `lambda`.

The old finite maximal-isotropic calculation is useful motivation, but it does
not discharge the infinite adjoint/domain theorem.

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
