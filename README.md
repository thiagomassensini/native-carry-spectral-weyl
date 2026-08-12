# Native Carry Spectral Weyl

Lean 4 formalization of the spectral/Weyl layer associated with the native
carry cameras.

## Current status

The v0.53 closed rigged-port milestone contains **1,318 public
kernel-checked Lean theorems**.  It builds against the exact Green Frame v2.1
commit and the exact finite native-carry operator commit.  The current public
surface proves:

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
- the countable index of every supported camera `b >= 2`, with canonical
  pairwise period `lcm(ell_b,ell_c)` and a normalized product mean proved
  invariant under every larger positive common period;
- exact identification of every finite principal restriction of the
  all-bases kernel with the earlier finite periodic Gram matrix;
- the exact exceptional C2/C4 slope-four periodic-mean block
  `[[3/2,5/2],[5/2,11/2]]`, determinant `2`, and positive definiteness;
- a level/residue sum-of-squares identity proving every finite principal Gram
  matrix positive definite and the induced `Finsupp` Gram form strictly
  positive on every nonzero finitely supported coefficient vector.
- the intrinsic real inner-product and Gram norm on finitely supported
  all-bases camera coefficients, with no externally chosen camera weight;
- the canonical complete camera Hilbert space obtained from Mathlib's
  completion, together with its dense isometric `Finsupp` embedding;
- canonical camera vectors whose inner products are exactly the all-bases
  Gram kernel, and compatible finite-label inclusions whose union is dense.
- exact recovery of every finite principal periodic-mean kernel restriction
  as the earlier finite periodic profile-mean matrix, hence positive
  semidefiniteness on every finite camera support;
- the intrinsic periodic-mean pre-inner product on a type-distinct `Finsupp`
  core and its canonical complete Kolmogorov space `K₀`, with seminorm-zero
  vectors separated by Mathlib's completion;
- canonical Kolmogorov vectors `r_b` satisfying
  `inner r_b r_c = periodicMeanKernel b c` exactly, whose algebraic span is
  dense in `K₀`.
- Lebesgue measure on the positive half-line and the exact overlap formula
  `measure((0,ell_b] ∩ (0,ell_c]) = min(ell_b,ell_c)`;
- explicit Naimark vectors `1_(0,ell_b] r_b` in `L²((0,∞),K₀)`, with their
  almost-everywhere indicator representatives and inner products exactly
  equal to the complete all-bases Gram kernel;
- the finite step-function map preserving the intrinsic camera Gram form and
  norm, and its extension to a real linear isometry
  `CameraHilbert →ₗᵢ[ℝ] L²((0,∞),K₀)` that maps every canonical camera
  vector to its explicit indicator vector.
- the documented spectral coordinate `y(x)=1+log x` and multiplication by
  `y` as a Mathlib `LinearPMap` on the exact maximal domain
  `{f ∈ L² : y f ∈ L²}`, with its literal almost-everywhere action;
- square-integrability at the singular endpoint for every camera indicator,
  placing every explicit Naimark camera vector and every finite camera-core
  combination in that maximal domain;
- density of the logarithmic domain via the bounded positive regularizer
  `(1+|y|)⁻¹`, whose symmetric multiplication map is injective and has dense
  range contained in the domain;
- symmetry of the logarithmic `LinearPMap` and the bounded transfer identity
  obtained from the positive regularizer `(1+|y|)⁻¹`;
- exact characterization of the adjoint action and domain, equality of the
  maximal multiplier with its Hilbert-space adjoint, self-adjointness and
  closedness; its canonical graph closure is exactly the original operator.
- the exact real and imaginary coefficients of `(lambda-y)⁻¹` for every
  nonreal `lambda`, including both scalar inverse identities, the reciprocal-
  denominator norm identity and the standard resolvent-scale component bounds
  `|Re|, |Im| <= |Im lambda|⁻¹`;
- bounded self-adjoint real and imaginary resolvent multiplication operators
  on the Naimark `L²` space, with literal almost-everywhere action, operator-
  norm bounds and conjugate-parameter symmetry;
- compression through the all-bases Naimark isometry, producing the canonical
  real/imaginary-component representation of
  `M_infinity(lambda)=V†(lambda-Y)⁻¹V` on the real camera Hilbert space;
- self-adjointness of both compressed components, the same
  `|Im lambda|⁻¹` bounds, conjugate symmetry, strict negative imaginary
  quadratic form in the upper half-plane and strict positive sign in the
  lower half-plane;
- injectivity and dense range of the compressed imaginary component for every
  nonreal `lambda`.
- the canonical real `2 × 2` block
  `(x,y) ↦ (Ax-By,Bx+Ay)` on
  `WithLp 2 (CameraHilbert × CameraHilbert)`, representing the full complex
  Cauchy family without silently imposing an unproved complex scalar action;
- the exact skew quadratic-form identity, strict upper/lower half-plane sign,
  injectivity of the full Cauchy block, conjugate-parameter adjoint identity
  and dense range;
- the inverse of that block on its exact range as a Mathlib `LinearPMap`, with
  dense domain, closed graph, exact left/right inverse laws and full range.
- the exact camera-interval identity
  `integral 0..ell (1 + log x - log ell)^2 = ell`, giving unit logarithmic
  variance after normalization;
- exact scalar and operator resolvent-shift identities and the explicit bound
  `(abs(Re (lambda-mu)⁻¹) + abs(Im (lambda-mu)⁻¹)) *
  (1 + 2 * abs(Im lambda)⁻¹)` at `mu = log ell`;
- the unit sequence supported on camera labels `3,4,5,...`, whose complete
  Cauchy images converge to zero;
- failure of every positive lower bound for the complete Cauchy block and
  failure of every global norm bound for its closed densely defined
  `LinearPMap` inverse.
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
- the exact return metric `G_E = I + PᴴP` and the finite cancellation
  `Eᴴ G_E E = I` from `P E = B` and `EᴴE + BᴴB = I`, hence
  `S G_E Sᴴ = C R Rᴴ Cᴴ` for `S = C R Eᴴ`;
- a common-window literal finite camera matrix containing every seed and tail
  coefficient, including the one-unit correction at the final antipodal
  point of each even camera;
- exact identification of its normalized diagonal-resolvent matrix product
  with the complete finite coefficient covariance;
- decomposition of that covariance into the shifted periodic core plus a
  cutoff-independent finite boundary tail, and proof that the resolvent tail
  vanishes;
- entrywise and matrix-norm convergence of the literal finite covariance, the
  direct matrix product and every compatible return-metric colligation family,
  including the exact complexified six-camera limit `sixCameraGram`.
- exact cancellation of the return-metric cross covariance after inserting an
  arbitrary spectral observable in one probe leg, with no commutation or
  polynomial hypothesis;
- exact identification of every real functional multiplier with its complete
  literal finite coefficient sum, including all finite seeds and corrected
  even-camera endpoints;
- specialization to every real polynomial evaluated at
  `log(n+1) - μ_M(z)`, where `μ_M(z)` is the finite resolvent-weighted
  logarithmic mean, and exact recovery of the order-zero covariance for the
  constant polynomial;
- transfer of any proved coefficient-sum limit to both the direct functional
  matrix product and every compatible return-metric colligation family.
- the exact telescoping formula for the centered resolvent-weighted logarithmic
  numerator, whose increment is
  `w_M - A_M * (log(M+1) - log M)`;
- the elementary limit `M * (log(M+1) - log M) → 1` and, together with the
  existing `A_M / (M w_M) → 1`, the kernel-checked second-order asymptotic
  `μ_M(z) - log M → -1` for every fixed nonreal `z`.
- fixed-displacement slow variation
  `w_z(ell*M+r) / w_z(M) → 1` and the logarithmic boundary limit
  `log(ell*M+r+1) - log(M+1) → log ell` for every fixed positive natural
  `ell` and fixed natural `r`;
- the exact discrete increment for the first logarithmic scalar moment below
  `ell*M`, and the normalized limit centered at `log M`,
  `A_M^-1 sum_(n<ell*M) (log(n+1)-log M)w_z(n) → ell(log ell-1)`;
- the first weighted-mean-centered scalar functional limit
  `A_M^-1 sum_(n<ell*M) (log(n+1)-μ_M(z))w_z(n) → ell log ell`, exactly the
  endpoint integral of `1 + log x` from `0` to `ell`;
- bounded Dirichlet prefixes for zero-mean periodic residues against the
  eventually antitone weights `w_z(n)` and `log(n+1)w_z(n)`, which eliminate
  the centered linear periodic residue after normalization by `A_M`;
- vanishing of every fixed seed and corrected endpoint contribution for the
  centered linear multiplier, followed by entrywise and finite-matrix norm
  convergence of the complete literal coefficient covariance to
  `H_bc = G_bc log(min(ell_b,ell_c))`;
- transfer of that first-moment limit to the direct functional matrix product
  and every compatible return-metric colligation family, with cameras
  `2,...,7` converging to the exact complexification of
  `sixCameraFirstMoment`;
- the exact quadratic discrete recurrence below `ell*M`, whose boundary,
  first-moment and squared change-of-center terms yield
  `A_M^-1 sum (log(n+1)-log M)^2 w_z(n) →
  ell(log(ell)^2-2log(ell)+2)`;
- the second weighted-mean-centered scalar functional limit
  `A_M^-1 sum_(n<ell*M) (log(n+1)-μ_M(z))^2 w_z(n) →
  ell(1+log(ell)^2)`, matching the endpoint integral of `(1+log x)^2`.
- bounded Dirichlet prefixes for zero-mean periodic residues against the
  log-squared resolvent weight, whose tail is proved eventually monotone in
  the appropriate direction for every nonreal `z`;
- elimination of the centered quadratic periodic residue and every fixed
  literal seed/corrected-endpoint boundary term, giving entrywise and
  finite-matrix norm convergence of the complete coefficient covariance to
  `J_bc = G_bc * (1 + log(min(ell_b,ell_c))^2)`;
- transfer of the second-moment limit to the direct functional matrix product
  and every compatible return-metric colligation family, with cameras
  `2,...,7` converging to the exact complexification of
  `sixCameraSecondCenteredMoment`.
- the exact cubic discrete recurrence below `ell*M`, whose endpoint block and
  binomial change-of-center terms yield the raw limit
  `A_M^-1 sum (log(n+1)-log M)^3 w_z(n) →
  ell(log(ell)^3-3log(ell)^2+6log(ell)-6)`;
- the third weighted-mean-centered scalar functional limit
  `A_M^-1 sum_(n<ell*M) (log(n+1)-μ_M(z))^3 w_z(n) →
  ell(log(ell)^3+3log(ell)-2)`.
- a discrete Abel summation bound for unbounded monotone periodic weights,
  applied to `log(n+1)^3 w_z(n) = O(log n)` together with
  `log(M)/A_M(z) → 0`;
- elimination of the centered cubic zero-mean periodic residue and every
  fixed literal seed/corrected-endpoint boundary term, giving convergence of
  the complete coefficient covariance to
  `K_bc = G_bc * (log(min(ell_b,ell_c))^3 +
  3log(min(ell_b,ell_c)) - 2)`;
- transfer of the third-moment limit to the direct functional matrix product
  and every compatible return-metric colligation family, with cameras
  `2,...,7` converging to the exact complexification of
  `sixCameraThirdCenteredMoment`.
- the exact quartic discrete recurrence below `ell*M`, whose endpoint block
  and binomial change-of-center terms yield the raw limit
  `A_M^-1 sum (log(n+1)-log M)^4 w_z(n) →
  ell(log(ell)^4-4log(ell)^3+12log(ell)^2-24log(ell)+24)`;
- the fourth weighted-mean-centered scalar functional limit
  `A_M^-1 sum_(n<ell*M) (log(n+1)-μ_M(z))^4 w_z(n) →
  ell(log(ell)^4+6log(ell)^2-8log(ell)+9)`.
- a discrete Abel estimate for the log-fourth resolvent weight, whose endpoint
  is `O(log(M)^2)`, together with `log(M)^2/A_M(z) → 0` and slow variation
  of the logarithmic mean under every fixed positive natural dilation;
- elimination of the complete centered quartic periodic residue and every
  fixed literal seed/corrected-endpoint boundary term, yielding
  `L_bc = G_bc * (log(min(ell_b,ell_c))^4 +
  6log(min(ell_b,ell_c))^2 - 8log(min(ell_b,ell_c)) + 9)`;
- transfer of the fourth-moment limit to the direct functional matrix product
  and every compatible return-metric colligation family, with cameras
  `2,...,7` converging to the exact complexification of
  `sixCameraFourthCenteredMoment`.
- the exact quintic discrete recurrence below `ell*M`, whose endpoint block
  and binomial change-of-center terms yield the raw limit
  `A_M^-1 sum (log(n+1)-log M)^5 w_z(n) →
  ell(log(ell)^5-5log(ell)^4+20log(ell)^3-60log(ell)^2+
  120log(ell)-120)`;
- the fifth weighted-mean-centered scalar functional limit
  `A_M^-1 sum_(n<ell*M) (log(n+1)-μ_M(z))^5 w_z(n) →
  ell(log(ell)^5+10log(ell)^3-20log(ell)^2+45log(ell)-44)`.
- a discrete Abel estimate for the log-fifth resolvent weight, whose endpoint
  grows as `O(log(M)^3)`, together with `log(M)^3/A_M(z) → 0`;
- elimination of the complete centered quintic periodic residue, including
  the mixed `μ_M log^4` and `μ_M^2 log^3` terms, and every fixed literal
  seed/corrected-endpoint boundary;
- convergence of the complete fifth coefficient covariance, direct product
  and every compatible return-metric family to `fifthCenteredMomentMatrix`,
  with exact six-camera target `sixCameraFifthCenteredMoment`.
- the exact sextic discrete recurrence below `ell*M`, with binomial
  coefficients `-6, 15, -20, 15, -6, 1` and raw limit
  `ell(log(ell)^6-6log(ell)^5+30log(ell)^4-120log(ell)^3+
  360log(ell)^2-720log(ell)+720)`;
- the sixth weighted-mean-centered scalar functional limit
  `ell(log(ell)^6+15log(ell)^4-40log(ell)^3+
  135log(ell)^2-264log(ell)+265)`.
- a discrete Abel estimate for the log-sixth resolvent weight, whose endpoint
  grows as `O(log(M)^4)`, together with `log(M)^4/A_M(z) → 0`;
- elimination of the complete centered sextic periodic residue, including
  the critical mixed `μ_M log^5`, `μ_M^2 log^4` and `μ_M^3 log^3`
  terms, and every fixed literal seed/corrected-endpoint boundary;
- convergence of the complete sixth coefficient covariance, direct product
  and every compatible return-metric family to `sixthCenteredMomentMatrix`,
  with exact six-camera target `sixCameraSixthCenteredMoment`.
- the exact seventh-power recurrence below `ell*M`, with binomial
  coefficients `-7, 21, -35, 35, -21, 7, -1` and raw limit
  `ell(log(ell)^7-7log(ell)^6+42log(ell)^5-210log(ell)^4+
  840log(ell)^3-2520log(ell)^2+5040log(ell)-5040)`;
- the seventh weighted-mean-centered scalar functional limit
  `ell(log(ell)^7+21log(ell)^5-70log(ell)^4+315log(ell)^3-
  924log(ell)^2+1855log(ell)-1854)`.
- a discrete Abel estimate for the log-seventh resolvent weight, whose endpoint
  grows as `O(log(M)^5)`, together with `log(M)^5/A_M(z) → 0`;
- elimination of the complete centered seventh-power periodic residue,
  including the four critical mixed terms `μ_M log^6`, `μ_M^2 log^5`,
  `μ_M^3 log^4` and `μ_M^4 log^3`, and every fixed literal boundary;
- convergence of the complete seventh coefficient covariance, direct product
  and every compatible return-metric family to `seventhCenteredMomentMatrix`,
  with exact six-camera target `sixCameraSeventhCenteredMoment`.
- the exact eighth-power recurrence below `ell*M`, with binomial
  coefficients `-8, 28, -56, 70, -56, 28, -8, 1` and raw limit
  `ell(log(ell)^8-8log(ell)^7+56log(ell)^6-336log(ell)^5+
  1680log(ell)^4-6720log(ell)^3+20160log(ell)^2-
  40320log(ell)+40320)`;
- the eighth weighted-mean-centered scalar functional limit
  `ell(log(ell)^8+28log(ell)^6-112log(ell)^5+630log(ell)^4-
  2464log(ell)^3+7420log(ell)^2-14832log(ell)+14833)`.
- a discrete Abel estimate for the log-eighth resolvent weight, whose endpoint
  grows as `O(log(M)^6)`, together with `log(M)^6/A_M(z) → 0`;
- elimination of the complete centered eighth-power periodic residue,
  including the five critical mixed terms `μ_M log^7`, `μ_M^2 log^6`,
  `μ_M^3 log^5`, `μ_M^4 log^4` and `μ_M^5 log^3`, and every fixed literal
  boundary;
- convergence of the complete eighth coefficient covariance, direct product
  and every compatible return-metric family to `eighthCenteredMomentMatrix`,
  with exact six-camera target `sixCameraEighthCenteredMoment`.
- the general recurrence `P_0=1`, `P_k=(1+X)^k-kP_(k-1)` as a single
  polynomial family, with every `P_k` monic of natural degree exactly `k`;
- the all-degree algebraic camera target
  `M_k(i,j)=G(i,j)P_k(log(ell(i,j)))`, Hermitian and self-adjoint for every
  finite camera family;
- exact recovery of the previously checked degree-zero through degree-eight
  moment matrices and one literal self-adjoint six-camera matrix for every
  degree `k`.
- Hilbert-space linear relations represented as submodules of `H × H`, with
  the documented skew-Hermitian Green form
  `omega((f,f'),(g,g')) = inner f' g - inner f g'`;
- the exact symplectic orthogonal as Mathlib's submodule adjoint, formal
  Green-isotropy and maximal Green-isotropy, and the Weyl/impedance rotation
  `(Gamma_0,Gamma_1) ↦ (-Gamma_1,Gamma_0)` preserving the Green form;
- for every densely defined `LinearPMap`, equality of the Green adjoint of its
  graph with the graph of its Hilbert-space adjoint, so graph maximality is
  equivalent to self-adjointness;
- the graph of maximal multiplication by `1+log x` as a concrete closed
  maximal Green relation satisfying the exact Green identity;
- the actual source-extended relation
  `T_C = {(f, Y f + V u) | f in dom(Y), u in CameraHilbert}`, with uniqueness
  of `(f,u)` supplied by injectivity of the all-bases Naimark port;
- honest reference and Weyl boundary charts
  `Gamma_H = (u,-V^*f)` and `Gamma_W = (V^*f,u)`, related by the exact
  symplectic quarter-turn;
- the abstract and concrete Green identities for both charts, and maximal
  coupled Green-isotropy of the Weyl boundary graph whenever `Y` is
  self-adjoint, instantiated with maximal logarithmic multiplication and the
  all-bases Naimark isometry;
- the explicit real `2 × 2` ambient Naimark resolvent, whose compression by
  the realified port and adjoint is exactly the complete Cauchy block;
- exact maximal-domain membership of both resolvent components and the
  two-sided inverse laws for `lambda-Y`, proving the operator bijective for
  every nonreal `lambda` without postulating a separate complex scalar action;
- the injective source gamma map `u ↦ (lambda-Y)⁻¹Vu`, its exact defect
  equation and uniqueness among all maximal-domain solutions;
- the source boundary identities `Gamma_0=M_infinity(lambda)u` and
  `Gamma_1=u`, followed by trace reparametrization on the exact dense Cauchy
  range;
- the checked boundary law
  `Gamma_1 gamma(lambda)xi=M_infinity(lambda)⁻¹xi`, with the boundary Weyl
  family equal to the existing closed, densely defined and non-norm-bounded
  `LinearPMap` inverse;
- a generic external Green-camera coupling whose only new analytic datum is
  an explicitly supplied bounded real-linear state readout into the realified
  all-bases camera space;
- canonical external synthesis followed by that readout, with the exact
  operator identity `cameraPort ∘ normalizedExternal = stateReadout`;
- the separate joint output `(cameraPort, staticPoisson)`, recovering on every
  coherent state both the camera readout and the normalized Green bulk without
  identifying the static Poisson component with the spectral Weyl family;
- pullback of the source gamma field along the external camera port, producing
  defect states in the exact carry defect subspace and the unique solutions of
  the maximal-domain defect equation;
- induced Cauchy traces in the exact Weyl domain, with the kernel-checked laws
  `gamma(trace(e)) = gammaSource(cameraPort(e))` and
  `W(lambda)(trace(e)) = cameraPort(e)`, plus a specialization to the pinned
  concrete Green analysis operator and its exact split bounds;
- an `AngularGreenCameraCoupling` that adds a supplied state-valued family
  `t ↦ x(t)` without silently assuming a unitary group law, continuity or a
  rigged-state realization;
- exact coherent angular evaluation of the external camera port, static bulk,
  source gamma vector and dense-domain Cauchy trace, including the defect
  equation and uniqueness on the maximal logarithmic domain;
- the angular Weyl law
  `W(lambda)(trace(t,lambda)) = stateReadout(x(t))` for every real `t` and
  every independently chosen nonreal `lambda`, together with equivalent
  gamma/Weyl zero tests;
- explicit probe independence: arbitrary nonreal `z0` and `lambda` recover
  the same angular readout and zero test, with no equality among `t`, `z0`
  and `lambda`;
- the exact obstruction to an unweighted critical state:
  `Complex.normSq (n⁻¹ᐟ²) = n⁻¹`, hence the raw native amplitude is not in
  `ℓ²(PNat, ℂ)`;
- summability of the logarithmically rigged energy
  `n⁻¹/(1+log n)²` and construction of its distinguished `LogRiggedState`;
- the diagonal logarithmic evolution
  `U(t)x(n)=exp(-it log n)x(n)` as a strongly continuous group of
  complex-linear isometric equivalences, with exact group, inverse and norm
  laws;
- constant norm and continuity of the distinguished critical orbit, together
  with the exact pointwise bridge obtained by removing the rigging weight:
  `unriggedCoordinate (criticalRiggedOrbit t) n =
  dirichletValue (nativeLine t) n`.
- the bounded injective rigging map `Jx(n)=x(n)/(1+log n)`, with dense range,
  and its inverse as multiplication by `1+log n` on the explicit maximal
  square-summability domain;
- density and properness of that domain, exact coordinate and two-sided
  inverse laws, surjectivity, closedness, closability, self-adjointness and
  equality with the canonical graph closure;
- invariance of the maximal domain under the logarithmic angular evolution
  and exact intertwining of evolution with unrigging;
- formal exclusion of every critical-orbit vector from the unrigging domain,
  consistently with the harmonic obstruction;
- the everywhere-defined Fréchet--Riesz anti-linear isometric equivalence from
  the `H₋₁` coordinate realization into the strong dual of the corresponding
  `H₁` test-coordinate realization, carrying the critical orbit to a
  continuous constant-norm dual orbit.

The finite functional algebra is now kernel checked through arbitrary real
polynomials.  The camera/resolvent construction is fully concrete; the
return-metric theorem is parametrized by a finite colligation family satisfying
the explicit identities `P_M E_M = B_M` and
`E_MᴴE_M + B_MᴴB_M = I`.  Instantiating those matrices from an additional
upstream Green model is therefore a separate integration step, not a hidden
premise.  The logarithmic centering asymptotic, the first eight scalar weighted
moments at cutoffs `ell * M`, and the complete linear through eighth-power
functional covariance limits are now kernel checked.  The next analytic gate
is to lift the scalar and periodic-residue arguments to a degree-generic
induction over the new polynomial hierarchy.  The algebraic all-degree targets
are complete, but analytic convergence beyond degree eight is not yet claimed.
Independently, Phase 5 has passed its unbounded-Weyl gate: the canonical
strictly positive Gram form on `Finsupp` now generates its intrinsic real
inner product, and the all-bases camera Hilbert space is its canonical
completion.  Every finite-label level enters isometrically and compatibly,
and their union is dense.  This is not the standard unweighted camera `l2`
space.  Separately, the periodic kernel `m_bc` now has its canonical complete
Kolmogorov realization `K₀`; its vectors `r_b` recover `m_bc` exactly and
generate densely.  The slope-minimum factor is now realized by explicit
positive-half-line indicator vectors, and their finite map extends
isometrically from the intrinsic camera completion into `L²((0,∞),K₀)`.
Multiplication by `1+log x` is now defined on its exact maximal `L²` domain;
that domain is dense, contains the complete finite camera core, and equals
the domain of the Hilbert-space adjoint.  The maximal multiplier equals its
adjoint, is self-adjoint and closed, and its canonical graph closure does not
enlarge it.  Direct bounded multiplication by the real and imaginary parts of
`(lambda-y)⁻¹`, followed by Naimark compression, now gives the all-bases
Cauchy family for every nonreal `lambda`.  Its components are self-adjoint,
obey the sharp resolvent-scale bounds and conjugate symmetry, and its
imaginary component has strict anti-Herglotz sign, is injective and has dense
range.  On the underlying real Hilbert space of the canonical
complexification, the standard `2 × 2` block combines those components into
the full Cauchy operator.  Its strict skew-form sign proves injectivity, and
its adjoint is the block at the conjugate parameter, proving dense range.
The inverse on that exact range is now a closed densely defined Mathlib
`LinearPMap` satisfying both inverse laws and surjecting onto the full
realified complexification.  Centering each normalized camera interval at
`log ell` has exact variance one.  Resolvent-shift identities turn this into
an explicit scalar bound that vanishes along camera labels `3,4,5,...`; the
resulting unit vectors have Cauchy images converging to zero.  Thus the block
is not bounded below and its closed densely defined inverse admits no global
norm bound.  Phase 6 now contains both the abstract Green-relation API and the
actual source-extended all-bases relation `{(f,Yf+Vu)}`.  The injective
Naimark port gives unique source coordinates; the reference/Weyl charts,
their rotation and Green identities, and maximality of the coupled Weyl graph
are all kernel checked.  The canonical realification now also supplies the
ambient resolvent, unique defect solutions, source and trace gamma fields and
the exact compressed-resolvent/Weyl identification.  The external Green/camera
interface is now kernel checked for every explicitly supplied bounded state
readout, including canonical external synthesis, the separate static Poisson
output and transport through the defect and Weyl families.  Its angular
evaluation is also checked for every supplied state-valued family: `t` stays
in the state family and each nonreal spectral probe stays in its own
Cauchy/Weyl trace.  Separately, the critical native amplitude now has its
canonical logarithmically weighted coordinate realization and a strongly
continuous isometric orbit.  Its canonical unrigging is the closed
self-adjoint maximal multiplier on the exact proper dense domain.  Lean proves
that the whole critical orbit lies outside that domain, while the canonical
strong-dual port contains it continuously.  What remains is not operator
closure for this diagonal map, but construction of the research-specific
Green/Haar-to-all-bases camera synthesis and proof that its output agrees with
the existing bounded-readout interface.  A native complex
scalar action on the real all-bases camera completion, explicit PVM and
ordinary boundary triple also remain outside the current surface.

Pinned foundations:

- Lean `4.32.0`;
- Mathlib `v4.32.0`, inherited through the pinned dependencies;
- Green Frame commit `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`
  (`v2.1.0`);
- Finite Native Carry Operator commit
  `00e9d6beb17226545abf5ddf90bbfede6c7146b0` (`v0.1.0`).

## Intended theorem boundary

The formalization proceeds from exact camera arithmetic to finite spectral
objects, then to the countable camera completion, Cauchy transform and closed
unbounded Weyl inverse.  Those gates are now complete.  The abstract relation,
Green-form, self-adjoint graph-maximality, source-extended relation and maximal
coupled Weyl boundary graph are also complete.  The realified gamma field and
the exact identification of its Weyl family with the compressed-resolvent
inverse are now complete as well.  The external Green state/port coupling and
its angular evaluation theorem are complete when parameterized by an explicit
bounded state readout and a supplied state-valued family; the concrete Green
split specialization is also exported.  The logarithmic `H₋₁` coordinate
realization, its strongly continuous orbit `exp(-it log n)`, the canonical
strong-dual port and the closed self-adjoint maximal unrigging operator are now
constructed independently.  No subsequent boundary gate is selected by this
milestone.  The remaining research problem is the separate, typed
Green/Haar-to-all-bases camera synthesis; it cannot be obtained by applying
maximal unrigging to the critical orbit, which is formally outside that
operator's domain.

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
- `docs/20_POST_RIGGED_PORT_CONCEPTUAL_AUDIT.md`: post-v0.53 separation of
  genuinely new mathematical structure from formalization/consolidation;
- `research/SOURCE_CATALOG.md`: source inventory and provenance findings;
- `audit/theorem-registry.json`: ordered registry of all 1,318 public theorems;
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
