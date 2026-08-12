# Claim ledger

The machine-readable ledger is `audit/claim-ledger.json`.  At v0.51 it contains
sixty-five `KERNEL_CHECKED` claims covering finite-camera geometry, exact
periodic profiles, period mean zero, explicit camera factors and the uniform positive
native-line floor, plus the exact free-coefficient realization of the finite
operator, the complete aligned-C2 finite/profile coefficient identity, and the
complete odd/even natural-camera identities with the final even antipodal
correction.  It also covers absolute and normal bracket convergence,
holomorphy, the exact bracket/profile bridge on `re s > 1`, analytic
continuation of the cross identity, native-scalar factorization and the common
native-line zero set.  The quantitative-tail claims cover the explicit `M^-3/2`
characteristic and stable cross-residual tails, termwise first differentiation,
the actual native-line first-derivative rate `M^-3/2 log M`, and all fixed-order
complex and native-line derivative rates `M^-3/2 log(M)^k` obtained from a
dynamic-radius Cauchy estimate.  The zero-multiplicity claim proves that the nonvanishing
camera factors are local analytic units, so every supported characteristic has
the same analytic order of vanishing at every native-line point.  The two new
claims formalize the real/complex analytic-order bridge and the five limiting
modal energies: their positive weights, nonnegativity, common native-scalar
zero set, and exact real order `2m` for an amplitude zero of complex order `m`,
including the canonical rank-two mode-4 aggregate with binary defect factor
`1 - 2^(1-s)` and the corresponding mixed product with `A_3`.
The finite-Gram claim adds common-period product means, positivity of the
slope-minimum and weighted Gram kernels for every finite camera family, and the
exact positive-definite period-`420` matrix for cameras `2,...,7`, including
its determinant `4_981_760`.
The first all-bases claim defines the countable camera index and its canonical
pair-period mean, proves that every positive larger common period gives the
same value, identifies every finite principal restriction with the existing
finite periodic Gram matrix, checks the exceptional C2/C4 mean block and its
determinant `2`, and proves strict positivity of both every finite principal
matrix and the induced Gram form on finitely supported coefficients.
The second all-bases claim equips that `Finsupp` space with the intrinsic real
Gram inner product, takes its canonical complete Hilbert-space completion,
proves the completion embedding is isometric and dense, recovers the exact
Gram kernel as inner products of canonical camera vectors, and proves the
compatible finite-label levels have dense union.
The third all-bases claim constructs the canonical Kolmogorov realization of
the periodic kernel `m_bc`.  It identifies every finite restriction with the
finite periodic-mean matrix, proves positive semidefiniteness, builds the
intrinsic pre-inner-product completion `K₀`, and supplies canonical vectors
`r_b` with exact kernel inner products and dense algebraic span.
The fourth all-bases claim constructs the explicit Naimark isometry.  It uses
Lebesgue measure on `(0,∞)` and the vectors `1_(0,ell_b] r_b` in
`L²((0,∞),K₀)`, proves their almost-everywhere indicator formula and exact
full-Gram inner products, and extends their finite linear-combination map from
the intrinsic `Finsupp` core to a norm- and inner-product-preserving linear
isometry on the complete camera Hilbert space.
The fifth all-bases claim constructs multiplication by the documented
coordinate `1 + log x` as a `LinearPMap` on its exact maximal `L²` domain.
Every camera indicator and the finite camera core lie in that domain.  The
bounded positive regularizer `(1+|1+log x|)⁻¹` has symmetric dense range
inside it, proving the domain dense; the logarithmic operator is symmetric and
closable, and its canonical graph closure is closed.  The claim deliberately
does not identify the original operator with its adjoint.
The sixth all-bases claim closes that maximality gate.  Composing the positive
regularizer with logarithmic multiplication gives the bounded real transfer
multiplier `y/(1+|y|)`.  Testing the adjoint identity on those regularized
vectors yields `(yR)g = R(Y†g)`; strict positivity of `R` then gives the
literal almost-everywhere adjoint action.  Thus the adjoint domain equals the
natural maximal multiplication domain, `Y†=Y`, and the operator is
self-adjoint and closed.  Its canonical graph closure is exactly `Y`.
The seventh all-bases claim constructs the compressed Cauchy family for every
nonreal `lambda`.  On the real Naimark model it bundles the real and imaginary
parts of `(lambda-y)⁻¹` as bounded self-adjoint multiplication operators,
checks the exact scalar inverse and modulus identities, proves the
`|Im lambda|⁻¹` bounds and conjugation laws, and compresses through the
all-bases Naimark isometry.  The resulting real two-component representation
of `V†(lambda-Y)⁻¹V` is self-adjoint componentwise, has strict anti-Herglotz
sign, and its imaginary component is injective with dense range.  No separate
complexification, explicit PVM or unbounded Weyl inverse is claimed.
The eighth all-bases claim passes to the underlying real Hilbert space
`WithLp 2 (CameraHilbert × CameraHilbert)` of the canonical complexification.
It combines the two components into the standard block
`(x,y) ↦ (Ax-By,Bx+Ay)`, proves the exact skew quadratic-form identity and
identifies the adjoint with the block at the conjugate parameter.  The strict
anti-Herglotz sign makes the full block injective, while injectivity of its
adjoint makes its range dense.
The ninth all-bases claim defines the inverse of that full block on its exact
range as a Mathlib `LinearPMap`.  Its domain is dense, its graph is the
coordinate swap of the closed bounded Cauchy graph and is therefore closed,
both inverse laws hold exactly, and its range is the whole realified
complexification.  Unboundedness of this closed densely defined inverse is
not part of that claim; it is discharged by the next claim.
The tenth all-bases claim closes that quantitative gate.  On `(0,ell]`, the
coordinate `1+log x` centered at `log ell` has exact variance one after camera
normalization.  The real and imaginary resolvent-shift identities give an
explicit complete-block bound proportional to
`abs(Re (lambda-log ell)⁻¹)+abs(Im (lambda-log ell)⁻¹)`, and that bound tends
to zero along camera labels `3,4,5,...`.  These cameras yield explicit unit
vectors with Cauchy images converging to zero.  Hence the block is not bounded
below and its closed densely defined `LinearPMap` inverse has no global norm
bound on its domain.
The first boundary claim opens Phase 6 with an abstract relation layer over
real or complex Hilbert spaces.  Linear relations are product submodules, the
documented Green form is skew-Hermitian, and the Weyl/impedance quarter-turn
preserves it.  Mathlib's submodule adjoint is exactly the Green symplectic
orthogonal.  For densely defined partial operators, graph isotropy is formal
symmetry and graph maximality is self-adjointness.  Thus the maximal
logarithmic multiplier has a concrete closed maximal Green graph.  This claim
does not yet add the source term `V u`, a gamma field, or the boundary-Weyl
identification.
The finite-moments claim adds the generic self-adjoint shared-slope moment
construction, the exact first and second centered logarithmic formulas, and
their literal period-`420` matrices for cameras `2,...,7`.
The finite-whitening claim adds the canonical positive inverse square root,
exact Gram normalization, congruence preservation, whitened first and second
moments, the exact variance/Schur-complement identity, conditional variance
positivity from the moment block, and the canonical self-adjoint six-camera
operators.
The step-density claim evaluates the singular centered-logarithmic integrals,
realizes the two-level slope moment block as an integral Gram matrix, combines
it with the repeated periodic mean by the Schur product theorem, and proves
the exact six-camera moment block and variance positive semidefinite.
The finite-POVM claim realizes `D(x) M₀ D(x) dx` as a positive matrix-valued
measure with total mass `G`, normalizes it by `G⁻¹/²` to total mass `I`, and
pushes it forward under `y = 1 + log x`.  The canonical six-camera
centered-log measure is therefore a positive normalized POVM.
The first two limit claims prove ordinary and Dirichlet--Abel weighted means
for vector-valued periodic sequences, including stability under a finite
nonmonotone prefix, then lift them to the genuine pairwise camera cutoff.  The
new resolvent-limit claim proves that `|z-log(n+1)|^-2` is positive, decays,
becomes antitone, has mass asymptotic to `M/log(M+1)^2`, and is regularly
varying with index one.  It therefore instantiates the finite covariance norm
limit, including the exact six-camera matrix.
The finite-defect covariance claim closes the next bridge: the endpoint return
metric cancels exactly under the finite Poisson and Pythagorean identities;
the complete literal camera stencils form a common-window matrix whose direct
diagonal-resolvent covariance equals the finite coefficient formula; and its
fixed-width seed/endpoint boundary vanishes.  Thus the literal covariance, the
direct matrix product and every compatible cutoff-indexed return-metric
colligation family converge in matrix norm, with the six-camera target exactly
the complexification of `sixCameraGram`.
The finite-functional claim inserts an arbitrary real spectral multiplier in
one probe leg, proves exact return-metric cancellation and identifies the
result with the complete literal finite coefficient sum.  It specializes this
identity to every real polynomial centered at the finite logarithmic mean
`μ_M(z)`, proves constant-polynomial compatibility with the order-zero layer,
and transfers any future coefficient-sum limit to both matrix realizations.
It does not claim the analytic polynomial moment limit itself.
The logarithmic-mean claim now proves `μ_M(z) - log M -> -1` from an exact
telescoping identity and the previously established resolvent mass asymptotic.
The first scalar-moment claim proves fixed-displacement endpoint slow
variation and the normalized first functional limit at every positive natural
cutoff multiplier `ell`, both centered at `log M` and at `μ_M(z)`.
The linear functional-covariance claim then eliminates the zero-mean periodic
residue using bounded Dirichlet sums for `w_z` and `log(n+1)w_z`, proves every
fixed literal seed/endpoint boundary vanishes, and obtains the full first
moment in coefficient, direct-product and return-metric forms.  Its six-camera
target is exactly the complexification of `sixCameraFirstMoment`.
The second scalar-moment claim proves the exact quadratic cutoff recurrence,
sums its little-o increment and obtains both the raw limit
`ell(log(ell)^2-2log(ell)+2)` and the documented centered limit
`ell(1+log(ell)^2)`.
The quadratic functional-covariance claim proves the required log-squared
Dirichlet boundedness, eliminates the quadratic periodic residue and literal
boundary, and obtains the complete second centered moment in coefficient,
direct-product and return-metric forms.  Its six-camera target is exactly the
complexification of `sixCameraSecondCenteredMoment`.
The third scalar-moment claim proves the exact cubic cutoff recurrence, shows
that its squared-step first-moment and cubic-step mass corrections vanish,
sums the resulting little-o increment and obtains the raw limit
`ell(log(ell)^3-3log(ell)^2+6log(ell)-6)`.  Shifting from `log M` to `μ_M(z)`
gives the documented centered limit `ell(log(ell)^3+3log(ell)-2)`.
The cubic functional-covariance claim then proves a discrete Abel estimate for
the unbounded weight `log(n+1)^3 w_z(n)`, whose periodic residue is
`O(log M)` and hence negligible relative to `A_M(z)`.  It eliminates that
residue and every fixed literal seed/endpoint boundary, obtaining the complete
third centered moment in coefficient, direct-product and return-metric forms.
Its six-camera target is exactly the complexification of
`sixCameraThirdCenteredMoment`.
The fourth scalar-moment claim proves the exact quartic cutoff recurrence,
shows that its squared-step quadratic, cubed-step linear and fourth-step mass
corrections vanish, and sums the resulting little-o increment to obtain the
raw limit
`ell(log(ell)^4-4log(ell)^3+12log(ell)^2-24log(ell)+24)`.  Shifting from
`log M` to `μ_M(z)` gives the documented centered limit
`ell(log(ell)^4+6log(ell)^2-8log(ell)+9)`.
The quartic functional-covariance claim proves slow variation of the
logarithmic mean under positive natural dilation and applies discrete Abel
summation to the log-fourth resolvent weight, whose endpoint grows as
`O(log(M)^2)` and is negligible relative to `A_M(z)`.  It eliminates all five
terms in the centered quartic periodic residue and every fixed literal
seed/corrected-endpoint boundary.  The complete coefficient covariance, direct
functional product and every compatible return-metric colligation converge to
`L_bc = G_bc(log(min(ell_b,ell_c))^4 + 6log(min(ell_b,ell_c))^2 -
8log(min(ell_b,ell_c)) + 9)`.  Its six-camera target is exactly the
complexification of `sixCameraFourthCenteredMoment`.
The fifth scalar-moment claim proves the exact quintic cutoff recurrence,
shows that all corrections beyond the logarithmic step times the raw fourth
moment vanish at endpoint-weight scale, and sums the resulting little-o
increment to obtain
`ell(log(ell)^5-5log(ell)^4+20log(ell)^3-60log(ell)^2+
120log(ell)-120)`.  Shifting from `log M` to `μ_M(z)` gives the documented
centered limit
`ell(log(ell)^5+10log(ell)^3-20log(ell)^2+45log(ell)-44)`.
The quintic functional-covariance claim controls the log-fifth periodic
weight, eliminates its two new mixed terms and literal boundary, and obtains
the complete fifth centered covariance in coefficient, direct-product and
return-metric forms.
The sixth scalar-moment claim proves the exact sextic cutoff recurrence and
the centered limit
`ell(log(ell)^6+15log(ell)^4-40log(ell)^3+135log(ell)^2-
264log(ell)+265)`.
The sextic functional-covariance claim applies discrete Abel summation to the
log-sixth weight, closes the three critical mixed terms
`μ_M log^5`, `μ_M^2 log^4` and `μ_M^3 log^3`, and eliminates every fixed
literal boundary.  The complete sixth covariance follows in coefficient,
direct-product and return-metric forms, with exact six-camera target
`sixCameraSixthCenteredMoment`.
The seventh scalar-moment claim proves the exact seventh-power cutoff
recurrence, shows that only the logarithmic step times the raw sixth moment
survives at endpoint-weight scale, and derives the centered limit
`ell(log(ell)^7+21log(ell)^5-70log(ell)^4+315log(ell)^3-
924log(ell)^2+1855log(ell)-1854)`.  The seventh periodic residue and literal
boundary are then eliminated by the seventh functional-covariance claim.
Discrete Abel summation controls the log-seventh weight and closes the four
critical mixed terms `μ_M log^6`, `μ_M^2 log^5`, `μ_M^3 log^4` and
`μ_M^4 log^3`.  The complete seventh covariance follows in coefficient,
direct-product and return-metric forms, with exact six-camera target
`sixCameraSeventhCenteredMoment`.
The eighth scalar-moment claim continues the exact recurrence with binomial
coefficients `-8`, `28`, `-56`, `70`, `-56`, `28`, `-8`, `1`.  It proves the
raw limit
`ell(log(ell)^8-8log(ell)^7+56log(ell)^6-336log(ell)^5+
1680log(ell)^4-6720log(ell)^3+20160log(ell)^2-40320log(ell)+40320)`
and the weighted-mean-centered limit
`ell(log(ell)^8+28log(ell)^6-112log(ell)^5+630log(ell)^4-
2464log(ell)^3+7420log(ell)^2-14832log(ell)+14833)`.  The eighth periodic
residue and literal boundary are then eliminated by the eighth
functional-covariance claim.  Discrete Abel summation controls the log-eighth
weight and closes the five critical mixed terms `μ_M log^7`, `μ_M^2 log^6`,
`μ_M^3 log^5`, `μ_M^4 log^4` and `μ_M^5 log^3`.  The complete eighth
covariance follows in coefficient, direct-product and return-metric forms,
with exact six-camera target `sixCameraEighthCenteredMoment`.
The general moment-hierarchy claim packages the documented recurrence
`P_0=1`, `P_k=(1+X)^k-kP_(k-1)` for every natural degree, proves that `P_k` is
monic of degree `k`, and defines the self-adjoint algebraic camera target
`G_bc P_k(log(ell_bc))`.  It recovers all concrete targets through degree
eight and gives one exact literal six-camera matrix in every degree.  It does
not promote the degree-at-most-eight analytic limits to arbitrary degree.

No explicit all-bases PVM or separate complex-linear realization is claimed
by this milestone.  The compressed Cauchy family is represented by its
canonical real block because the established camera Hilbert space is real.
Positivity and normalization of the finite POVM do not imply idempotent
spectral effects.

The second boundary claim constructs the actual source-extended relation
`T_C={(f,Yf+Vu)}`.  Injectivity of the port gives unique source coordinates,
so the reference chart `(u,-V^*f)` and Weyl chart `(V^*f,u)` are well-defined
linear maps and differ by the exact symplectic quarter-turn.  Formal symmetry
gives the Green identity in both charts, while self-adjointness makes the
coupled Weyl graph equal to its coupled Green adjoint.  The concrete instance
uses maximal logarithmic multiplication and the all-bases Naimark isometry.
The spectral-parameter-dependent gamma field and compressed-resolvent/Weyl
identification remain outside this second claim and are supplied by the next
two claims.

The eleventh all-bases claim constructs the explicit ambient realification
needed by the gamma field.  The real and imaginary parts of the Naimark port,
its adjoint and `(lambda-Y)⁻¹` are assembled into rectangular `2 × 2` real
blocks, and compression of the ambient resolvent is proved exactly equal to
`M_infinity(lambda)`.  Both resolvent components lie in the maximal domain of
`Y`; the imaginary-part energy identity makes `lambda-Y` injective off the
real axis, while the explicit domain-valued resolvent proves surjectivity and
both inverse laws.  Thus `lambda-Y` is bijective on its exact maximal domain.

The third boundary claim constructs the realified source gamma map
`u ↦ (lambda-Y)⁻¹Vu`, proves it injective and proves that it is the unique
maximal-domain solution of `lambda f=Yf+Vu`.  Its boundary values are exactly
`Gamma_0=M_infinity(lambda)u` and `Gamma_1=u`.  Reparametrizing by `Gamma_0`
on the dense range of `M_infinity(lambda)` gives the partial trace gamma field
and the checked law
`Gamma_1 gamma(lambda)xi=M_infinity(lambda)⁻¹xi`.  The resulting Weyl family
is the existing closed, densely defined `LinearPMap` inverse and admits no
global norm bound.  This claim does not introduce an everywhere-defined
inverse, an independent complex-linear realization, or an ordinary boundary
triple.

The fourth boundary claim adds the external Green-to-camera interface.  For
an arbitrary complex Green split with certified lower frame bounds, it takes
one bounded real-linear state readout as explicit analytic input.  Canonical
ambient external synthesis then induces a camera port satisfying the exact
coherent-state identity, while the independent static Poisson component
recovers the normalized Green bulk.  Pulling the port through the source gamma
field gives defect states in the exact carry defect subspace and unique
maximal-domain solutions.  Their induced Cauchy traces lie in the exact Weyl
domain and satisfy `W(lambda)(trace(e))=cameraPort(e)`.  The concrete
specialization fills the split certificate from the pinned GreenFrame theorem.
Neither existence of the research-specific bounded state readout nor equality
of static Poisson and spectral Weyl is claimed.

The fifth boundary claim evaluates that interface along a supplied
state-valued angular family `t ↦ x(t)`.  Coherent external synthesis recovers
both `stateReadout(x(t))` and the independent normalized bulk.  For every
nonreal `lambda`, the source gamma vector is the unique maximal-domain solution
of its exact defect equation, and its exact-domain Cauchy trace satisfies
`W(lambda)(trace(t,lambda))=stateReadout(x(t))`.  Both gamma and Weyl vanishing
are equivalent to vanishing of that readout.  Any two nonreal probes
`z0` and `lambda` therefore give the same recovered value and zero test without
being identified with each other or with `t`.  The claim supplies no unitary
orbit law, rigged-state realization or construction/boundedness proof for the
research-specific readout.
