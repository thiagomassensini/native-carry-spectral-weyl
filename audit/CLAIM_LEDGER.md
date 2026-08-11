# Claim ledger

The machine-readable ledger is `audit/claim-ledger.json`.  At v0.29 it contains
forty-one `KERNEL_CHECKED` claims covering finite-camera geometry, exact
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
`ell(log(ell)^5+10log(ell)^3-20log(ell)^2+45log(ell)-44)`.  The quintic
periodic residue and literal boundary are the next coefficient-covariance
obligations.

No projection-valued measure, infinite camera completion or Weyl inverse is
claimed by this milestone.  Positivity and normalization of the finite POVM
do not imply idempotent spectral effects.
