# Scope and trust boundary

This document fixes the intended semantic boundary of the Native Carry
Spectral Weyl formalization.  It is a plan, not mathematical evidence.

## Upstream interfaces

The project consumes two independently versioned Lean packages:

1. `GreenFrame` supplies the all-bases state space, canonical Parseval
   normalization, external/bulk split, static Poisson operator and their finite
   strong limits.
2. `FiniteNativeCarryOperator` supplies the finite real-plane native state,
   camera geometry and finite camera resultants.

The static Green Poisson map is not renamed as a Weyl family.  A Weyl layer
must additionally construct a spectral generator, its resolvent or Cauchy
transform, the correct domain of any inverse, and the appropriate boundary
relation.

## Evidence levels

Every claim belongs to exactly one level:

- `KERNEL_CHECKED`: cited public Lean declarations prove the claim at the
  audited release SHA;
- `CONDITIONAL`: Lean theorem with explicit hypotheses still awaiting a
  concrete discharge;
- `SOURCE_DERIVATION`: mathematical argument preserved in research notes but
  not yet formalized;
- `NUMERICAL_AUDIT`: finite or floating-point evidence only;
- `OPEN`: a stated mathematical obligation;
- `FUTURE_LAYER`: deliberately outside the current release.

Words such as “closed”, “constructed” or “proved” in a research note do not
promote a claim above `SOURCE_DERIVATION` or `NUMERICAL_AUDIT`.

## Permanent firewalls

- Markdown, Python, JSON and numerical tolerances are never Lean premises.
- `t`, `z0` and `lambda` are separate parameters.
- Finite-dimensional invertibility does not imply a bounded inverse on the
  all-bases completion.
- Operator-norm, strong, strong-star, strong-resolvent and strong-graph
  convergence are never interchanged without a theorem.
- A positive operator-valued measure is not silently upgraded to a projection-
  valued measure.
- A maximal isotropic finite relation is not automatically the adjoint of a
  densely defined infinite symmetric operator.
- Closedness of an inverse is not boundedness of that inverse.

## Initial target

The first theorem milestone is intentionally finite and arithmetic:

1. classify every native periodic camera profile;
2. prove the mean-zero identities and exact camera factors;
3. prove the uniform nonvanishing floor on the native line;
4. define the periodic mean kernel and prove finite-support positivity;
5. recover the exact finite Gram for cameras `2,...,7`.

The scalar common-zero-set theorem is admitted to the release surface only
after normal convergence, analytic continuation and factor nonvanishing are
kernel checked.  The v0.9 surface additionally admits equality of local zero
multiplicities only through Mathlib's analytic order and an explicit proof that
each nonvanishing camera factor has local order zero.

The v0.10 surface admits the five limiting scalar-sector energies only after
separating complex analytic amplitude order from real analytic energy order.
Restriction to the native line is proved through its complex-affine extension
with derivative `I`; `Complex.normSq` is then proved to double every finite
order, and each explicit positive modal weight is proved not to alter it.  The
canonical mode-4 formula is the aggregate of the rank-two sector, not a claim
that either leg is a separate eigenspace.

The v0.11 surface admits the finite periodic Gram layer.  Its positivity is
proved directly from rank-one decompositions of the periodic product mean and
the slope-minimum kernel, followed by the Schur product theorem.  For cameras
`2,...,7`, period `420`, the exact rational matrix and determinant are checked
inside Lean; Python output is not used as a premise.  Positive definiteness of
this six-camera matrix does not by itself construct whitening or a POVM.

The v0.12 surface admits the unwhitened first and second centered logarithmic
moments only through their exact shared-slope formulas over the periodic Gram.
Their Hermitian and self-adjoint character is kernel checked for every finite
camera package, and the literal six-camera matrices are recovered at period
`420`.  This does not identify `G⁻¹/²`, prove positivity of the whitened
variance, or construct a normalized operator-valued measure.

The v0.13 surface constructs the canonical positive inverse square root for
every positive-definite finite Gram matrix and proves the exact identities
`R² = G⁻¹` and `R G R = I`.  It defines the whitened first and second moments,
the variance `V = M₂ - L²`, and proves
`V = R (J - H G⁻¹ H) R`.  Positivity of `V` is kernel checked from positivity
of the moment block, equivalently its Schur complement.  The concrete
six-camera operators are instantiated and self-adjoint, but positivity of the
concrete variance remains conditional until the continuous step-density
realization of the moment block is formalized.  No finite POVM or spectral
projector is inferred from whitening alone.

The v0.14 surface supplies that missing continuous realization.  It evaluates
the first two centered logarithmic moments at the singular endpoint, realizes
the two-level slope block as the integral Gram matrix of the truncated
features `1` and `1 + log x`, and proves its positive semidefiniteness by
integrating a square.  The full camera moment block is exactly its Hadamard
product with the repeated periodic product-mean block, so the exact
period-`420` six-camera block and canonical variance are now positive
semidefinite without a conditional hypothesis.  This still does not define a
normalized finite POVM, spectral projectors or a Cauchy/Weyl transform.

The v0.15 surface constructs the normalized finite POVM.  It represents the
continuous density `D(x) M₀ D(x) dx` as a Bochner-integrated vector measure,
proves positive semidefiniteness of every measurable effect and proves exact
total mass `G`.  Continuous congruence by `G⁻¹/²` then gives total effect `I`;
pushforward by `x ↦ 1 + log x` supplies the centered-log spectral coordinate.
The canonical period-`420` six-camera POVM is instantiated and proved positive
and normalized.  This is an operator-valued measure, not a projection-valued
measure: no idempotence, spectral projector, Cauchy transform or Weyl family is
inferred from normalization.

The scalar surface additionally admits quantitative cutoff claims only
after the centered block identity is retained through the norm estimate.  In
particular, the first native-line derivative tail is proved by differentiating
the centered bracket before taking norms; no three-leg termwise estimate or
numerical slope is used as a Lean premise.  Every higher fixed-order derivative
tail is then proved from a uniform order-zero estimate on a Cauchy circle of
radius `1 / log M`; no numerical derivative fit is used as a Lean premise.

The v0.16--v0.18 surface proves the periodic, concrete-resolvent and literal
finite-defect covariance limits.  The return-metric realization is universal
over finite colligation families satisfying the displayed Poisson and
Pythagorean identities; it does not claim that an additional upstream Green
model has been instantiated inside this repository.

The v0.19 surface adds the exact finite functional layer.  An arbitrary real
spectral multiplier in one probe leg cancels through the return metric and is
identified with the complete literal coefficient sum.  Every real polynomial
in the finite centered logarithmic coordinate is included, and conditional
transfer theorems reduce both matrix realizations to convergence of that sum.
This surface does not claim the remaining asymptotic
`μ_M(z) - log M -> -1`, the polynomial moment limit, locally uniform Cauchy
transform convergence, or any operator-valued Weyl inverse.

The v0.20 surface proves that previously open logarithmic-mean asymptotic.  It
uses an exact discrete telescoping identity and the already checked resolvent
mass equivalence, not a numerical fit or an unformalized Riemann-sum premise.

The v0.21 surface proves the first scalar weighted functional moment at every
fixed positive natural cutoff multiplier `ell`.  Fixed displaced endpoint
weights and logarithms are controlled directly, and an exact increment plus
little-o summation gives the limits `ell(log ell-1)` when centered at `log M`
and `ell log ell` when centered at `μ_M(z)`.  Higher scalar moments,
periodic-residue elimination, the full polynomial coefficient-sum limit and
the analytic transform remain outside that surface.

The v0.22 surface eliminates the zero-mean periodic residue and every fixed
literal seed/endpoint boundary term for the centered linear multiplier.  The
complete coefficient covariance therefore converges entrywise and in finite
matrix norm to `H_bc = G_bc log(min(ell_b,ell_c))`; the direct functional
product and every compatible return-metric colligation inherit the same
limit, with exact target `sixCameraFirstMoment` for cameras `2,...,7`.  Higher
centered powers, the full polynomial limit and the analytic transform remain
outside this surface.

The v0.23 surface proves the second scalar weighted functional moment at every
fixed positive natural cutoff multiplier `ell`.  An exact quadratic increment
identity and little-o summation give the `log M`-centered limit
`ell(log(ell)^2-2log(ell)+2)`; the proved logarithmic-mean asymptotic converts
it to `ell(1+log(ell)^2)` in the documented `μ_M(z)` coordinate.  Elimination
of the quadratic periodic camera residue, the complete second coefficient
covariance and all higher polynomial moments remain outside this surface.

The v0.24 surface eliminates the zero-mean periodic camera residue and every
fixed literal seed/corrected-endpoint boundary term for the centered quadratic
multiplier.  The complete coefficient covariance therefore converges
entrywise and in finite matrix norm to
`J_bc = G_bc(1+log(min(ell_b,ell_c))^2)`; the direct functional product and
every compatible return-metric colligation inherit the same limit, with exact
target `sixCameraSecondCenteredMoment` for cameras `2,...,7`.  Scalar moments
of degree at least three, the full arbitrary-polynomial limit and the analytic
transform remain outside this surface.

The v0.29 surface proves the fifth scalar weighted functional moment at every
fixed positive natural cutoff multiplier `ell`.  The exact quintic increment
uses the previously checked fourth, cubic, quadratic and linear logarithmic
moments with binomial coefficients `-5`, `10`, `-10` and `5`, followed by the
fifth-power mass correction.  Only the logarithmic step times the raw fourth
moment survives at endpoint-weight scale.  Little-o summation gives the
`log M`-centered limit
`ell(log(ell)^5-5log(ell)^4+20log(ell)^3-60log(ell)^2+
120log(ell)-120)`, and the logarithmic-mean asymptotic converts it to
`ell(log(ell)^5+10log(ell)^3-20log(ell)^2+45log(ell)-44)` in the documented
`μ_M(z)` coordinate.  Elimination of the quintic periodic camera residue,
the complete fifth coefficient covariance and all moments of degree at least
six remain outside this surface.

The v0.30 surface eliminates the centered quintic periodic residue and every
fixed literal seed/corrected-endpoint boundary.  Discrete Abel summation
controls `log(n+1)^5 w_z(n)` by `O(log(M)^3)`, while
`μ_M(z)/log(M+1) → 1` reduces the new `μ_M log^4` and
`μ_M^2 log^3` contributions to already checked endpoint and periodic-sum
limits.  Consequently the complete fifth coefficient covariance converges
entrywise and in finite matrix norm to
`G_bc(log(min(ell_b,ell_c))^5 + 10log(min(ell_b,ell_c))^3 -
20log(min(ell_b,ell_c))^2 + 45log(min(ell_b,ell_c)) - 44)`.
The direct functional product and every compatible return-metric colligation
inherit the same limit, with exact target `sixCameraFifthCenteredMoment` for
cameras `2,...,7`.  Scalar moments of degree at least six, the full
arbitrary-polynomial limit and the analytic transform remain outside this
surface.

The v0.31 surface proves the sixth scalar weighted functional moment at every
fixed positive natural cutoff multiplier `ell`.  The exact sextic increment
uses the already checked fifth through first logarithmic moments with binomial
coefficients `-6`, `15`, `-20`, `15` and `-6`, followed by the positive
sixth-power mass correction.  Only the logarithmic step times the raw fifth
moment survives at endpoint-weight scale.  Little-o summation gives the
`log M`-centered limit
`ell(log(ell)^6-6log(ell)^5+30log(ell)^4-120log(ell)^3+
360log(ell)^2-720log(ell)+720)`, and the logarithmic-mean asymptotic converts
it to
`ell(log(ell)^6+15log(ell)^4-40log(ell)^3+135log(ell)^2-
264log(ell)+265)` in the documented `μ_M(z)` coordinate.  Elimination of the
sextic periodic residue, the complete sixth coefficient covariance and all
moments of degree at least seven remain outside this surface.

The v0.32 surface eliminates the centered sextic periodic residue and every
fixed literal seed/corrected-endpoint boundary.  Discrete Abel summation
controls `log(n+1)^6 w_z(n)` by `O(log(M)^4)`, while
`μ_M(z)/log(M+1) → 1` closes the three critical mixed contributions
`μ_M log^5`, `μ_M^2 log^4` and `μ_M^3 log^3`.  Consequently the complete
sixth coefficient covariance converges entrywise and in finite matrix norm to
`G_bc(log(min(ell_b,ell_c))^6 + 15log(min(ell_b,ell_c))^4 -
40log(min(ell_b,ell_c))^3 + 135log(min(ell_b,ell_c))^2 -
264log(min(ell_b,ell_c)) + 265)`.  The direct functional product and every
compatible return-metric colligation inherit the same limit, with exact
target `sixCameraSixthCenteredMoment` for cameras `2,...,7`.  Scalar moments
of degree at least seven, the full arbitrary-polynomial limit and the
analytic transform remain outside this surface.

The v0.33 surface proves the seventh scalar weighted functional moment at
every fixed positive natural cutoff multiplier `ell`.  The exact
seventh-power increment uses the already checked sixth through first
logarithmic moments with binomial coefficients `-7`, `21`, `-35`, `35`,
`-21` and `7`, followed by the negative seventh-power mass correction.  Only
the logarithmic step times the raw sixth moment survives at endpoint-weight
scale.  Little-o summation gives the `log M`-centered limit
`ell(log(ell)^7-7log(ell)^6+42log(ell)^5-210log(ell)^4+
840log(ell)^3-2520log(ell)^2+5040log(ell)-5040)`, and the
logarithmic-mean asymptotic converts it to
`ell(log(ell)^7+21log(ell)^5-70log(ell)^4+315log(ell)^3-
924log(ell)^2+1855log(ell)-1854)`.  Elimination of the seventh-power periodic
residue, the complete seventh coefficient covariance and all moments of
degree at least eight remain outside this surface.

The v0.34 surface eliminates that seventh-power periodic residue and every
fixed literal seed/corrected-endpoint boundary.  Discrete Abel summation
controls `log(n+1)^7 w_z(n)` by its `O(log(M)^5)` endpoint, while
`μ_M(z)/log(M+1) → 1` closes the four critical mixed contributions
`μ_M log^6`, `μ_M^2 log^5`, `μ_M^3 log^4` and `μ_M^4 log^3`.  Consequently
the complete seventh coefficient covariance converges entrywise and in finite
matrix norm to
`G_bc(log(min(ell_b,ell_c))^7 + 21log(min(ell_b,ell_c))^5 -
70log(min(ell_b,ell_c))^4 + 315log(min(ell_b,ell_c))^3 -
924log(min(ell_b,ell_c))^2 + 1855log(min(ell_b,ell_c)) - 1854)`.
The direct functional product and every compatible return-metric colligation
inherit the same limit, with exact target `sixCameraSeventhCenteredMoment` for
cameras `2,...,7`.  Scalar moments of degree at least eight, the full
arbitrary-polynomial limit and the analytic transform remain outside this
surface.

The v0.35 surface proves the eighth scalar weighted functional moment at every
fixed positive natural cutoff multiplier `ell`.  Its exact increment has
binomial coefficients `-8`, `28`, `-56`, `70`, `-56`, `28`, `-8`, followed
by the positive eighth-power mass correction.  Only the logarithmic step times
the already checked raw seventh moment survives at endpoint-weight scale;
all higher-step terms vanish.  Little-o summation gives the `log M`-centered
limit
`ell(log(ell)^8-8log(ell)^7+56log(ell)^6-336log(ell)^5+
1680log(ell)^4-6720log(ell)^3+20160log(ell)^2-40320log(ell)+40320)`,
and `log M - μ_M(z) → 1` converts it to
`ell(log(ell)^8+28log(ell)^6-112log(ell)^5+630log(ell)^4-
2464log(ell)^3+7420log(ell)^2-14832log(ell)+14833)`.  Elimination
of the eighth-power periodic residue, the complete eighth coefficient
covariance and all scalar moments of degree at least nine remain outside this
surface.

The v0.36 surface eliminates that eighth-power periodic residue and every
fixed literal seed/corrected-endpoint boundary.  Discrete Abel summation
controls `log(n+1)^8 w_z(n)` by its `O(log(M)^6)` endpoint, while
`μ_M(z)/log(M+1) → 1` closes the five critical mixed contributions
`μ_M log^7`, `μ_M^2 log^6`, `μ_M^3 log^5`, `μ_M^4 log^4` and
`μ_M^5 log^3`.  Consequently the complete eighth coefficient covariance
converges entrywise and in finite matrix norm to
`G_bc(log(min(ell_b,ell_c))^8 + 28log(min(ell_b,ell_c))^6 -
112log(min(ell_b,ell_c))^5 + 630log(min(ell_b,ell_c))^4 -
2464log(min(ell_b,ell_c))^3 + 7420log(min(ell_b,ell_c))^2 -
14832log(min(ell_b,ell_c)) + 14833)`.  The direct functional product and
every compatible return-metric colligation inherit the same limit, with exact
target `sixCameraEighthCenteredMoment` for cameras `2,...,7`.  Scalar moments
of degree at least nine, the full arbitrary-polynomial limit and the analytic
transform remain outside this surface.

The v0.37 surface replaces the finite list of algebraic moment targets by the
single polynomial hierarchy `P_0=1`, `P_k=(1+X)^k-kP_(k-1)`.  Every `P_k` is
proved monic of natural degree exactly `k`, and the general finite-camera
matrix has the kernel-checked entry formula
`M_k(b,c)=G_bc P_k(log(min(ell_b,ell_c)))`.  It is Hermitian and self-adjoint
for every finite camera family.  Degrees zero through eight recover the
existing concrete matrices definitionally through proved bridge theorems, and
cameras `2,...,7` have one exact literal self-adjoint matrix in every degree.
This is an algebraic hierarchy: scalar and covariance convergence remains
proved only through degree eight.  Arbitrary-degree analytic convergence, the
all-bases completion and the analytic transform remain outside this surface.

The v0.25 surface proves the third scalar weighted functional moment at every
fixed positive natural cutoff multiplier `ell`.  The exact cubic increment
uses the previously checked second and first logarithmic moments with the
binomial coefficients `-3` and `3`; the remaining higher-step corrections
vanish.  Little-o summation gives the `log M`-centered limit
`ell(log(ell)^3-3log(ell)^2+6log(ell)-6)`, and the logarithmic-mean asymptotic
converts it to `ell(log(ell)^3+3log(ell)-2)` in the documented `μ_M(z)`
coordinate.  Elimination of the cubic periodic camera residue, the complete
third coefficient covariance and all moments of degree at least four remain
outside this surface.

The v0.26 surface eliminates the zero-mean periodic camera residue and every
fixed literal seed/corrected-endpoint boundary term for the centered cubic
multiplier.  Because `log(n+1)^3 w_z(n)` is unbounded, the proof uses discrete
Abel summation to bound its periodic weighted sum by the endpoint size
`O(log M)` and then applies `log(M)/A_M(z) -> 0`.  The complete coefficient
covariance therefore converges entrywise and in finite matrix norm to
`K_bc = G_bc(log(min(ell_b,ell_c))^3 + 3log(min(ell_b,ell_c)) - 2)`; the
direct functional product and every compatible return-metric colligation
inherit the same limit, with exact target `sixCameraThirdCenteredMoment` for
cameras `2,...,7`.  Scalar moments of degree at least four, the full
arbitrary-polynomial limit and the analytic transform remain outside this
surface.

The v0.27 surface proves the fourth scalar weighted functional moment at
every fixed positive natural cutoff multiplier `ell`.  The exact quartic
increment uses the previously checked cubic, quadratic and linear logarithmic
moments with binomial coefficients `-4`, `6` and `-4`; all terms beyond the
logarithmic step times the cubic moment vanish at endpoint-weight scale.
Little-o summation gives the `log M`-centered limit
`ell(log(ell)^4-4log(ell)^3+12log(ell)^2-24log(ell)+24)`, and the
logarithmic-mean asymptotic converts it to
`ell(log(ell)^4+6log(ell)^2-8log(ell)+9)` in the documented `μ_M(z)`
coordinate.  Elimination of the quartic periodic camera residue, the complete
fourth coefficient covariance and all moments of degree at least five remain
outside this surface.

The v0.28 surface eliminates the quartic periodic camera residue and every
fixed literal seed/corrected-endpoint boundary.  Discrete Abel summation
controls `log(n+1)^4 w_z(n)` by its endpoint size `O(log(M)^2)`, and the
independently checked limit `log(M)^2/A_M(z) -> 0` makes that contribution
negligible.  Slow variation of `μ_M(z)` under fixed positive natural dilation
closes the mixed terms in the centered expansion.  Consequently the complete
fourth coefficient covariance converges entrywise and in finite matrix norm to
`L_bc = G_bc(log(min(ell_b,ell_c))^4 + 6log(min(ell_b,ell_c))^2 -
8log(min(ell_b,ell_c)) + 9)`.  The direct functional product and every
compatible return-metric colligation inherit the same limit, with exact target
`sixCameraFourthCenteredMoment` for cameras `2,...,7`.  Scalar moments of
degree at least five, the full arbitrary-polynomial limit and the analytic
transform remain outside this surface.

## Explicit nonclaims

The bootstrap and first milestone do not claim:

- an all-bases POVM or Naimark dilation;
- a self-adjoint unbounded logarithmic multiplication operator;
- a closed densely defined all-bases Weyl inverse;
- a maximal boundary relation or gamma field;
- strong-resolvent or strong-graph convergence;
- equality between the Green static Poisson map and a spectral Weyl map;
- any consequence concerning external special-function zeros.
