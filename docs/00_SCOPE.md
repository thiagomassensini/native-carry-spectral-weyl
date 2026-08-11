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

## Explicit nonclaims

The bootstrap and first milestone do not claim:

- an all-bases POVM or Naimark dilation;
- a self-adjoint unbounded logarithmic multiplication operator;
- a closed densely defined all-bases Weyl inverse;
- a maximal boundary relation or gamma field;
- strong-resolvent or strong-graph convergence;
- equality between the Green static Poisson map and a spectral Weyl map;
- any consequence concerning external special-function zeros.
