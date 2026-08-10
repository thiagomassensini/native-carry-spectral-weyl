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

The scalar surface additionally admits quantitative cutoff claims only
after the centered block identity is retained through the norm estimate.  In
particular, the first native-line derivative tail is proved by differentiating
the centered bracket before taking norms; no three-leg termwise estimate or
numerical slope is used as a Lean premise.  Every higher fixed-order derivative
tail is then proved from a uniform order-zero estimate on a Cauchy circle of
radius `1 / log M`; no numerical derivative fit is used as a Lean premise.

## Explicit nonclaims

The bootstrap and first milestone do not claim:

- an all-bases POVM or Naimark dilation;
- a self-adjoint unbounded logarithmic multiplication operator;
- a closed densely defined all-bases Weyl inverse;
- a maximal boundary relation or gamma field;
- strong-resolvent or strong-graph convergence;
- equality between the Green static Poisson map and a spectral Weyl map;
- any consequence concerning external special-function zeros.
