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

The analytic common-zero theorem is admitted to the release surface only after
normal convergence, analytic continuation and local multiplicity are all
kernel checked.

## Explicit nonclaims

The bootstrap and first milestone do not claim:

- an all-bases POVM or Naimark dilation;
- a self-adjoint unbounded logarithmic multiplication operator;
- a closed densely defined all-bases Weyl inverse;
- a maximal boundary relation or gamma field;
- strong-resolvent or strong-graph convergence;
- equality between the Green static Poisson map and a spectral Weyl map;
- any consequence concerning external special-function zeros.
