# Conceptual audit after the closed rigged-port milestone

Status: post-v0.53 form-first extension.  This document separates the closed
atlas-independent mechanism from the remaining Green/Haar analytic input.

## What is actually closed

The canonical logarithmic rigged structure is no longer an open
functional-analytic problem in the current coordinate model.

- `Jx(n)=x(n)/(1+log n)` is a bounded injective complex-linear map with dense
  range.
- Its range is exactly
  `{x ∈ ℓ² | ((1+log n)x(n))_n ∈ ℓ²}`.
- The inverse `M_w x(n)=(1+log n)x(n)` is a densely defined, proper-domain,
  surjective `LinearPMap`.
- `M_w` is closed, closable and self-adjoint, and its canonical graph closure
  is `M_w` itself.
- The domain is invariant under `U(t)` and `M_w U(t)=U(t)M_w` on that domain.
- Every point of the distinguished critical orbit is outside `Dom(M_w)`.
  Thus closed unrigging does not turn the harmonic raw amplitude into an
  unweighted `ℓ²` state.
- The critical orbit does belong globally to the canonical strong dual: the
  Fréchet--Riesz map is an anti-linear isometric equivalence from the `H₋₁`
  coordinate realization to the strong dual of the corresponding `H₁`
  test-coordinate realization.

Consequently, neither closability nor closedness of the diagonal unrigging
operator remains open.  Replacing this operator by a bounded everywhere-
defined unrigging map would contradict the proved domain obstruction.

The form-level all-bases mechanism is also closed.  Every bounded real-linear
map on the finitely supported camera core with values in a complete real
normed target extends uniquely to `CameraHilbert`; the extension preserves the
exact operator norm.  In particular, the target can be the two-coordinate
real plane used by the native operator.  The C3 packaging into `ℂ` is an
equivalence of coordinates, so it neither creates nor discards a Green
channel.  Restriction
along any isometric atlas inclusion retains the same bound, with no atlas
cardinality or cutoff in the constant.  The concrete finite-label restrictions
are exactly compatible under enlargement.  In the explicit Naimark model,
`u ↦ ⟨g,V u⟩` is the canonical target functional and has uniform bound
`‖g‖`, hence one for a unit source.  These results are functional-analytic
infrastructure: they do not assert that the research-specific Green/Haar core
formula has been defined, that it satisfies the required bound, or that its
source has been realized as such a `g`.

## Open work requiring new mathematical structure

These items cannot be discharged by translating an already fixed Lean
statement.  Each requires an additional mathematical object, topology or
identification theorem.

1. **Research-specific Green/Haar core formula and estimate.**  Define the
   proposed functional on `CameraFinsupp` and prove one estimate
   `|q(u)| ≤ C‖u‖` in the intrinsic all-bases Gram norm, with `C`
   independent of every finite atlas.  The new completion theorem then extends
   it uniquely; it does not prove this analytic input.

2. **Mixed-order boundary geometry.**  The source notes retain a first-order
   coarse channel while bracket/hidden channels are second order.  A valid
   anisotropic test space, common domain and output topology must be chosen
   before those channels can be assembled into one port.

3. **Operator-level Haar/CP-Green intertwining.**  The boundary-completed
   energy identity must be connected by a typed theorem to the native return
   atlas.  Current repositories provide the two sides and abstract transport,
   but not this intertwiner.

4. **Source realization or vector synthesis, if needed.**  The all-bases
   functional itself now has a canonical topology and an order-independent
   continuous extension.  A stronger literal camera-vector output would still
   require a separate Riesz/source realization theorem and the corresponding
   global value/flux estimate.

5. **Downstream factorization through the form.**  The form-first branch has
   now been selected and formalized.  It remains to prove that the intended
   Green/Haar observables factor through this continuous functional, or else to
   add a genuinely new mixed-order operator/relation realization.  No bounded
   vector port follows from the extension theorem.

6. **Limit identification, if finite cutoffs are required downstream.**  The
   present all-bases Weyl family is constructed directly, so strong-resolvent
   or strong-graph convergence is not needed for it.  A future claim that a
   particular Green/Haar cutoff converges to the new boundary synthesis would
   require a new topology-aware limit theorem.

## Open work that is formalization or consolidation

These tasks refine or package mathematics whose intended content is already
substantially fixed.  They do not, by themselves, resolve the missing camera
synthesis above.

1. Generalize the fixed logarithmic `H₋₁` realization to the full
   `H_{-σ}`/`H_σ` scale and formalize the threshold `σ>1/2`.

2. Replace the semantic coordinate aliases by explicit isometric
   identifications of the weighted test and distribution spaces, and state
   the raw coefficient pairing through those identifications.

3. Bundle `t ↦ U(t)` as a strongly continuous representation, identify its
   Stone generator as diagonal multiplication by `log n`, and add graph-norm,
   core and finite-coordinate cutoff lemmas for the maximal multiplier.

4. Extend the analytic functional-covariance convergence from degrees zero
   through eight to arbitrary degree using the already formalized polynomial
   hierarchy.  This is a separate analytic-consolidation track.

5. Once a research-specific readout is supplied, instantiate the existing
   `GreenCameraCoupling` and `AngularGreenCameraCoupling` transport theorems.
   The gamma/Weyl transport itself is already formalized.

6. Consolidate cross-repository terminology and provenance for the Green,
   Haar, finite-return and Weyl layers after the missing intertwiner has a
   stable statement.

## Optional structures, not current blockers

- A native complex scalar action on the real all-bases camera completion.
- An explicit PVM rather than the existing multiplication model.
- An ordinary boundary triple rather than the checked relation/gamma-field
  formulation.
- Holonomic, tau/Painlevé and three-color extensions.

None of these optional structures is needed to preserve the v0.53 results.
No next gate is selected by this audit.
