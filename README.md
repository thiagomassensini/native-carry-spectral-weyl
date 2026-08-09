# Native Carry Spectral Weyl

Lean 4 formalization of the spectral/Weyl layer associated with the native
carry cameras.

## Current status

The v0.3 C2 interior-profile milestone contains **64 public kernel-checked Lean
theorems**.  It builds against the exact Green Frame v2.1 commit and the exact
finite native-carry operator commit.  The current public surface proves:

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

The remaining finite bridge obligation is to prove the corresponding exact
window formulas for odd and even natural cameras.
The analytic factorization of camera characteristics is also separate.  No
common-zero or Weyl-family claim is inferred from this milestone.

Pinned foundations:

- Lean `4.32.0`;
- Mathlib `v4.32.0`, inherited through the pinned dependencies;
- Green Frame commit `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`
  (`v2.1.0`);
- Finite Native Carry Operator commit
  `00e9d6beb17226545abf5ddf90bbfede6c7146b0` (`v0.1.0`).

## Intended theorem boundary

The formalization will proceed from exact camera arithmetic to finite spectral
objects, then to the countable camera completion, Cauchy transform and an
unbounded Weyl inverse.  Boundary relations and the coupling to the Green
state/port layer come only after their domain and maximality statements are
proved independently.

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
- `research/SOURCE_CATALOG.md`: source inventory and provenance findings;
- `audit/theorem-registry.json`: ordered registry of all 64 public theorems;
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
