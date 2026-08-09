# Theorem registry

The v0.2 finite-coefficient milestone contains exactly **60** named public Lean
theorems, ordered as `NCSW-001` through `NCSW-060` in
`audit/theorem-registry.json`.  The same order is used by
`NativeCarrySpectralWeyl/Audit.lean`, which emits one named `#print axioms`
report for every declaration.

| Range | Module | Content |
|---|---|---|
| `NCSW-001`–`NCSW-015` | `Camera/PeriodicProfiles.lean` | exact profiles, periodicity and mean zero |
| `NCSW-016`–`NCSW-023` | `Camera/Geometry.lean` | bridge to upstream finite-camera geometry |
| `NCSW-024`–`NCSW-030` | `Camera/Factors.lean` | native line and explicit complex factors |
| `NCSW-031`–`NCSW-046` | `Camera/NativeLineFloor.lean` | exact power norms, uniform floor and nonvanishing |
| `NCSW-047`–`NCSW-060` | `Camera/FiniteCoefficientBridge.lean` | free stencils, scalar coefficients and exact evaluation upstream |

The JSON registry is the machine-readable authority for exact qualified names.
