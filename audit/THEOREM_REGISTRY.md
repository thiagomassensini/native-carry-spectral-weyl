# Theorem registry

The v0.11 finite-Gram milestone contains exactly **270** named public Lean
theorems, ordered as `NCSW-001` through `NCSW-270` in
`audit/theorem-registry.json`.  The same order is used by
`NativeCarrySpectralWeyl/Audit.lean`, which emits one named `#print axioms`
report for every declaration.

| Range | Module | Content |
|---|---|---|
| `NCSW-001`–`NCSW-015` | `Camera/PeriodicProfiles.lean` | exact profiles, periodicity and mean zero |
| `NCSW-016`–`NCSW-023` | `Camera/Geometry.lean` | bridge to upstream finite-camera geometry |
| `NCSW-024`–`NCSW-030` | `Camera/Factors.lean` | native line and explicit complex factors |
| `NCSW-031`–`NCSW-047` | `Camera/NativeLineFloor.lean` | exact power norms, alternate floor form, uniform floor and nonvanishing |
| `NCSW-048`–`NCSW-061` | `Camera/FiniteCoefficientBridge.lean` | free stencils, scalar coefficients and exact evaluation upstream |
| `NCSW-062`–`NCSW-065` | `Camera/C2InteriorProfile.lean` | complete finite/profile formula for aligned C2 |
| `NCSW-066`–`NCSW-079` | `Camera/NaturalInteriorProfile.lean` | complete odd/even formulas and even antipodal correction |
| `NCSW-080`–`NCSW-093` | `Camera/ProfileDirichlet.lean` | profile/factor Dirichlet identities on `re s > 1` |
| `NCSW-094`–`NCSW-107` | `Camera/BracketSeries.lean` | centered-difference bounds, absolute summability and pointwise cutoff limits |
| `NCSW-108`–`NCSW-120` | `Camera/NormalConvergence.lean` | compact-normal convergence, holomorphy and locally uniform cutoff limits |
| `NCSW-121`–`NCSW-139` | `Camera/BracketProfileBridge.lean` | complex finite stencils, exact profile prefixes and prefix limits |
| `NCSW-140`–`NCSW-143` | `Camera/BracketProfileFactorization.lean` | infinite bracket/profile/zeta bridge and initial cross identity |
| `NCSW-144`–`NCSW-150` | `Camera/CrossFactorization.lean` | entire factors and analytic continuation of the cross identity |
| `NCSW-151`–`NCSW-156` | `Camera/CommonZeroSet.lean` | native scalar and common native-line zero sets |
| `NCSW-157`–`NCSW-167` | `Camera/QuantitativeTail.lean` | explicit `M^-3/2` characteristic tails and stable cross residuals |
| `NCSW-168`–`NCSW-202` | `Camera/DerivativeTail.lean` | differentiated centered series and `M^-3/2 log M` native-line derivative tail |
| `NCSW-203`–`NCSW-218` | `Camera/HigherDerivativeTail.lean` | dynamic Cauchy discs and all fixed-order `M^-3/2 log(M)^k` derivative tails |
| `NCSW-219`–`NCSW-226` | `Camera/ZeroMultiplicity.lean` | local analytic units and common native-line zero multiplicities |
| `NCSW-227`–`NCSW-257` | `Camera/ModalEnergy.lean` | real/complex order bridge, five modal energies, common zeros and exact order doubling |
| `NCSW-258`–`NCSW-270` | `Finite/Gram.lean` | common periods, periodic product means, finite Gram positivity and exact positive-definite six-camera matrix |

The JSON registry is the machine-readable authority for exact qualified names.
