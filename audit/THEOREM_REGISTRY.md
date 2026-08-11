# Theorem registry

The v0.33 scalar seventh-moment milestone contains exactly **711** named public
Lean theorems, ordered as `NCSW-001` through `NCSW-711` in
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
| `NCSW-271`–`NCSW-284` | `Finite/Moments.lean` | generic shared-slope moments, exact first/second centered formulas and six-camera self-adjointness |
| `NCSW-285`–`NCSW-313` | `Finite/Whitening.lean` | positive inverse square root, exact Gram normalization, whitened moments, variance/Schur identity and six-camera operators |
| `NCSW-314`–`NCSW-333` | `Finite/StepDensity.lean` | exact centered-log integrals, continuous step Gram positivity, moment-block factorization and unconditional six-camera variance positivity |
| `NCSW-334`–`NCSW-355` | `Finite/StepPOVM.lean` | positive step-density measure, exact total mass, whitening normalization, centered-log pushforward and canonical six-camera POVM |
| `NCSW-356`–`NCSW-366` | `Limits/PeriodicMean.lean` | exact periodic block/remainder formulas, bounded centered prefixes, Cesàro convergence, Dirichlet--Abel weighted means and finite-prefix stability |
| `NCSW-367`–`NCSW-381` | `Limits/CameraCovariance.lean` | weighted profile limits, asymptotically-linear mass interface, eventual-antitone scaled-cutoff matrix convergence and exact six-camera Gram limit |
| `NCSW-382`–`NCSW-404` | `Limits/ResolventWeight.lean` | concrete resolvent-weight decay and eventual monotonicity, mass divergence, `M/log(M+1)^2` asymptotic, regular variation and concrete covariance limits |
| `NCSW-405`–`NCSW-406` | `Finite/ReturnMetric.lean` | exact endpoint return-metric isometry and source-probe covariance cancellation |
| `NCSW-407`–`NCSW-442` | `Limits/FiniteDefectCovariance.lean` | literal finite supports and endpoints, common-window camera/resolvent matrices, core-boundary decomposition, boundary vanishing and exact return-metric six-camera norm limit |
| `NCSW-443`–`NCSW-446` | `Finite/FunctionalReturnMetric.lean` | constant-observable compatibility and exact arbitrary-observable return-metric cross-covariance cancellation |
| `NCSW-447`–`NCSW-454` | `Limits/FiniteFunctionalCovariance.lean` | literal functional coefficient identity, centered-polynomial specialization, order-zero compatibility and conditional limit transfer |
| `NCSW-455`–`NCSW-458` | `Limits/ResolventLogMean.lean` | centered-numerator telescoping, logarithmic step limit and second-order asymptotic `μ_M(z) - log M → -1` |
| `NCSW-459`–`NCSW-466` | `Limits/ScalarFunctionalMoment.lean` | displaced endpoint slow variation, exact scaled first-moment recurrence and normalized centered limit `ℓ log ℓ` |
| `NCSW-467`–`NCSW-489` | `Limits/LinearFunctionalCovariance.lean` | centered linear periodic-residue and boundary elimination, complete coefficient/direct/return-metric first-moment limits and exact six-camera target |
| `NCSW-490`–`NCSW-497` | `Limits/ScalarSecondFunctionalMoment.lean` | exact quadratic recurrence, raw second scalar limit and weighted-mean-centered limit `ℓ(1+log(ℓ)²)` |
| `NCSW-498`–`NCSW-521` | `Limits/QuadraticFunctionalCovariance.lean` | log-squared periodic-residue and literal-boundary elimination, complete coefficient/direct/return-metric second-moment limits and exact six-camera target |
| `NCSW-522`–`NCSW-530` | `Limits/ScalarThirdFunctionalMoment.lean` | exact cubic recurrence, raw third scalar limit and weighted-mean-centered limit `ℓ(log(ℓ)³+3log(ℓ)-2)` |
| `NCSW-531`–`NCSW-561` | `Limits/CubicFunctionalCovariance.lean` | discrete Abel control of the unbounded log-cubed periodic weight, cubic residue and literal-boundary elimination, complete coefficient/direct/return-metric third-moment limits and exact six-camera target |
| `NCSW-562`–`NCSW-571` | `Limits/ScalarFourthFunctionalMoment.lean` | exact quartic recurrence, raw fourth scalar limit and weighted-mean-centered limit `ℓ(log(ℓ)⁴+6log(ℓ)²-8log(ℓ)+9)` |
| `NCSW-572`–`NCSW-604` | `Limits/QuarticFunctionalCovariance.lean` | log-fourth Abel control, slow variation of the logarithmic mean, quartic residue and literal-boundary elimination, complete coefficient/direct/return-metric fourth-moment limits and exact six-camera target |
| `NCSW-605`–`NCSW-615` | `Limits/ScalarFifthFunctionalMoment.lean` | exact quintic recurrence, raw fifth scalar limit and weighted-mean-centered limit `ℓ(log(ℓ)⁵+10log(ℓ)³-20log(ℓ)²+45log(ℓ)-44)` |
| `NCSW-616`–`NCSW-650` | `Limits/QuinticFunctionalCovariance.lean` | log-fifth Abel control, quintic residue and literal-boundary elimination, complete coefficient/direct/return-metric fifth-moment limits and exact six-camera target |
| `NCSW-651`–`NCSW-662` | `Limits/ScalarSixthFunctionalMoment.lean` | exact sextic recurrence, raw sixth scalar limit and weighted-mean-centered limit `ℓ(log(ℓ)⁶+15log(ℓ)⁴-40log(ℓ)³+135log(ℓ)²-264log(ℓ)+265)` |
| `NCSW-663`–`NCSW-698` | `Limits/SexticFunctionalCovariance.lean` | log-sixth Abel control, three critical mixed terms, sextic residue and literal-boundary elimination, complete coefficient/direct/return-metric sixth-moment limits and exact six-camera target |
| `NCSW-699`–`NCSW-711` | `Limits/ScalarSeventhFunctionalMoment.lean` | exact seventh-power recurrence, raw seventh scalar limit and weighted-mean-centered limit `ℓ(log(ℓ)⁷+21log(ℓ)⁵-70log(ℓ)⁴+315log(ℓ)³-924log(ℓ)²+1855log(ℓ)-1854)` |

The JSON registry is the machine-readable authority for exact qualified names.
