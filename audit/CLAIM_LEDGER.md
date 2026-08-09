# Claim ledger

The machine-readable ledger is `audit/claim-ledger.json`.  At v0.9 it contains
nineteen `KERNEL_CHECKED` claims covering finite-camera geometry, exact periodic
profiles, period mean zero, explicit camera factors and the uniform positive
native-line floor, plus the exact free-coefficient realization of the finite
operator, the complete aligned-C2 finite/profile coefficient identity, and the
complete odd/even natural-camera identities with the final even antipodal
correction.  It also covers absolute and normal bracket convergence,
holomorphy, the exact bracket/profile bridge on `re s > 1`, analytic
continuation of the cross identity, native-scalar factorization and the common
native-line zero set.  The final two claims cover the explicit `M^-3/2`
characteristic and stable cross-residual tails, termwise first differentiation,
the actual native-line first-derivative rate `M^-3/2 log M`, and all fixed-order
complex and native-line derivative rates `M^-3/2 log(M)^k` obtained from a
dynamic-radius Cauchy estimate.  The final claim proves that the nonvanishing
camera factors are local analytic units, so every supported characteristic has
the same analytic order of vanishing at every native-line point.

No finite POVM, infinite camera completion or Weyl inverse is claimed by this
milestone.  The energy-order statement from the research notes is also not
claimed because modal energies are not part of the current scalar API.
