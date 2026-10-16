# Negative joint-energy pilot on eight residual parents

After the 13 graph-only closures, the first eight remaining parents in the
fixed cohort's discovery order were tested.  The model retained every
derivative-graph, midpoint-slab, DBM and KKT row, then added the existing
energy support epigraph and `F <= 11/1250`.  The old single-slab joint-energy
method was run as a paired control.  Both models had zero closures on all
eight; every new LP L1 residual was zero.  Total time was 13.90 seconds.

No integer certificate was emitted, no new exact replay is claimed, and the
sample was not expanded.  LP zero residual is diagnostic evidence of this
relaxation's limitation, not a theorem that an actual KKT point exists.
The 13 successful graph-only regions remain the complete positive count.

The proposed integer extension, unused because there was no positive hint,
would aggregate energy epigraph variables `v_t >= 0`.  Support multipliers
would obey `D*sum(mu_support_t) <= mu_energy*a_t` after quantization, leaving
all aggregate `v_t` coefficients nonnegative.  These coefficients could be
dropped while retaining the existing residual payment for derivative `u_t`
variables and one exact flow over the common nine gaps.  No extra bound on
`w` would be needed.  The pilot changed no frozen graph source, live runner,
ledger or target.  The full negative curvature bundle is not required here.
