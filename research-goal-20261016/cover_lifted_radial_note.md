# Stopped radial KKT/RLT diagnostic

The same eight residual parents used in the stopped energy pilot were tested
without changing their cells or expanding the cohort.  The original
derivative graph, affine slabs, DBM constraints and KKT rows were retained.
Complementarity for the original orthant gives the additional identity

`sum_r b_r*(g_r-sep) + sum_t a_t*v_t = 0`,

where `v_t=(span_t(g)-len_t*sep)*w'(span_t(g))`.
One relaxation added 164 McCormick inequalities coupling the common gaps,
derivative variables and these products.  A second also added the supporting
facets of complete-grid rectangle hulls for the actual scalar product graph.
Both models had zero L1 KKT residual and no infeasibility hint on all eight
cells.  Total time was 4.42 seconds.  These are floating diagnostic results,
not accepted proof inequalities or certificates of actual stationarity.

No sample expansion, formal lemma, integer producer or extra verifier was
started.  The existing 13 graph exclusions and their immutable pins remain
unchanged.  The sole full-cover runner continues unchanged, and all global
coverage and new-record flags remain false.
