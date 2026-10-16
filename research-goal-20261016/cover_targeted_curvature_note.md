Targeted second variation in six c=0.0088 frontier cells
=====================================================

The frozen 53,500-node frontier snapshot has six cells at depth at least
18. Exact DBM intersection proves that none of these six cells intersects
any of the existing 69 coherent Gram basin domains. Floating root searches
find stable or saddle stationary points outside the cells, suggesting
correlated interval-gradient artifacts rather than unregistered stationary
minima inside these six cells. These searches are diagnostics, not proofs
of absence of stationary points. One constrained gradient solver reports
failure; solver status is retained in the data.

The targeted second-variation test first selects Hessian directions at
the diagnostic points. Signed affine bounds on each actual-ledger w''
are aggregated with the nonnegative coefficients a*(span d)^2, retaining
the shared nine gaps in an exact flow bound. It certifies uniform negative
curvature on one whole cell. A further fixed test of only the other five
cells uses sparse directions and directions reused across the six cells,
and independently certifies two more cells. The latter witnesses are
d=e8 and d=e0+e8. Every nonzero direction component is supported on a gap
whose whole-cell lower bound is strictly above the original orthant bound.

The evidence directory contains a 17,531-byte gzip of the necessary main
tree ancestry and first certificate, plus a small two-certificate extension.
The shared ancestry is sufficient for all three siblings. The independent
three-leaf replayer reconstructs the c=0.0088 pressure root, every required
ancestor split, and every ancestor OBBT/Newton step, then verifies all three
curvature witnesses. It requires no large evolving checkpoint.

These are alternative local exclusion certificates. They must not be added
to the earlier 43-region count, which concerns a different c=0.00884 tree.
The current main search had already closed the first targeted path without
recording any descendant branch, so no new branch-count saving has been
established by these certificates. They demonstrate a second-variation
exclusion before that path's further sublevel contraction; two of the three
cells have positive upper bounds in the tested first-variation directions.

The same six-cell diagnostic also tests second-order Taylor expansions of
directional gradients. It retains the signed full nine-by-nine quadratic
matrix, bounds it with an exact rational LDL-certified diagonal shift,
and maximizes the remaining affine part by exact flow. The test yields no
strict negative gradient bound. On the three broader cells the cubic
remainder remains large; on the finer cells the matrix payment and cubic
remainder are both material. This negative result is retained and was not
expanded to a larger search.

All actual-analytic-bridge-complete, complete-global-cover and
new-zero-proportion-proven flags remain false. The generic actual
second-variation necessary condition is formalized separately; connecting
these finite scalar bounds and integer aggregates remains an explicit
formal obligation.
