# Fixed parent64 lifted derivative-graph expansion

This follow-up applies the immutable graph8 method to all 64 parents of the
same previously frozen cohort.  The parents are mutually nonnested,
depth-24 branch records below `r00100000`, sampled in discovery order from
the latest 512 eligible branches at that depth.  No new cells were selected
after seeing graph success.  The source checkpoint had checked 65,500 nodes.
This is a local proof-compression experiment at `c=11/1250`; every global
coverage, actual graph-consumer and new-record flag remains false.

The single-slab KKT LP has zero residual in all 64 cells.  Adding globally
valid affine facets of each scalar derivative graph produces 13 positive
residuals and 13 strict rounded-integer Farkas/flow certificates.  Discovery
took 11.89 seconds including initialization.  These 13 *include* all four
successful graph8 cases; the two packages must not be added as 17 regions.
The independent full-cohort replay passed in 20.97 seconds, reconstructing
562 ancestor/parent nodes, 4,415 ancestor OBBT bounds and 37 Newton steps,
and recomputing 741 derivative grid cells directly from rational Taylor
jets and the order-24 remainder.

The ancestor-only archive is 163,452 bytes.  It contains the 13 witnesses,
their 140 strict ancestor branch records, the projected OBBT/Newton chains,
and fresh nonclosing old controls.  Its standalone replay passed in 10.32
seconds: 153 reconstructed nodes, 1,209 ancestor bounds, three ancestor
Newton steps, and 13 old controls with 121 bounds and 15 Newton steps.
It needs neither the full parent64 sample nor the original large checkpoint.
Run:

```text
python -B -X utf8 research-goal-20261016/cover_lifted_graph_archive_replay.py --archive research-goal-20261016/cover-lifted-graph64-evidence
```

The 13 parents' frozen source subtrees contain 27 branch records, 40 accepted
leaves, 38 OBBT paths with 422 bounds, and 14 Newton paths with 69 steps.
These work metrics come from the source projection, not an independent
replay of every descendant contraction.  Every selected parent is strictly
excluded as a location of an original global minimum by its new certificate;
this is stronger than the paired old control's outcome at that parent.
The live full-cover process was not modified to use the new method.

The pilot `r001000001000100110001001` was chosen from the 13 positives by
the fewest distinct active scalar graphs, followed by the fewest facets,
slabs and total weighted rows.  It has 31 active scalar graphs, 22 facet
rows, ten old slab rows, four DBM rows and seven KKT rows (43 weighted rows
total).  The raw certificate is 6,826 bytes.  The explicit 31,189-byte pilot
JSON also includes the cell, 41 term coefficients, pressure coefficients,
the correct DBM pair order, input hashes and all 623 facet-grid rows.
Its strict residual-paid integer margin is
`12310810974159504285408296960000000000`.
The generic actual Lean consumer and the pilot's Lean instantiation are
separate tasks; this receipt does not claim either has passed.

The complete row schema and proof inequality are pinned in
`cover_lifted_graph8_note.md`.  No original pinned source was changed for
this expansion.  The 13 regions concern the current c880 tree; previously
archived finite-move cuts concern a c884 tree, so cross-tree path strings
alone are not used to claim a larger disjoint union.
