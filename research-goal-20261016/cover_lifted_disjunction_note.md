# One extra parent from a single graph split

The exact same eight residual parents from the stopped energy and radial
pilots were tested at one split level.  At each parent's graph-LP solution,
the discrepancy between the relaxed derivative variable and the actual
scalar derivative selected at most three spans.  Each span supplied only
the LP point, nearest integer and nearest half-integer cut candidates when
strictly inside its interval.  All old graph rows were preserved.  The old
single-slab predicate was run on the same children, and the old value-based
split rule was also tested with both predicates.  These choices are
discovery heuristics; the accepted proof uses only exact child geometry and
strict integer certificates.

Across eight parents, 48 candidate splits and 112 distinct child cells were
tested in 30.64 seconds.  Exactly one parent closed with two graph leaves:

- Parent: `r001000001000001110011100`.
- Split axis 39, span `(5,7)`, at `73527/32768`.
- The relaxed derivative at the selected LP point was about `-0.0184488`,
  while the actual derivative there was about `+0.0338056`.
- Child strict margins:
  `9273915747776907966958469120000000000` and
  `16638686788409057404028846080000000000`.

Neither the same split with the old single-slab checker nor the old
value-based split with the graph checker closed this parent at one level.
The fresh old OBBT/Newton control also remained a branch.  This parent is
disjoint from the prior 13 fixed-cohort graph parents.  The count is thus
14 parent regions in this cohort, represented by 13 direct graph leaves and
one split with two graph leaves.  The 21 candidate graph child-certificate
occurrences are *not* 21 additional parent regions; partial child results
and repeated cells are excluded from that total.

The full pilot's independent replay passed under `python -S` in 8.44
seconds, checking all 40 distinct accepted certificates (old and new
controls included), 77 ancestor nodes and 617 ancestor OBBT bounds.  The
89,534-byte gzip file losslessly stores the local 402,024-byte full JSON.
The full verifier reads the raw JSON if available and otherwise uses gzip.
All numerical selection and negative-control values remain diagnostic,
not certificates of actual stationary points or LP feasibility.

The minimal successful-parent archive is 23,051 bytes and needs no full
parent64 input or large checkpoint.  Its independent `python -S` replay
passed in 4.31 seconds, reconstructing 25 nodes and 163 ancestor bounds,
checking the split and two strict graph leaves, and replaying the nonclosing
old control's 13 OBBT bounds.  The original source subtree had two branch
records, three leaves, 46 OBBT bounds and four Newton steps; these last work
counts remain source-projection metrics, not a complete old-subtree replay.

```text
python -S -B -X utf8 research-goal-20261016/cover_lifted_graph_disjunction_archive_replay.py
```

No second-level search, sample expansion or new full-domain job was started.
The existing main process, threshold, APIs and prior immutable pins were not
changed.  Global coverage and new zero-proportion flags remain false.
