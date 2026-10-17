# Fixed W10 cell-to-certificate predictor pilot

The three fixed simple geometry predictors do not give a useful route to
a complete source below 2,000,000 bytes on this pilot. This is a negative
result about these rules, not an impossibility theorem for algorithmic
certificate reconstruction. No predictor was tuned after seeing the data.
No optimizer, new covering search or Lean process was run.

The sample is exactly the first 1000 numeric leaves in the frozen preorder,
from `r0000` through `r0101010111101000`, consuming 2009 tree nodes. It is
a nonrandom prefix and cannot establish a full-tree compression rate.
All old caches, sources, parameters and candidate thresholds stayed unchanged.

## Fixed PT rules and actual certificate success

For each span, use
`L=max(spanLo,sum gapLo)` and `U=min(spanHi,sum gapHi)`. An encoded PT anchor
`p` on the inherited 32-unit grid is eligible only when its actual table
domain satisfies `valid_u>0` and `valid_l<=L<=p<=U<=valid_u`. Thus its
certified tangent applies throughout the cell. Select the nearest eligible
anchor to the midpoint (smaller on ties), the left endpoint, or the right
endpoint respectively. Use kind1/full tangent weight1024; use kind0/the
inherited interval lower bound if no eligible PT exists. No margin is used
to infer domain validity.

| Fixed rule | Exact original FS row matches /39000 | First point matches /19386 active rows | New FS + old tree passes /1000 |
| --- | ---: | ---: | ---: |
| Midpoint | 5081 | 3578 | 4 |
| Left endpoint | 2990 | 1483 | 1 |
| Right endpoint | 5603 | 4099 | 3 |

The last column is a genuine new-certificate numerical check, separate from
matching the old witness. For every candidate the actual PT scalar guards
are checked, slopes/divergence are recomputed from the new FS, and signed
flows are reconstructed from the old Pruefer code. The complete integer
inequality is then checked. Old flow amounts are never reused. Invalid
domains, codes or flow conservation are fatal; only a false final target
inequality counts as a numerical failure. All three rules have valid PT
domains in this sample, but almost all of their resulting bounds are too weak.

Legal PT anchors exist for37491/39000 term cells, whereas the original
certificate uses a tangent in only19386. The predicted kind agrees in
20168/39000 rows. Therefore PT availability alone misses most decisions
to retain the interval lower bound. Geometry alone also predicts only a
small fraction of the chosen first anchors. The existing witness decisions
reflect the aggregate slopes and their coupled linear bound.

## Explicit exception format and exact reconstruction

For each leaf store a39-bit exception mask (5 bytes). A set bit is followed
by the original kind byte; a mixture has its original UInt16 weight; an
active term has signed ULEB point-index difference from the predicted
anchor; kind3 also has its signed second-minus-first point-index difference.
The original UInt32 Pruefer code is retained. Header: `W10P`, version1,
one rule byte, UInt16 count1000. Unused mask bits must be zero.

| Rule | Complete exception stream bytes, including original trees | Gzip bytes | Shared-Huffman residual payload bits, excluding tree |
| --- | ---: | ---: | ---: |
| Midpoint | 68238 | 35973 | 209790 |
| Left | 80937 | 38082 | 225827 |
| Right | 67347 | 34662 | 194831 |

All three streams reconstruct every original FS exactly and all1000 old
integer inequalities pass. Gzip here is a lossless storage format; no Lean
gzip decoder or complete compressed-source artifact is claimed.

## Flow reconstruction is not a greedy algorithm

The frozen `tree_flow.recompute` builds all90 directed arcs with DBM costs,
divergence demands, and calls `nx.network_simplex`. It then completes the
returned nonzero flow forest by ordered adjacent zero-flow edges and emits
a Pruefer code. This is a full min-cost-flow algorithm, not a simple greedy
reconstruction. No such solve was called in this pilot. Exact reproduction
would also need to fix the algorithm implementation/tie choices. For proof
soundness, a deterministic replacement need only produce a valid checked
flow; it need not reproduce the old optimum or prove optimality. Its actual
Lean elaboration/kernel cost remains unmeasured.

Four predeclared constant trees were checked with the **original FS**:
adjacent chain(code87654321):254/1000; star0:64; star5:20; star9:63.
Their union passes332/1000; none exactly matches an original tree code.
These332 successes are not new-FS successes and are not added to the4/1/3.
They only show that some existing FS can use a deterministic checked tree.

## Source budget and limits of this diagnosis

The already measured full field-Huffman binary has geometry280659 bytes,
FS2217236 bytes, tree294132 bytes and7 framing bytes. Its printable data
alone is3461607 bytes. The retained formal/analytic source is542851 bytes;
the earlier engineering reserve for a still-unimplemented decoder/expander
is128000 bytes. Even removing the entire tree channel saves only about
0.37MB at the observed literal factor, far below the current source gap.

For diagnosis only, carrying the first1000 residual distributions to all
95615 leaves, retaining the actual full geometry/tree channels, and using
a1.25 printable factor gives4.53MB(midpoint),4.77MB(left),4.31MB(right)
including the retained source and decoder reserve. These are distribution
extrapolations, not bounds or measured complete Lean files. They do not
support a claim of source below2MB. No full-tree predictor scan was done.

A stronger reconstruction algorithm would have to address the active-kind
and aggregate-slope decisions, rather than only choosing a nearby legal
anchor. That is a different finite algorithm/certificate-generation task;
its success, source size and compilation cost have not been established.

## Reproduction and frozen scope

`pilot.py` reproduces the original analysis using the three read-only
semantic caches whose full hashes are in `result.json`, plus the frozen
analytic reader. Its output paths are exclusive. To rerun it, use a fresh
output copy rather than overwriting this package.

`sample-input.json.gz` is a57253-byte projection of just the consumed node,
FS and tree prefixes, with full donor hashes and exact prefix hashes. It
does not claim that a prefix hash proves membership in a full file without
the donor; the exporter checked those full donor hashes. The separate
standalone replayer rechecks all mathematics for the projected prefix and
needs no large semantic cache or historical checkpoint:

```text
python -B -X utf8 research-goal-20261016/w10-cell-predictor-20261017/standalone.py
```

The receipt target is exclusive, so use a fresh copy of this small folder
with its old `standalone-replay.json` omitted for a new replay. Required
frozen analytic/geometry reader paths and hashes are in the packet and the
existing `w10-size-audit-20261017/independent-codec-files.json` pin. The new
standalone pass took13.48 seconds:1000 original leaf checks,3000 exact
exception reconstructions, and independent confirmation of both sets of
candidate success counts. Only false final target inequalities are treated
as failed candidates; other assertion failures abort the replay.

No full95615-leaf predictor replay, new functional Lean decoder, complete
Lean cover, source below2MB, unconditional zero proportion, or website
submission readiness is asserted. All such flags remain false.
