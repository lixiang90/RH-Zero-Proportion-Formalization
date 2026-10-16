# Lossless integration route and checked local replacement

No running process or existing guarded runner was changed or restarted.
`cover_lifted_graph_api.py` provides `make_graph_oracle(taylor=None, path)`,
`exclusion(state, oracle)` and `probe(state, oracle)` for a future independent
fork.  It reuses the current first-order Taylor oracle and caches the graph
facets.  The API reproduced all 64 outcomes and all 13 certificates field
for field in 9.33 seconds.  Its source-hash map is recorded separately.
The predicate is independent of the energy threshold and proves absence
of original-domain KKT points in the supplied closed cell.

The minimum future-runner change is to call this predicate once after the
existing cheap stationary and value checks fail, and before that path's
OBBT/Newton contraction.  A positive result becomes a new `lifted_graph`
leaf at the original cell; no contraction maps are added at that path.
The existing codec returns an unfamiliar leaf verbatim, so its data can be
kept without altering the frozen codec.  The fork must use a new explicit
format version, hash the new API/engine dependencies, count the new leaf
kind, and dispatch it to the graph checker.  A checker must reject unknown
leaf kinds.  It can inherit all old accepted leaves, branches, contractions
and pending states when resuming a saved v2 checkpoint.  The old v2 runner
and verifier should remain unchanged.  This document does not launch a fork
or replace the current live process.

A postprocessing alternative leaves discovery untouched: on an immutable
complete subtree, prove a graph exclusion on its pre-OBBT parent cell,
replace all its branches and leaves by the one graph leaf, and remove all
OBBT/Newton records at or below that parent.  Ancestor records are shared
unchanged.  This operation was checked on all 13 successful parents using a
new share-delete-safe snapshot of the live file at 76,000 checked nodes.
The snapshot stream kept only the required old subtrees and strict ancestors;
it did not copy or mutate the whole evolving checkpoint.

Both old and replacement local trees passed an independent exact replay
under `python -S` in 15.62 seconds.  The old 13 complete subtrees contain 67
nodes: 27 branches and 40 leaves (27 stationary, 12 value, one reflection),
38 OBBT paths/422 bounds and 14 Newton paths/69 steps.  The replacement has
13 graph leaves, saving 54 nodes and every below-parent contraction.  Every
old leaf, scalar support, contraction, exact flow and branch geometry was
checked, rather than merely counted from a projection.  Strict ancestor
obligations are reconstructed too; omitted ancestor siblings remain external
open obligations, so this is not a complete global cover.

Using identical compact JSON and gzip encoding on the two local payloads,
old bytes `464417 -> 99612` raw and `98724 -> 31947` gzip show a 67.6 percent
gzip reduction **only for these 13 selected subtrees**.  Shared ancestors
are excluded from both local payload measurements.  The self-contained
replacement comparison, including ancestors and both versions, is 241,502
bytes gzip.  This does not imply a global size reduction of that magnitude
or satisfy the website's final Lean source-size requirement.

Discovery creates 1,438--2,110 facet inequalities per cell (median 1,866),
but an accepted certificate retains only 21--34 selected facets and about
49 weighted rows on average.  The 13 replacement leaves together are
99,612 raw /31,947 gzip bytes, about 2.46 KB gzip per leaf.  The standalone
API's 64-cell timing was 0.146 seconds per cell after oracle creation; the
already-warmed original graph diagnostic spent 4.29 seconds on its 64 graph
LPs, or 0.067 seconds per cell.  The old fresh controls for the 13 successful
parents consumed 17.95 seconds, before considering their descendants.
These are local measurements, not a whole-domain runtime forecast.

The fresh replacement verifier uses `cover_exact_scalar_replay.py` to supply
only the legacy decoder's two exact rational scalar support routines and
literal ledger constants.  Existing legacy verifier modules otherwise
transitively import a producer module containing unused numerical imports.
The new adapter permits a stronger audit under Python's `-S` mode; the
receipt explicitly checks that NumPy, SciPy and NetworkX were never imported.
Every decoded proof unit must still match its original canonical SHA256.
No optimizer or numerical discovery routine is called in this audit.

```text
python -S -B -X utf8 research-goal-20261016/cover_lifted_graph_replacement_verify.py
```

The separate eight-cell joint-energy pilot was negative and stopped.  Its
tiny source, diagnostic and note are included, without the two-megabyte
negative curvature bundle.  All global-cover and new-record flags remain
false.  The actual Lean graph/Farkas consumer and mixed-cover composition
are separate formalization tasks owned by the main proof queue.
