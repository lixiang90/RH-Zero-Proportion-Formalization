# Lifted derivative graph: fixed eight-parent pilot

This is a local proof-compression result for the fixed 24-mode ledger at
`c = 11/1250`, not a complete global energy bound or zero-proportion record.
The sole full-cover process remains unchanged.

The eight parents were selected by the most negative feasible-midpoint
Hessian eigenvalue hints within an already frozen sample of 64 mutually
nonnested depth-24 branch parents below `r00100000`.  This selection is a
discovery heuristic, not part of the proof.  All eight remained open under
the old OBBT/Newton control.  Direct negative curvature and nonnegative
curvature portfolios closed none of the 64.  A paired two-round test adding
curvature-upper cuts to energy OBBT chose no positive curvature multipliers
and closed none of the eight.  LP basis changes generated different ordinary
energy bounds; these are not counted as mathematical improvements.

The new method introduces one actual derivative variable
`u_t = w'(sum(g_i, i in span t))` per positive-weight pair.  It retains the
old midpoint affine slab on both sides and adds supporting affine lines
selected from the convex hull of the frozen 1/64 derivative rectangles.
Every selected line's intercept is recomputed over *every* rectangle
intersecting the complete span interval.  It therefore remains valid
without any assumption that the derivative graph is convex or concave.
The common nine gaps, all DBM constraints and the KKT conditions share these
scalar variables.  Interior coordinates have zero gradient; a coordinate
whose lower bound reaches the original separation boundary has only the
necessary nonnegative-gradient condition.

The old single-slab LP has zero L1 KKT residual on all eight sampled cells.
The new graph has positive residual on four and produces four strict
integer certificates in 3.33 seconds total, including startup.  No floating
LP value is used in an accepted inequality.  The positive certificates use
nonnegative integer Farkas multipliers, an independently checked DBM flow,
and the actual global `|w'| <= 7` bound to pay for uncancelled scalar
coefficients.  The four parents are mutually nonnested.  Their frozen source
subtrees contain 14 branch records, 18 accepted leaves, 184 OBBT bounds and
35 Newton steps.  These counts are source-projection cost metrics, not a
claim to have independently replayed every descendant contraction.

## Stable integer schema

Use `SC = 32768`, `DS = 10^15`, `D = 10^10`,
`Q = 2*SC*DS*D`, and the 41 positive-weight pair order of
`window_reweight_rational.json`.  Each valid row is

`Ag . g + Au . u <= B`.

All rows use the same integer denominator `Q` before LP discovery.  A grid
facet with integer slope `S` is
`SC*DS*u - S*q <= C`, where `q = SC*span(g)`.  Its upper intercept is
`max_k(SC*U_k - S*(lo_k if S >= 0 else hi_k))`; the lower intercept is
`min_k(SC*L_k - S*(hi_k if S >= 0 else lo_k))`.
The grid endpoints `lo_k,hi_k` are clipped to the current cell interval.

Certificate `weighted_rows` stores `[meta, decimal_nonnegative_integer]`:

- `['DBM', z, sign]` selects a span endpoint constraint.
- `['slab', t, sign]` selects a side of the old affine enclosure.
- `['facet', t, sign, decimal_S, decimal_C]` selects a new graph line.
- `['KKT', k, sign]` selects a gradient inequality. `sign=1` requires a
  strictly interior lower bound; `sign=-1` is always necessary.

`gap_coefficients`, `scalar_coefficients` and `rhs` store the integer sums
`Ag`, `Au`, `B`.  Flow certifies `M <= Ag . q`, with `q = SC*g`.
`scalar_residual_payment = 7*SC*sum(abs(Au_t))` and
`strict_margin = M - scalar_residual_payment - SC*B > 0`.
Consequently every feasible actual KKT point would satisfy both the summed
upper inequality and its strict opposite.  The `weight_scale` used to
quantize the LP multipliers has no proof significance.

## Independent replay and minimal archive

Run from the repository root:

```text
python -B -X utf8 research-goal-20261016/cover_lifted_graph_archive_replay.py
```

The ancestor-only `cover-lifted-graph8-evidence/proof.json.gz` is 60,261
bytes.  It reconstructs the four cells from 62 ancestor branch records,
replays 450 ancestor OBBT bounds, checks the four certificates, and also
replays the four fresh nonclosing old controls (23 bounds and seven Newton
steps).  It needs neither the original large full-cover checkpoint nor the
full parent64 sample.  Replay passed in 6.45 seconds.  The verifier
independently recomputed all 641 used derivative grid cells from frozen
rational Taylor coefficients and the explicit order-24 remainder, and
checked all original affine slabs, complete-span facet intercepts, KKT
boundary signs, flow balances and strict margins.  The full-eight replay
also passed, with 111 reconstructed nodes and 725 ancestor bounds.

The discovery scripts are included for transparency.  Their larger local
selection inputs are not required by the minimal archive's verifier.  The
actual Lean graph/Farkas consumer is a separate work item; this package does
not claim that consumer has passed or that the four cells complete a cover.
The 64-parent expansion is intentionally outside this immutable pilot pin.
