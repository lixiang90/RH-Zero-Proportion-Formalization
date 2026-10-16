# Same Friendly factors with global derivative/product boxes

The two frozen Friendly grouped certificates retain all 103/106 factors,
all `old_meta,A,b` values and the original energy weight/packet. Only the
boxes used for outward-rounding payment and final residual cost change:

- g: the original nine cell intervals;
- u: [-7,7] for all 41 actual derivative values;
- H: [0,1] on its diagonal, [-1,1] off its diagonal;
- q: [-7,7] for all 369 position-times-derivative products.

The 41 tight derivative ranges and their induced q ranges are no longer
needed for the final box argument. The actual old derivative slab/facet
rows still use the same frozen grid inputs and are checked by GraphReplay.
This simplification does not remove those scalar graph premises.

Every weighted group is re-integerized outward at 1e30 using these larger
boxes; the old rounding payments are not reused. Exact strict normalized
margins are approximately 0.002186353792546525 and 0.00010148292670532981.
All 464 unrounded coefficients and the constant remain unchanged. The
global-box proof is 35,768 gzip bytes and its ordinary consumer JSON is
41,888 bytes, with no `tight_derivative_bounds` field.

The independent wrapper changes only the frozen replay's box-construction
hook. It uses canonical nonnegative RLT decomposition, checks the unmerged
multiplier audit and old actual graph atoms, independently rounds all rows
and verifies the strict aggregate. It passes in about 5.95 seconds. The
wrapper makes two global box constructions and no tight scalar-box query.
Existing energy point/grid analytic inputs remain inputs to this finite
arithmetic audit; no new kernel evaluation, LP, sampling, PSD search, Lean
execution or old-source edit is performed.

```text
python -S -B -X utf8 research-goal-20261016/cover_cross_moment_global_box_replay.py
```

`cover-cross-moment-global-box-cases.json` is the owner-facing view. Its box
policy is `cell-g/unit-H/global7-u-q-v1`. This is the same two local
contradictions, with no new region, actual Lean leaf or global coverage
claim. A separately pinned aggregate supplement can clear the exact common
denominator and avoid rounding entirely.
