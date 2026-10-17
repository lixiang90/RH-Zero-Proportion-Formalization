# Independent replay of the fixed stationary swap comparison

The stdlib-only checker imports neither the producer nor its helper. It independently reconstructs the normalized-W derivative orders 2 through 6 at all eight saved anchors (40 intervals), all 391 selected q7/d16 whole-path grid bounds, and all 40 weighted power integrals. It expands each power in a temporary integration variable before integrating, then separately checks the binomial coefficient formula. All eight positive ledger weights, path directions, old/image hulls, the 495-term sum, the linear-row sign and the fixed 714-moment expectation match exactly.

The one replay passed in 736 ms. The upper expectation is positive, approximately **0.08156396303205875**. It does not separate the saved pseudo-moment point. This is a negative result for this fixed envelope, not a proof that every integral-based certificate fails.

No actual function sample, new point, model builder, optimizer or Lean process was called. Taylor/FTC interpretation and concrete actual interval claims remain explicit analytic proof obligations. No region exclusion, global cover or zero-proportion improvement is claimed.

Read-only reproduction from the repository root:

```text
python -S -B -X utf8 research-goal-20261017-stationary-swap-audit/independent_stationary_replay.py
```

The archived receipt was created once with `--write-receipt`. Existing receipts are never overwritten. This addon does not change the separate frozen degree-six static review or any producer source/input.
