# Independent decode of the factored degree-six static model

One stdlib-only replay passed in 1961 ms. It imports no producer and creates no large repeated Fraction matrix. It checks:

- All 5005 canonical monomials and the unchanged old prefix.
- All 73 multiplier sources, including the eight actual-competitor polynomials and 18 legal E4 +/- P3 expressions.
- Every one of 39325 distinct coefficient-reference plans and 1416525 little-endian uint16 target moment indices, including injectivity and complete byte/plan consumption.
- All 96580 column-major matrix entries, using their exact basis shifts and multiplier references.
- All 4070 old principal forms, with identical constants and coefficient strings.
- All 180 old KKT row signs; the 5803-row adapter's exact canonical hash and sole slack-column change 714 to 5004.
- All 4290 new moment boxes, giving 8580 scalar rows and 165 all-even lower bounds of zero. No bound is applied to the energy slack.

This is a proof of consistency of the serialized representation with its cited frozen model ingredients. No solver, new point, scalar sample or Lean process is called. It does not decide whether an old 714-moment witness has an extension, prove strict projection shrink, or produce a cell/global exclusion. All actual analytic premises remain those of the separately reviewed model.

Read-only reproduction from the repository root:

```text
python -S -B -X utf8 research-goal-20261017-degree6-audit/independent_decode.py
```

The receipt was created once with `--write-receipt`; existing receipts are never overwritten. No producer output, source or older review package is changed.
