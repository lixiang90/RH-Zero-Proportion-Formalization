# Independent actual-sextic STATIC replay

The completed exact stdlib replay passed in 1,187 ms. It imports no producer,
optimizer, numerical array library or Lean tool. The producer and every bound
input remained byte-identical. The auditor's initial metadata-adapter attempt
stopped at the old model's `blocks` field before numerical replay; correcting
that auditor-only field name led to the one completed replay recorded here.

Run the independent checker read-only with:

```powershell
python -S -B -X utf8 research-goal-20261017-actual-sextic-audit/independent_replay.py
```

The frozen receipt was created by the same command with `--write-receipt`.
That option refuses to replace an existing receipt. Do not regenerate or edit
the producer packet to repeat this audit.

The check covers:

- All 41 original positive ledger weights and the nine strict lower-gap
  margins of the fixed cell. Each new anchor and radius is independently
  recovered from its whole-span DBM bounds.
- All 792 normalized-W interval coefficients against the literal `qi30`
  table in the already proved `WindowJetTableData.lean` source. No old F0 or
  old w-prime literal coefficients supply a new envelope.
- The 287 point derivative intervals (orders 0 through 6 on 41 fixed
  anchors), using a direct sum of fixed-scalar intervals instead of the
  producer's Horner loop. The derivative-order remainder is
  `(44/7)^24 * |p-n|^(24-q)/(24-q)!`.
- All 658 whole-grid seventh-derivative intervals, using degree 16 and
  remainder `(44/7)^24 * (1/2)^17/17!`, plus the outward decimal absolute
  bounds and exact span-to-grid coverage.
- Every T6/A6/L6 and U5/E6 coefficient. In particular the last energy error
  coefficient is `eps6/720 + M7*R/5040`, and the derivative error's sixth
  coefficient is `M7/720`. The odd errors use `|d| <= R` to pay an adjacent
  even power; mu0 supplies the new absolute energy term.
- All 287 span powers and 41,794 exact coefficients by a closed multinomial
  expansion, independently of the producer's repeated multiplication.
- All 2,501 shift plans and 206,278 little-endian uint16 moment references:
  exact canonical target, per-plan injectivity, complete stream consumption
  and use by the stated rows. The shared nine-coordinate moment basis has
  5,005 monomials and target degree at most six.
- The one unsoftened absolute-energy row and 180 free-gradient scalar/M0
  row descriptors. Only P5 is multiplied by the constant or a single y
  coordinate; the nonnegative error E6 is not multiplied. No degree-eight
  M1 localizer is introduced.

The old 14,383 rows and 73 PSD blocks are preserved by their frozen model
hash, rather than replaced by the new envelopes. Their separate independent
structural audit is in `research-goal-20261017-degree6-audit`.

This is a finite representation and arithmetic audit. The coefficient
source has existing actual Lean soundness APIs, but these new exact-rational
point and whole-grid instances have not been supplied as concrete Lean
proofs. No point or pseudo-moment vector was evaluated, no extension of the
old exact 714 moments was tested, and no strict projection shrink, cell
exclusion, global floor or new zero proportion is claimed. The free-gradient
rows apply to global minima in this interior cell; this is not an arbitrary
low-energy-window classification.
