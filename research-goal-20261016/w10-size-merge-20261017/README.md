# One-pass original-certificate merge test

This test produced **zero parent merges**. It changes no old tree, point table, scalar witness, coefficient or published Lean source. No optimizer or Lean compiler was called.

At each normalized original parent, the producer tries at most two certificates: the representative of its left subtree and that of its right subtree. A successful child representative is retained; otherwise the leftmost available numerical representative is propagated. Only the original 39 support tuples and original Prüfer code are used. A parent is collapsed only if one complete actual integer checker passes, including every whole-parent tangent-validity guard and coordinate residual payment. A positive arithmetic expression with a failed scalar guard is never accepted.

| Scope | Parent tests | Accepted merges | Time inside traversal/checking |
|---|---:|---:|---:|
| Original `n = 86600000` pilot | 1,000 | 0 | 0.236538 s |
| Same pilot cells and candidates, fixed `n = 86450000` | 1,000 | 0 | 0.240781 s |
| One complete original-floor pass | 95,778 | 0 | 21.157784 s |

The 2,000 original-pilot candidates comprised 1,883 failed whole-parent tangent guards and 117 failed integer inequalities. Lowering the one approved constant did not improve the pilot, so no lower-floor full pass or parameter sweep was run. The complete original pass retains **95,615 numerical leaves, 163 empty leaves and one reflection leaf**. The 6,501,272-byte gzip packet is an audit artifact, not the website source or an assertion of compression success.

The lower pilot was chosen to preserve the requested improvement if its global energy floor could eventually be proved. The exact required floor is strictly greater than

`242125948973912479045633901091386938489600910650924364438067713 / 28009683941039967632979924905692003148800000000000000000000000000`.

The one fixed choice `86450000/10^10 = 0.008645` exceeds that threshold. Under the same inherited counting inputs and a global proof of this floor, the resulting conditional zero proportion would be

`3338842690820594373879991756052499665323 / 4956775000000000000000000000000000000000`, or approximately **67.35917387455744%**.

This exceeds the requested website record plus 0.001 percentage point by approximately `4.31e-7` in absolute proportion. This arithmetic explains the pilot threshold; it proves neither the global floor nor a new unconditional proportion. Lowering the target also cannot repair failed tangent-domain guards.

The independent replay is kept in separate `independent_merge_*` sources and receipts. It verifies the complete new root geometry, original certificate identities, actual scalar guards and integer checks, without importing the merge producer. The output is the same partition when no merge succeeds. The prior field-Huffman source accounting therefore remains applicable: **4,004,458 known retained source bytes**, or **4,132,458 bytes** with the explicit 128,000-byte future-decoder budget, against a 2,000,000-byte limit. A new Lean Huffman decoder/expander and complete cover remain unimplemented.

## A genuine uniform-energy obligation

The certified 612-leaf region includes parent `r001100`. Its total span `s = g₀ + ⋯ + g₈` lies in `[10,11]`. The left child's original witness has only one invalid whole-parent tangent, term 5 for span `(0,9)`, whose actual ledger weight is **2**. Its anchor 328704 is certified through 350112, while the parent extends to 360448. The arithmetic expression alone has positive margin, but this is not a certificate. Replacing that invalid tangent by the inherited interval lower bound is sound but fails the required energy inequality; the exact negative result is in the earlier size audit's `parent-uniform-probe.json`.

A substantive next criterion could keep the actual nonlinear contribution `2*wfun(s)` and retain valid minorants for the other terms. If `A_C(g)` is their sound combined pressure/scalar lower bound, a sufficient whole-parent condition is

`A_C(g) + 2*wfun(g₀+⋯+g₈) >= 433/50000` for every `g` in this parent.

One possible finite certificate would bound `A_C` on each fixed-total-span slice by a shared piecewise affine function `phi_C(s)`, using exact dual inequalities for the parent difference constraints, and prove `phi_C(s)+2*wfun(s)` above the target on `[10,11]`. Keeping the total span avoids the independent-coordinate loss in the current residual payment. No such `phi_C`, scalar curve proof, or successful uniform parent certificate was computed here. A case split that merely reuses both old child packets would establish the known coverage but would not reduce stored witness data. The required kernel is the inherited old `AMW.Cert.wfun`; new-window formulas need an explicit identity bridge before use.

Point templates remain a separate lossless possibility. The full audit measured 1,373,557 binary bytes for first-anchor delta streams, so they are the largest single component. Reconstructing anchors from a dual-tree potential plus a small template/escape correction would need an exact full FS roundtrip and must still pass whole-cell tangent guards. This test does not evaluate that further codec or claim an entropy lower bound.

There is no new formal exclusion, global floor, unconditional zero proportion or website-ready submission. All additional outputs use this new directory; the old 612-leaf proofs and full source-size audit remain frozen.

## Archive and reproduction

The retained archive splits the gzip packet into three parts of at most 3 MiB and stores the two pilot JSON files as separate gzip streams. `restore-inputs.json` pins every part and the complete restored bytes. The restoration helper also recreates the three old semantic cache streams from this zero-merge packet and checks their hashes against the frozen size audit. It checks any existing output byte for byte and never overwrites an existing file. These are lossless audit archives, with no implication for the website's Lean source limit.

From the repository root, restore the inputs and run the independent checker with assertions enabled:

```text
python -B -X utf8 research-goal-20261016/w10-size-merge-20261017/restore_inputs.py
python -B -X utf8 research-goal-20261016/w10-size-merge-20261017/independent_merge_replay.py research-goal-20261016/w10-size-merge-20261017/merged-tree.json.gz
```

The archived independent receipt records a complete 76.119-second replay: all 95,778 branch identities, all 95,615 original numerical witnesses, complete root geometry, scalar guards and integer inequalities passed. It found zero merged parents and minimum exact integer margin `2623983786731307008`. The producer's earlier `merged-summary.json` retains its historical `independent_replay_passed: false`; the later independent receipt and final package manifest record the completed replay separately. No additional producer or full-tree replay is needed to interpret that receipt.
