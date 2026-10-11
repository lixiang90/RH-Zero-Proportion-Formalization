# Joint frame and pair proportion: Lean verification addendum

Author: Li Xiang (lixiang90). Date: 2026-10-11.

The additive namespace `RHWeilRecord.JointFramePair` proves the exact lower
proportion 66812491/99194552 = 67.35500050446319…%, strictly exceeding 67.355%.
The simple and distinct counting theorems concern actual Riemann zeta zeros,
with all nontrivial zeros counted with multiplicity in the denominator.
For every ε>0, the ratio p−ε holds at every sufficiently large height,
both on (T,2T] and on (0,T]. The local theorem has no finite certificate premise.

The complete new proof passed ordinary Lean compilation. Seven supporting
modules have separate source-before/source-after, compiler command, output
artifact and log bindings; the final driver freshly compiled the headline
module and audited all eight roots transitively. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. No `sorryAx`, native-decide
computation axiom, or additional analytic axiom is admitted.

The pinned lean4export exporter freshly exported all eight dependency graphs.
Independent nanoda replay checked **84,362 declarations with no errors**
in **697.532 seconds**, using 4 threads.
The checker permitted exactly the same three standard axioms and rejected
unpermitted axioms. All proof sources, imported local artifacts, exporter
sources and artifacts, configuration and export bytes were unchanged
between the recorded before and after hashes.

## Audited roots

- `RHWeilRecord.JointFramePair.local_certificate`
- `RHWeilRecord.JointFramePair.simple_dyadic`
- `RHWeilRecord.JointFramePair.simple_cumulative`
- `RHWeilRecord.JointFramePair.distinct_dyadic`
- `RHWeilRecord.JointFramePair.distinct_cumulative`
- `RHWeilRecord.JointFramePair.previous_recordRatio_lt`
- `RHWeilRecord.JointFramePair.ninth_span_recordRatio_lt`
- `RHWeilRecord.JointFramePair.recordRatio_gt_67355`

## Mathematical certificate and formal adapter

The mathematical paper and certificate retain 201 original YA frame payments
and add 40 frame patches (43 closed numeric payments). The Lean adapter instead
uses independently checked base-only 33-variable dual witnesses for those
201 retained payments, with the same floor and no new tangent or analytic
input. It has 244 numeric frame payments in total. These are separate witness
representations of the same real-domain inequality; the adapter is preserved
as `output/am-joint-frame-ya-adapter.json`.

The proof covers all 241 original frames, their reflections, and the complete
2,399 compatible-pair domains. All 104 closed pair branches, physical square
boxes, signed dual residuals, integer path closures, and actual counting
transport are retained. The independent finite-data audit checks the adapter,
the original Lean tables, the complete pair cover and the exact new ratio.

## Evidence and preservation

- [Ordinary Lean and axiom report](../verification/joint-frame-pair-complete-formal-kernel.json)
- [Independent nanoda report](../verification/joint-frame-pair-complete-independent-nanoda.json)
- [Mathematical certificate check](../verification/joint-frame-pair-exact-certificate.json)
- [Generator checks](../verification/joint-frame-pair-generator-check.json)
- [Publication and old-record integrity](../verification/joint-frame-pair-publication-integrity.json)
- [Proof and reproduction guide](../docs/joint-frame-pair-formalization.md)

Ordinary report SHA-256: `f702b072ef6844833b2535e4986a0e870063e22993ef99eef19af34b8625f012`.
Independent report SHA-256: `5bcfb2e764f3cd3e7fa2d2be398ed07a164ca21960a1dc01a59a359aeca61c02`.

The previous 758 tracked paths are retained; the old README is archived
verbatim at `docs/c403-repository-status-20261011.md`. The c403 and c260
proofs, papers, single-file submission and verification history remain intact.
The mathematical paper is its original snapshot; this addendum records the
subsequent completed formal verification.

The new result has not been submitted to or accepted by the website. The
modular proof and independent replay do not establish the website's complete
single-file resource compliance. Its previous code-137 failure and the old
single-file submission remain preserved.
