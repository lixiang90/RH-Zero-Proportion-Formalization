# Joint frame and pair proportion: proof and verification

Author: Li Xiang (lixiang90), 2026-10-11. The exact target is
66812491/99194552 = 67.35500050446319…%, with reward 805448/10^8.
The preserved c403 and c260 declarations, records and submission remain intact.

## Actual statement

The new namespace is `RHWeilRecord.JointFramePair`. The final statements
use `Zeta23.Ncount`, `Zeta23.N0simple`, and `Zeta23.N0star`, rather than
abstract spectrum counts. For every ε>0 there is T₀ such that for T≥T₀,
the simple and distinct dyadic counts exceed `(recordRatio-ε)*Ncount T (2*T)`;
the cumulative versions use `Ncount 0 T`. The local theorem is on all real
eight-gap frames with gaps at least 4/5. It has no finite certificate hypothesis.

The eight audited headline roots are `local_certificate`, `simple_dyadic`,
`simple_cumulative`, `distinct_dyadic`, `distinct_cumulative`,
`previous_recordRatio_lt`, `ninth_span_recordRatio_lt`, and
`recordRatio_gt_67355` in this namespace. All eight passed ordinary Lean
and a fresh transitive axiom audit. Independent nanoda replay checked 84,362
declarations with no errors in 697.532 seconds. Both checks allow only
the three standard axioms; the [addendum](../papers/joint-frame-pair-lean-verification-addendum.md)
links the complete, source-bound receipts.

## Finite proof and adapter

The public mathematical certificate uses 39 direct frame patches, four closed
branches of frame 17, and 201 original YA lower bounds. All 241 frames and their
reflections are covered. Ten pair replacements with twenty closed branches,
47 old replacements with 84 branches, and 2,342 old duals pay all 2,399 compatible
physical domains. New tangents use 425 original points; the fixed original
continuous capture, kernel and convexity regions are retained.

The Lean proof separately adapts the 201 retained YA payments into base-only
33-variable dual witnesses. Those witnesses have no new tangent or analytic
input and prove the same floor; they are not relabelled as the public YA data.
Together with the forty original frame patches they produce 244 numeric frame
checks. Integer path witnesses prove actual closure bounds from the original
real constraints, including the four first-gap branches. Physical square
variables keep their entire [0,1] boxes and all signed dual residuals.

The 42-variable pair proof uses the original complete orbit/reflection cover,
retains or strengthens every pair payment, and handles all 104 closed branches.
All new integer checks use ordinary kernel reduction. No native_decide or new
analytic axiom is introduced. The unchanged majorant, near-pair and lossless
all-zero transport provide the four actual counting conclusions.

## Reproduction

```powershell
lake --no-cache exe cache get
lake --no-cache build +RecordProportion.JointFramePair:olean
python -B -X utf8 scripts/am_joint_frame_pair_certificate.py --check
python -B -X utf8 scripts/generate_joint_frame_pair_certificate.py --check
python -B -X utf8 scripts/verify_joint_frame_pair_kernel.py --rebuild-dependencies --linux-native-cache
python -B -X utf8 scripts/verify_joint_frame_pair_nanoda.py --threads 4
```

The Linux-cache options describe the pinned, measured local dependency cache;
a new checkout first builds its pinned dependencies. Source, artifact, compiler,
exporter and checker hashes are bound by the verification drivers. Independent
nanoda export traverses every dependency of all eight roots with only
`propext`, `Classical.choice`, `Quot.sound` permitted.

The new paper is a preserved mathematical snapshot. Its verification addendum
records later formal verification without rewriting that snapshot. The
publication checker compares all old files against c705c4a, checks the verbatim
README archive, and with --check-index also verifies the staged blobs.
Website compilation/resource acceptance is a separate, unfinished step;
the old single-file submission and its code-137 failure records remain unchanged.
