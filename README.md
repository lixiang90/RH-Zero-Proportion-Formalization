# RH Zero Proportion Formalization

Author: **Li Xiang** ([lixiang90](https://github.com/lixiang90)).

The website's [attempt-024](https://www.riemannzeta.fun/submissions/attempt-024)
now proves **67.3581307708%**, exceeding this repository's completed October 15
bound below. **The old upload is no longer a record improvement.**

The fixed ten-point candidate targets **67.3601930885588067…%**. Its exact
parameters, executable integer leaf checker, initial-domain proof and coverage
machinery are being formalized in `StructuralW10Cert20261016`; full finite
coverage and isolated submission verification must finish before it is
described as a proved improvement. Current draft materials remain marked
`upload_ready: false`.

The complete discovery tree now has **95,615 numerical leaves, 163 empty
leaves and one reflection leaf**, with no unresolved frontier. Its independent
integer audit passed. The actual full-tree Lean computation, a size-compliant
upload, and its complete dual-kernel replay remain unfinished. The
[conditional materials](submission/w10-20261016/README.md) include a
self-contained conditional proof base. Both the modular conditional roots and
the sealed conditional roots passed their own default Lean kernel and nanoda
replays. The strict comparison between these two versions failed at a numeral
instance proof reference; this failure is preserved in the
[conditional verification receipt](verification/w10-20261016/conditional/verification.json).
The complete source currently assembles to **5,777,945 bytes**, exceeding the
website's 2,000,000-byte limit. These materials are explicitly **not ready for
website submission**.

The completed October 15 bound for critical-line zeros is

\[
\kappa=\frac{3338957652820594373879991756052499665323}
{4957023073704306225950000000000000000000}
=0.6735812206590039663684362480701863790258\ldots,
\]

or **67.3581220659003966368436248070186379025859…%**. It improves the
[accepted ajp88 reweighted nine-point record](https://www.riemannzeta.fun/submissions/ajp88-reweighted-nine-point)
by approximately **4.71819935420 × 10⁻⁸ percentage points**.

The bound concerns **simple** critical-line zeros relative to all nontrivial
zeros counted with multiplicity. It also applies to distinct critical-line
zeros. For every \(\varepsilon>0\), the proportion \(\kappa-\varepsilon\)
holds at all sufficiently large heights, both on \((T,2T]\) and \((0,T]\).
The [final module](GramDefect20261015/Final.lean) states all four actual
counting conclusions.

## Two refinements of the existing method

- **Higher local floor:** the same 48-root certificate permits
  \(c=859538525913875481/10^{20}\), raising its numerator by `69444403627`.
  Exact replay checks 10,937 numerical leaves, 419 reflection leaves and
  108 root conditions. The limiting leaf retains positive integer margin
  `235234080000000000`; one further numerator unit fails that fixed witness.
- **Sharper window enclosure:** inherited alternating cosine and sinc
  inequalities are evaluated exactly at \(\theta^2=1/2\), where
  \(\theta=\sqrt2/2\). They give
  \(h=6721684105641188747759983512104999330646/10^{40}\).

The window coefficients, tree, tangent data, weights and pressure
\(B=437688000000/10^{14}\) are retained. The existing counting formula
\(\kappa=(h-B)/(1-c)\) gives the result. This is a small improvement within
the established method. The [mathematical explanation](docs/alternating-window-refinement-20261015.md)
details the certificate and analytic comparisons. A separate
[bottleneck analysis](docs/certificate-bottlenecks-20261015.md) identifies
conditional research ceilings and explains why further Taylor terms alone
cannot raise the present window numerator; it proves no stronger
zero-proportion bound.

## Structural research, 16 October 2026

New research replaces isolated window minima with bounded state potentials
that cancel between overlapping windows, and adds longer-range pairs in
reoptimized ten-point certificates. The conditional counting transfer for
`17/20`-separated gaps, the potential range on that domain, fractional pinching,
the matrix Fenchel bound, affine supports and finite-flow payment have been
formalized separately. Exact arithmetic
replay supports a stronger overlap candidate, but its complete finite-data
instantiation in Lean remains open. An early ten-point candidate was refuted;
its replacement parameters remain a numerical research candidate.

**These are research results, not a newly proved zero-proportion record.**
See the [structural research report](docs/structural-research-20261016.md),
[certificate compression analysis](research-20261016/certificate-compression-summary.md)
and [submission status](submission/structural-20261016/status.json).
The proved proportion and upload below are unchanged.

## Verification and submission

**Verification of the completed October 15 bound: passed.** Both proof forms passed ordinary Lean
compilation, trusted-statement comparison, transitive axiom checks,
default-kernel replay and independent nanoda replay with unchanged input hashes.

| Proof form | Status | Nanoda declarations |
|---|---|---|
| [Modular proof, five roots](verification/gram-defect-20261015/lean/modular/verification.json) | Passed | 74945 |
| [Upload file, three website roots](verification/gram-defect-20261015/lean/single/verification.json) | Passed | 74925 |

Only `propext`, `Quot.sound` and `Classical.choice` are permitted. Supporting
audits include the [finite replay](verification/gram-defect-20261015/finite-margin.json),
[independent structural review](verification/gram-defect-20261015/independent-finite-review.json),
[exact score](verification/gram-defect-20261015/exact-score.json) and
[packaging review](verification/gram-defect-20261015/packaging-review.json).
These supporting calculations are separate from the kernel checks.

The website upload is [Solution.lean](submission/gram-defect-20261015/proof/Solution.lean).
[Submission instructions](submission/gram-defect-20261015/README.md),
[form fields](submission/gram-defect-20261015/submission-fields.json) and the
[manifest](submission/gram-defect-20261015/manifest.json) provide the exact
integers, summary, byte count and source hashes. The file remains below the
2,000,000-byte limit. The candidate has **not been submitted to or accepted
by the website**; local verification does not establish its sandbox limits
or acceptance against a future live record.

## Source and reproduction

The accepted [upstream source](formal/upstream/ajp88-reweighted-nine-point.lean)
is preserved at site commit `e08fce410ba008ff5c5a03215d9b6bfb3ab91200`,
including inherited attribution and licenses. The new refinements are by
Li Xiang. The independent library is `GramDefect20261015`; import it
separately from `GramDefectRecord` and `RecordProportion`, whose inherited
global declaration names overlap.

Follow the [runtime setup guide](scripts/setup_record_20261015/README.md)
for pinned dependencies, Linux/WSL setup and verification prerequisites.
From the repository root, regenerate and check the artifacts with:

```powershell
python -B -X utf8 scripts/extract_record_20261015.py
python -B -X utf8 scripts/finite_margin_20261015.py
python -B -X utf8 scripts/window_refinement_20261015.py
python -B -X utf8 scripts/final_record_20261015.py
python -B -X utf8 scripts/bundle_record_20261015.py
python -B -X utf8 scripts/review_packaging_20261015.py
python -B -X utf8 scripts/analyze_certificate_potential_20261015.py
```

Then run the verification driver under the prepared Linux runtime, using
an empty work directory; `--resume` permits only hash-checked reuse:

```bash
python3 scripts/verify_record_20261015.py --mode all --work-dir /var/tmp/rh-zero-20261015/recheck
```

| Component | Pinned version |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc2` |
| Mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` |
| Zeta23 | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |
| Comparator | `273294467ce06429e6667ece7f5699f8678c9f4e` |
| lean4export | `b18d673bd29b476466a51a3be1012df2ed322b10` |
| nanoda | `418320295890faed83a96fd97907b12a3b6728c2` |

Historical proofs and receipts remain available. The preceding repository
overview is [archived here](docs/gram-defect-previous-readme-20261015.md).
Historical research papers are maintained in [RH-Weil](https://github.com/lixiang90/RH-Weil).
