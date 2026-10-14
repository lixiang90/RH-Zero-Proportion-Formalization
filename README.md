# RH Zero Proportion Formalization

Author: **Li Xiang** ([lixiang90](https://github.com/lixiang90)).

Lean proofs and exact rational certificates for lower bounds on the proportion
of Riemann zeta zeros on the critical line. This repository contains the current
refinement and preserves the previous proofs and verification history.
Historical research papers are maintained in [RH-Weil](https://github.com/lixiang90/RH-Weil).

The latest formalized bound is

\[
 \kappa=\frac{39282451209654051457408555553}{58319774788300000000000000000}
 =0.673570008667708719595754467355\ldots,
\]

or **67.357000866770871959575446…%**. It concerns **simple** critical-line zeros
relative to all nontrivial zeros counted with multiplicity. It also gives
the same lower bound for distinct critical-line zeros. Every proportion below
\(\kappa\) holds for all sufficiently large heights, both on \( (T,2T] \) and
on \( (0,T] \). In particular **67.3570008667%** holds eventually.

This strictly exceeds the [website record checked on October 14, 2026](https://www.riemannzeta.fun/submissions/master-of-puppets4),
\(667801670564118872522651/991436171500000000000000\), by approximately
\(6.7191492529210\times10^{-9}\) percentage points. The improvement refines
the rational precision of the same nine-point Gram-defect certificate and
window bounds. It introduces no new window or analytic assumption.

The [final Lean module](GramDefectRecord/Final.lean) proves the exact comparison
and all four actual simple/distinct counting conclusions. Ordinary Lean
compilation and a fresh six-root axiom audit passed. Independent nanoda
checked **74,963 declarations with no errors**. Only `propext`,
`Classical.choice`, and `Quot.sound` were permitted. See the
[formal report](verification/gram-defect-20261014/formal-kernel.json),
[independent report](verification/gram-defect-20261014/independent-kernel.json),
[kernel transcript](verification/gram-defect-20261014/nanoda.log), and
[mathematical explanation](docs/gram-defect-refinement-20261014.md).

The finite objective and its denominator are both scaled by 1000, preserving
the real weights, pressure and span capacities. The new certified floor is
\(85638285989/10^{13}\); the sharpened window floor is
\(672168410564118874775945444401/10^{30}\). The unchanged counting formula
\((H_W^- - B)/(1-c)\), with \(B=436674/10^8\), gives the exact result above.

## Previous joint frame pair proof

The previous **66812491/99194552 = 67.35500050446319…%** result remains in
`RHWeilRecord.JointFramePair`. Its complete proof passed ordinary Lean and
independent nanoda replay of 84,362 declarations. Its
[formal report](verification/joint-frame-pair-complete-formal-kernel.json),
[independent report](verification/joint-frame-pair-complete-independent-nanoda.json),
[paper](papers/joint-frame-pair-simple-critical-paper.tex) and
[proof guide](docs/joint-frame-pair-formalization.md) are preserved.

The improvement pays both the eight-point frames and their nine-point
compatible pairs. Forty of the 241 original cells receive new duals, including
four closed branches of cell 17; the other 201 keep their original witnesses.
Ten compatible-pair domains receive twenty closed branches. The complete
2,399-domain cover retains all 47 previous replacements with their 84 branches
and all 2,342 other original duals. The 425 used tangent points belong to the
original certified kernel table. Real gaps, shared span squares, finite box
residuals and branch endpoints are all retained.

The global eight-point floor is 805094/10^8. The resulting outer-case bound is
1610897/200000000; the complete low--low bound is larger. Both pay the new
uniform nine-point reward 805448/10^8. The unchanged lossless counting bridge
retains every off-line reflected pair and all zero multiplicities.

For Lean, the 201 retained YA payments use a separately archived base-only
33-variable dual adapter, proving the same floor with no additional tangent
or analytic input. It produces 244 numeric frame checks; the mathematical
witnesses and this formal adapter are both preserved.

## Preserved results

The previous **941021/1397107 = 67.3549699486152…%** result remains in
[NinthSpan.lean](RecordProportion/NinthSpan.lean). All four actual counting
theorems passed ordinary Lean compilation, a fresh transitive axiom audit,
and independent nanoda replay of 82,804 declarations. Only `propext`,
`Quot.sound`, and `Classical.choice` were permitted. See its preserved
[Lean report](verification/ninth-span-complete-formal-kernel.json),
[independent replay](verification/ninth-span-complete-independent-nanoda.json),
and [guide](docs/ninth-span-formalization.md).

The older **66812491/99194740 = 67.3548728491047…%** proofs and single-file
submission also remain unchanged. All preceding tracked paths and mathematical
records are preserved. The preceding repository introductions are archived
[at c260](docs/c260-repository-status-20261010.md) and
[at c403](docs/c403-repository-status-20261011.md).

## Fixed environment and reproduction

| Component | Pinned version |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc2` |
| Mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` |
| Zeta23 | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |
| lean4export | `b18d673bd29b476466a51a3be1012df2ed322b10` |
| nanoda | `418320295890faed83a96fd97907b12a3b6728c2` |

```powershell
lake --no-cache exe cache get
lake --no-cache build +GramDefectRecord:olean
python -B -X utf8 scripts/gram_defect_exact_inputs.py
python -B -X utf8 scripts/verify_gram_defect_record.py
```

The pinned compiler, dependency commits, source hashes and exported proof
graph are bound by the verification receipts. Recorded WSL-cache commands
describe the measured local environment; fresh checkouts build their own
dependencies. The two libraries are separate because the inherited source
chains share declaration names. Build or import `GramDefectRecord` for the
latest result; do not import it together with `RecordProportion` in one module.

## Website submission

The new result has passed local Lean and independent nanoda verification;
it has **not been submitted to or accepted by the website**. The displayed
leaderboard therefore still has its preceding record. Modular verification
does not by itself establish the website's whole-file resource checks.

The repository's earlier website compilation attempt exited with code 137. The old
[single-file submission](submission/proof/Solution.lean) is preserved exactly;
no accepted website record has been obtained. Publishing a modular Lean
proof, independently replaying its kernel graph, and passing the site's
whole-file resource limits are separate steps. See the preserved
[submission requirements](docs/submission-contract.md),
[failure diagnosis](verification/site-compilation-exit137/diagnosis.json),
and [resource optimization](docs/resource-optimization.md).

The preceding README is archived [here](docs/gram-defect-previous-readme-20261014.md).
