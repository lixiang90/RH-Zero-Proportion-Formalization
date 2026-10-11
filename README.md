# RH Zero Proportion Formalization

Author: **Li Xiang** ([lixiang90](https://github.com/lixiang90)).

Lean proofs and exact rational certificates for lower bounds on the proportion
of Riemann zeta zeros on the critical line. The research project and papers are
maintained in [RH-Weil](https://github.com/lixiang90/RH-Weil).
This repository preserves each proportion proof and its verification history.

The latest formalized bound is

\[
 p=\frac{66812491}{99194552}=0.6735500050446319\ldots>0.67355,
\]

or **67.35500050446319…%**. It concerns **simple** critical-line zeros
relative to all nontrivial zeros counted with multiplicity. It also gives
the same lower bound for distinct critical-line zeros. Every proportion below
p holds for all sufficiently large heights, both on \( (T,2T] \) and
on \( (0,T] \). In particular 67.355% holds eventually.

The additive development uses the namespace `RHWeilRecord.JointFramePair`.
The complete proof passed ordinary Lean compilation and a fresh transitive
audit of eight roots. Independent nanoda replay checked **84,362 declarations
with no errors**. Both checks admit only `propext`, `Classical.choice`, and
`Quot.sound`. See the [Lean report](verification/joint-frame-pair-complete-formal-kernel.json),
[independent replay](verification/joint-frame-pair-complete-independent-nanoda.json),
and [verification addendum](papers/joint-frame-pair-lean-verification-addendum.md).
The new [paper source](papers/joint-frame-pair-simple-critical-paper.tex)
and [PDF](output/pdf/joint-frame-pair-simple-critical-paper.pdf) document the
mathematical certificate; the [proof guide](docs/joint-frame-pair-formalization.md)
explains its separate Lean adapter and reproduction.

## Proof structure

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
lake --no-cache build +RecordProportion.JointFramePair:olean
python -B -X utf8 scripts/am_joint_frame_pair_certificate.py --check
```

The pinned compiler, dependency commits and source closure are bound by
the new verification drivers. Recorded Linux-cache commands refer to the
measured local environment; fresh checkouts build their own dependencies.

## Website submission

The website's previous compilation attempt exited with code 137. The old
[single-file submission](submission/proof/Solution.lean) is preserved exactly;
no accepted website record has been obtained. Publishing a modular Lean
proof, independently replaying its kernel graph, and passing the site's
whole-file resource limits are separate steps. See the preserved
[submission requirements](docs/submission-contract.md),
[failure diagnosis](verification/site-compilation-exit137/diagnosis.json),
and [resource optimization](docs/resource-optimization.md).
