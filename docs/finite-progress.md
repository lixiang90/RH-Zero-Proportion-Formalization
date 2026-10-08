# Fixed expanded certificate: finite Lean formalization

The complete unconditional nine-point local certificate has now compiled
with the website-pinned Lean 4.33.0-rc2. The fixed target is
`805260/100000000`; its associated proportion is `66812491/99194740`.
New mathematical research remains paused. All numerical parameters,
sparse multipliers and the original full JSON remain unchanged.

The five terminal declarations, including `W9_local_certificate`, passed a
fresh axiom audit using only `propext`, `Classical.choice`, and `Quot.sound`.
There is no native decision procedure, custom mathematical axiom, numerical
hypothesis, or placeholder in this finite proof chain.

Whole single-file compilation, independent rechecking, the website
Comparator and submission acceptance are separate remaining obligations.
A module pass does not claim that the website has accepted the result.

## Actual formal module checks

| Module or family | Actual result | Record |
| --- | --- | --- |
| Complete 1224 original integer conclusions, 2399 orbit entries, 1224 packet shapes, primitive-to-Floyd transport | Build and four fresh audits passed; 1672.84 seconds | [finite-data-fast-kernel-v2.json](../verification/finite-data-fast-kernel-v2.json) |
| Actual old and extra point packets, all interval guards and extra-span metadata | Build and twelve fresh audits passed; 281.98 seconds | [point-soundness-formal-check.json](../verification/point-soundness-formal-check.json) |
| Complete physical 482-by-482 pair coverage and real row evaluation | Corrected formal build and five fresh audits passed; 250.05 seconds, reusing the already-built row module | [geometry-and-row-formal-kernel-v2.json](../verification/geometry-and-row-formal-kernel-v2.json) |
| Complete unconditional fixed W9 certificate | Build and five fresh audits passed; 330.72 seconds | [finite-certificate-formal-kernel-v1.json](../verification/finite-certificate-formal-kernel-v1.json) |
| Closed dyadic and cumulative simple critical-line count corollaries | Build and four fresh audits passed; 40.72 seconds | [simple-corollary-formal-kernel.json](../verification/simple-corollary-formal-kernel.json) |

Each record includes real process exits, recursive source hashes, an
unchanged-source check, named axiom output, and the actual compiler log.
Formal oleans were saved. The isolated earlier proofs are historical
milestones, rather than substitutes for these complete module checks.

## Exported mathematical interface

[FiniteCertificate.lean](../RecordProportion/FiniteCertificate.lean) exports
`RHWeil.RecordSubmission.FiniteCertificate.W9`, its admissibility,
`W9_pressure`, `W9_upper_pairmass`, and the unconditional theorem:

```lean
W9_local_certificate (g : Fin 8 → Real)
    (hg : ∀ r, (4 : Real) / 5 ≤ g r) :
  (805260 : Real) / 100000000 ≤ Zeta23Ext.BridgeW.Fw W9 g
```

It requires no unresolved integer-check, coverage, point-table, or solver
premise. The pair-mass interface is the proved upper bound `≤ 16`; the
actual mass is `15.99999987`, so no equality with 16 is assumed.

The proof covers all 32 original roots, both orientations, all physical
pairs of the 482 labelled cells, all 2399 retained labelled pairs, and all
1224 reflection representatives. The 49 fixed reflection orbits are
included. Every selected old or additional tangent row is certified on its
whole actual interval, and the sparse dual is transported to the full
continuous 42-column objective. No sampling or LP optimality is used.

[SimpleCorollary.lean](../RecordProportion/SimpleCorollary.lean) exports
`RHWeilRecord.SimpleCorollary.simple_dyadic` and `simple_cumulative`. Both
use the actual `Zeta23.N0simple` and `Ncount` definitions and the unchanged
ratio `66812491/99194740`. Their local certificate and analytic premises
are discharged by the compiled proof chain. The website entry declarations
use the weaker distinct count, and no website acceptance is claimed.

The stronger-or-low traversal is proved from the original split, cursor,
empty-cell and leaf soundness. The captured 241 original cells alone are
not treated as a completeness certificate. Original clear guards are
combined with the positive pressure lower bound 323480, exceeding the 800
integer-unit stronger-target increase. The two failed stronger single-term
clear guards are not silently assumed true.

## Fixed data and checking strategy

The full input is [am-expanded-nine-point-certificate.json](../output/am-expanded-nine-point-certificate.json),
canonical LF SHA256:

```text
3a3c8b24015162a4835f5c1d8633a4f9f8bdace26d711631dd6374c689bce04f
```

Only representative duals are packed into the new Lean data: 32054 positive
integer numerators over `10^9`, with a 9472-value dictionary. Packing uses
22-bit geometry words, shared point packets and ASCII64 numeral literals.
The `n64%` macro produces ordinary numeral syntax; the mathematical proof
checks the resulting numbers and does not assume the macro is correct.
The transparent decoder and generator roundtrip are retained for reproduction.

The complete reconstruction preserves ordered gap/span rows, enabled old
anchor rows, additional-point rows, the two-frame objective and the original
integer Floyd box. Its normalization is `Y = 5*32768*g` and
`Z = 5*10^10*32768*w`. Geometric multiplier numerators are scaled by
`10^10`, all multipliers have denominator `10^9`, and the exact integer
target is `2*805260*(5*10^10*32768)*10^9`.

The production proof first tries the same dual on primitive adjacent box
bounds. Proved integer monotonicity carries a successful result to the
unchanged original Floyd-box checker; otherwise the original full checker
is used. All 1224 final declarations retain that original conclusion.
They use ordinary kernel decisions, real top-level batches, preserved error
messages, and checks that emitted proofs contain no recovery placeholders.
Only editor information trees are disabled. No compiler or kernel check
is bypassed.

Current source pins:

```text
FiniteCertificate.lean
6c6cb5dc10588e430c28118107ad66e1da93dcd0b0e62bd579fcc92a3f078cb5
FiniteCertificateData.lean
0b12cba764e62ac55f1d7acdebc6c86cf1a26253ccb31939519b983f01b1bc59
```

## Superseded transcription and failed engineering attempts

An earlier Lean-generator snapshot manually transcribed zero-based full
square columns 38/39 as `(5,8)/(6,8)`. The original frozen insertion order
requires `(5,7)/(5,8)`. All other columns matched. The objective-identity
proof exposed this error in the Lean generator; the original JSON,
multipliers, target and mathematical certificate were not changed.
The generator now derives all 34 square columns from the ordered term
union, with explicit order and set assertions.

The old Data SHA
`917c0f7375dde03024957ea9b987030efbe5a2021f9c084a97c7559bd3ed7f2e`
run was terminated after verifying its process and command. It used
4761.921875 CPU seconds and 11918147584 bytes of working set and never
completed all 1224 checks. It is not a proof of F9. Earlier orbit and
encoding facts remain separate facts about their own tables.

The first fast emitter attempt failed on command syntax and was retained
as a failed attempt. The first formal geometry attempt needed a
`noncomputable` section after the transparent data were made explicitly
noncomputable; that annotation was repaired without changing any
mathematical body. The successful complete module records above bind the
corrected sources. Failed CBV and alternative getter diagnostics are not
part of the admitted production certificate.
