# Website submission materials

Upload [proof/Solution.lean](proof/Solution.lean) at
[riemannzeta.fun/submit](https://www.riemannzeta.fun/submit).
The complete proof is one UTF-8 file and imports only the fixed trusted
challenge, Mathlib and Zeta23 packages. Source hashes and the exact byte
count are in [manifest.json](manifest.json).

| Form field | Value |
|---|---|
| Public display name | `Li Xiang` |
| Suggested result name, if requested | `lixiang90-alternating-window-20261015` |
| Numerator p | `3338957652820594373879991756052499665323` |
| Denominator q | `4957023073704306225950000000000000000000` |
| Method | `Exact local-floor and alternating-series refinement of the nine-point Gram-defect proof` |
| Coding harness, optional | `Codex` |
| AI model, optional | Leave blank unless supplying the actual model attribution |

The score is a proportion: enter these integers unchanged, without a
factor of 100. It corresponds to
**67.3581220659003966368436248070186379025859…%**.
The increase over the accepted ajp88 record is approximately
**4.71819935420 × 10⁻⁸ percentage points**. This is a small improvement in
the certificate and analytic enclosure.

Suggested summary:

```text
Refines the accepted ajp88 reweighted nine-point Gram-defect proof. Exact replay of every leaf in its 48-root certificate permits the higher local floor c = 859538525913875481/10^20, with the proof tree, weights and pressures retained. At theta = sqrt(2)/2, theta^2 = 1/2 permits exact rational evaluation of inherited alternating cosine and sinc polynomials, sharpening the AM window floor. The counting formula (h-B)/(1-c) gives a strict exact improvement over the ajp88 record, about 4.72e-8 percentage points. The proof includes dyadic and cumulative bounds for distinct critical-line zeros, and the stronger simple-zero bounds. The ordinary Lean checks are rebuilt at the higher floor. Original attribution and licenses are retained.
```

The same fields are in [submission-fields.json](submission-fields.json).
The source contains the three root declarations required by the website:
`candidate_strict_improvement`, `candidate_critical_line_bound`, and
`candidate_critical_line_bound_cumulative`. It does not define either
trusted score constant. Root counting functions are related to their
Zeta23 copies by two reflexive proofs.

The package has **not been uploaded to or accepted by the website**.
The site's live record must still be below this exact fraction when
submitting; strict comparison is part of the proof. Local verification
does not establish the website's sandbox resource limits or acceptance.

See the [mathematical explanation](../../docs/alternating-window-refinement-20261015.md)
and the verification receipts in `verification/gram-defect-20261015`.
