# RH Zero Proportion Formalization

Lean formalization of the critical-line zero-proportion result developed in
[RH-Weil](https://github.com/lixiang90/RH-Weil), with reproducible exact certificates
and the corresponding [paper](papers/expanded-nine-point-tangent-simple-critical-paper.tex)
([PDF](output/pdf/expanded-nine-point-tangent-simple-critical-paper.pdf)).

The target is **66812491/99194740 = 67.3548728491047…%** of simple critical-line
zeros, relative to all nontrivial zeros counted with multiplicity. This implies
the same lower bound for distinct critical-line zeros, the website's scoring object.

**Status: formalization in progress; no website record has been submitted or accepted.**
The paper and Python certificate retain their documented PC8 admission scope.
The new Lean helper files have full proof scripts, but have not yet been compiled
in the pinned environment. They do not establish the complete headline theorem.

## Fixed verification environment

The [website contract](https://github.com/josusanmartin/riemann/blob/668e239f30c7c56494611b1825306a3d65f95537/challenge/contract.json)
fixes these versions:

| Component | Version |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc2` |
| Mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` |
| Zeta23 | `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` |
| Comparator | `273294467ce06429e6667ece7f5699f8678c9f4e` |
| nanoda | `418320295890faed83a96fd97907b12a3b6728c2` |

Only `propext`, `Quot.sound`, and `Classical.choice` are permitted transitively.
The submission must be one UTF-8 `Solution.lean` of at most 2,000,000 bytes,
prove the exact dyadic and cumulative statements and strict improvement, and
pass Lean and independent nanoda verification. See [the submission requirements](docs/submission-contract.md).

## Build and reproduce

```powershell
lake update
lake exe cache get
lake build
python -B -X utf8 scripts/am_expanded_nine_point_certificate.py --check
```

The Python check uses only the standard library and verifies the saved 2,399
rational dual certificates. It does not constitute a full Lean proof.
Development helpers are in `RecordProportion/`; immutable inputs are in
`output/`, `formal/certificates/`, and `reviews/`. The original research papers
and history remain in RH-Weil; this repository owns all new proportion formalization.

No further mathematical research is being pursued while this formalization is incomplete.
