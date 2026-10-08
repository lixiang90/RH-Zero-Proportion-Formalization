# RH Zero Proportion Formalization

Author: **Li Xiang** ([lixiang90](https://github.com/lixiang90)).

Lean formalization of the critical-line zero-proportion result developed in
[RH-Weil](https://github.com/lixiang90/RH-Weil), with reproducible exact certificates
and the corresponding [paper](papers/expanded-nine-point-tangent-simple-critical-paper.tex)
([PDF](output/pdf/expanded-nine-point-tangent-simple-critical-paper.pdf)).

The target is **66812491/99194740 = 67.3548728491047…%** of simple critical-line
zeros, relative to all nontrivial zeros counted with multiplicity. This implies
the same lower bound for distinct critical-line zeros, the website's scoring object.

**Status: formalization in progress; no website record has been submitted or accepted.**
The paper and Python certificate retain their documented PC8 admission scope.
The pinned environment and its common dependencies have been built. The complete
zero-proportion theorem is still being assembled and checked.

| Component | Verification status |
|---|---|
| Actual simple-to-distinct counting bridge | Full module compiled; only permitted axioms |
| Integer and real Floyd-closure soundness | Full module compiled; only permitted axioms |
| Sparse integer dual and real box correction | Full module compiled; only permitted axioms |
| Packed finite-data snapshot | Orbit, reflection, sizes and 49 fixed points compiled; complete dual and geometric coverage checks pending |
| Imported AM analytic chain and original PC8 certificate | Full module compiled; only permitted axioms |
| Separated AM majorant and spectral/count transport | Full modules compiled; only permitted axioms |
| Continuous nine-point certificate, complete geometry and point guards | Assembly and full checks pending |
| Three final website declarations and independent nanoda replay | Pending |

Snapshot results and their scope are recorded in `verification/` and `docs/`.
A passed data or helper check does not establish the complete headline theorem.

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
lake --no-cache exe cache get
lake --no-cache build +RecordProportion.AnalyticBridge:olean +RecordProportion.CountBridge:olean +RecordProportion.FloydSoundness:olean +RecordProportion.SparseDualSoundness:olean
python -B -X utf8 scripts/am_expanded_nine_point_certificate.py --check
```

The build command above checks the completed analytic and auxiliary modules.
A complete `lake build` also requires the finite-certificate work still in progress.
The Python check uses only the standard library and verifies the saved 2,399
rational dual certificates. It does not constitute a full Lean proof.
The committed `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin the
environment. The draft bundler retains proof terms and compacts integer literals
without changing their values; its output is not a verified submission.
The bundler follows local import dependencies and places each module in an ordinary
section to preserve its local options and scopes. Full compilation of the resulting
single file remains mandatory. Development helpers are in `RecordProportion/`; immutable inputs are in
`output/`, `formal/certificates/`, and `reviews/`. The original research papers
and history remain in RH-Weil; this repository owns all new proportion formalization.

No further mathematical research is being pursued while this formalization is incomplete.
