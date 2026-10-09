# RH Zero Proportion Formalization

Author: **Li Xiang** ([lixiang90](https://github.com/lixiang90)).

Lean formalization of the critical-line zero-proportion result developed in
[RH-Weil](https://github.com/lixiang90/RH-Weil), with reproducible exact certificates
and the corresponding [paper](papers/expanded-nine-point-tangent-simple-critical-paper.tex)
([PDF](output/pdf/expanded-nine-point-tangent-simple-critical-paper.pdf)).

The target is **66812491/99194740 = 67.3548728491047…%** of simple critical-line
zeros, relative to all nontrivial zeros counted with multiplicity. This implies
the same lower bound for distinct critical-line zeros, the website's scoring object.

**Status: the complete local proofs passed; the first reported website attempt failed during Lean compilation.**
The continuous certificate and named dyadic and cumulative simple-zero theorems
compile in the pinned environment. The three website declarations, concerning
distinct critical-line zeros, also compile and pass independent nanoda replay of
79,699 declarations. The modular declarations also pass the pinned Comparator core
(statement and primitive matching, axiom checks and default Lean kernel replay).
Fresh transitive audits contain only the three permitted axioms.
The 1,996,187-byte single file also passed Lean compilation, transitive axiom
audits and independent replay of all three theorem dependency graphs (79,750
declarations). Resource compliance, the official Comparator run and website
acceptance remain separate requirements. The user-provided website log reports
Solution.Candidate exiting with code 137 after 683 seconds. Memory exhaustion
is the leading diagnosis, not an established OOM event; see the [failed-attempt record](verification/site-compilation-exit137/diagnosis.json).
No website record has been obtained, and resource optimization remains in progress.

A same-Linux AM component pair reduced compilation from 553.329 to 448.761
seconds (18.9%); its small PSS change does not establish a memory gain.
The first replacement trial was cut off after memory-resource checks failed.
A further scheduling version is undergoing full verification. See the
[resource evidence](verification/linux-memory-time-20261010/README.md).

| Component | Verification status |
|---|---|
| Actual simple-to-distinct counting bridge and exact trusted website count identities | Full modules compiled; only permitted axioms |
| Integer and real Floyd-closure soundness | Full module compiled; only permitted axioms |
| Sparse integer dual and real box correction | Full module compiled; only permitted axioms |
| Complete finite-data certificate | All 1,224 original integer conclusions, orbit/shape and primitive-bound transport compiled; only permitted axioms |
| Imported AM analytic chain and original PC8 certificate | Full module compiled; only permitted axioms |
| Separated AM majorant and spectral/count transport | Full modules and packed single-file analytic chain compiled; only permitted axioms |
| Complete 482 × 482 physical-pair coverage and 42-column row evaluation | Full modules and fresh axiom audits passed |
| Complete point/tangent guards and extra-span membership | Full module and 12 fresh axiom audits passed |
| Continuous nine-point certificate | Full unconditional module and five fresh axiom audits passed |
| Named simple-zero dyadic and cumulative corollaries | Actual Zeta23.N0simple/Ncount; full module and fresh axiom audits passed |
| Three final website declarations and independent replay | Modular Lean, pinned Comparator core and independent nanoda passed; nanoda checked 79,699 declarations |
| Complete single-file candidate | Lean compilation, four axiom audits and independent replay passed; official runtime/memory compliance pending |

Snapshot results and their scope are recorded in `verification/` and `docs/`.
See [resource optimization](docs/resource-optimization.md) for measured proof-checking improvements and their limits.
The original Lean numeric transcription had two incorrect column entries; that
uncompleted run was terminated, and the generator now derives and checks the
original column order. The saved JSON certificate is unchanged. A passed data
or helper check does not establish the complete headline theorem.

## Fixed verification environment

The [website contract](https://github.com/josusanmartin/riemann/blob/6664d243005e12e155c19775b83f53721757414b/challenge/contract.json)
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
lake --no-cache build +RecordProportion.SimpleCorollary:olean +RecordProportion.TrustedCounts:olean
python -B -X utf8 scripts/am_expanded_nine_point_certificate.py --check
```

The build command checks the complete simple-zero theorem and its finite and analytic
dependencies. The website entry is in `submission/candidate-entry.lean.in`; its three
declarations require the exact website-generated `ChallengeDeps.CandidateSpec`.
The Python check uses only the standard library and verifies the saved 2,399
rational dual certificates. It does not constitute a full Lean proof.
The committed `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` pin the
environment. The draft bundler retains proof terms and compacts integer literals
without changing their values. The checked candidate is in submission/proof/;
its local Lean pass does not establish official submission acceptance.
The complete draft is within the 2 MB source limit; see [single-file packaging](docs/single-file-packaging.md) for the exact scope of its checks.
The bundler follows local import dependencies and places each module in an ordinary
section to preserve its local options and scopes. The saved complete candidate passed compilation; every subsequent source
revision requires a new complete check. Development helpers are in `RecordProportion/`; immutable inputs are in
`output/`, `formal/certificates/`, and `reviews/`. The original research papers
and history remain in RH-Weil; this repository owns all new proportion formalization.

Mathematical research remains paused until formalization and website submission are complete.
