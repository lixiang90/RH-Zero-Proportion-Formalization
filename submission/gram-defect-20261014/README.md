# Nine-point Gram-defect submission package

The upload file is [proof/Solution.lean](proof/Solution.lean), generated from
the `GramDefectRecord` modular proof. Its exact bound is

\[
\kappa=
\frac{39282451209654051457408555553}{58319774788300000000000000000}
=0.673570008667708719595754467355\ldots.
\]

Thus every proportion below **67.357000866770871959575446…%** holds for all
sufficiently large heights. The proof supplies the website's distinct
critical-line counting conclusions in dyadic and cumulative windows, and
also includes the stronger simple-zero counting results.

The gain over the `master-of-puppets4` record checked on October 14, 2026 is
approximately **6.7191492529210 × 10⁻⁹ percentage points**. It refines the
rational precision of the same nine-point certificate and window bounds;
the real objective weights, window and analytic inputs are unchanged.

## Upload fields

Enter the proportion as the exact fraction below. Do not multiply either
form input by 100.

| Field | Value |
|---|---|
| Record name | `lixiang90-nine-point-refinement` |
| Public author | `lixiang90` (the website account's bound value) |
| Exact numerator p | `39282451209654051457408555553` |
| Exact denominator q | `58319774788300000000000000000` |
| Method | `Exact rational refinement of a nine-point Gram-defect certificate` |
| AI model | Optional; enter the actual model used, or leave blank |
| Coding agent or harness | `Codex` |
| Proof file | `proof/Solution.lean` |

Suggested summary (below 1,000 characters):

```text
Refines R. Arun Chandru's accepted master-of-puppets4 nine-point Gram-defect proof. A 1000-fold rescaling of the integer certificate representation certifies c = 85638285989/10^13 while preserving the real pair weights, gap pressures and span capacities. Sharper rational root and trigonometric enclosures improve the window floor. The resulting exact fraction strictly improves the preceding record and proves dyadic and cumulative bounds for distinct critical-line zeros, with the stronger simple-zero conclusions also included. The single upload file contains the complete refined certificate and counting bridge together with the three fixed website theorem declarations. Original attribution and third-party license notices are retained. Fresh standalone Lean compilation, exact statement comparison, axiom audit and independent nanoda replay passed (74,955 declarations).
```

The same fields are available in [submission-fields.json](submission-fields.json).
The suggested summary describes the mathematics and assembly; it makes no
website acceptance claim.

## File contract

The UTF-8, LF upload source is **1,939,197 bytes**, strictly below 2,000,000
bytes by **60,803 bytes**. It needs no imports from this repository's proof
modules. Its imports are the pinned trusted challenge, Mathlib and Zeta23
dependencies, including `ChallengeDeps.CandidateSpec`.

It declares the three required theorems at root scope:

- `candidate_strict_improvement`: the form's `candidateKappa` exceeds the
  trusted `currentRecordKappa`.
- `candidate_critical_line_bound`: for every positive epsilon, the bound
  minus epsilon holds eventually on `(T, 2*T]`.
- `candidate_critical_line_bound_cumulative`: the same conclusion on `(0, T]`.

The website generates the two score constants from its trusted record and
the form inputs. This source neither declares nor overrides them. If the
site's trusted record changes, the strict-improvement declaration must be
checked against the updated value before submission.

The website's root `Ncount` and `N0star` are independent definition copies
of the corresponding `Zeta23` functions. The included
`GramDefectSubmissionCounts.count_eq` and `distinct_eq` each prove the
mapping with `by rfl`. The final wrappers rewrite by these identities;
they preserve the exact zero sets, distinct-zero convention and total-zero
multiplicities.

The old finite instance, literal data, final local certificate and W9 bridge
are replaced by their refined versions, rather than duplicated. Shared
generic PCell helpers are retained exactly. Anonymous sections left open at
the original module boundaries are explicitly closed, and each module's
local options and open commands are isolated in an ordinary named section.
The source uses ordinary Lean numerals without compression macros and
retains the original attribution and complete third-party notices/licenses.

## Reproduction and validation status

From the repository root, regenerate the upload source with:

```powershell
python -B -X utf8 scripts/bundle_gram_defect_solution.py
```

The generator prints its byte count, SHA-256, exact fraction, imports and
module-scope audit. It enforces the strict byte limit and rejects local proof
imports, incorrect scope closure, trusted-score declarations and forbidden
proof commands. This assembly check does not itself compile the proof.
Source hashes and file facts are recorded in [manifest.json](manifest.json).

Run the standalone validator from the repository root:

```powershell
python -B -X utf8 scripts/verify_single_solution.py
```

It compiles the full source in a fresh directory, compares all three theorem
statements to the trusted challenge statements, checks their transitive
axioms and proof graph with Lean, and independently replays the exported
graph with nanoda. An existing nonempty build directory is not used for a
fresh run; select a new empty directory with `--work-dir` when repeating
the check.

The defaults identify the recorded local Ubuntu WSL cache, not a portable
dependency installation. For another environment, configure
`--runtime-manifest`, `--package-manifest`, `--zeta-repo`, `--exporter-repo`,
`--comparator-repo` and `--nanoda-bin` (plus the matching binary provenance
or SHA-256). `--website-repo` selects the local challenge source snapshot;
`--distribution` and `--lean` can select the runtime. The validator checks
the pinned compiler, Mathlib, Zeta23, comparator, exporter and nanoda inputs.
See `python scripts/verify_single_solution.py --help` for all options and
the main README's pinned versions. Successful validation is still local.

The modular proof's Lean and independent nanoda verification passed;
see [the existing modular receipts](../../verification/gram-defect-20261014/).
For this exact standalone source, fresh local validation **passed**:

| Check | Status |
|---|---|
| Source size, imports, root declarations and scope closure | Passed |
| Fresh ordinary Lean compilation in the pinned challenge environment | Passed |
| Exact equality with all three fixed trusted theorem statements | Passed |
| Transitive axiom audit of the three fixed declarations | Passed; only `propext`, `Quot.sound` and `Classical.choice` permitted |
| Lean default kernel replay for the standalone proof graph | Passed |
| Independent nanoda replay for the standalone proof graph | Passed; 74,955 declarations, no errors |
| Website submission and acceptance | Not submitted |
| Website resource checks | Not certified by local validation |

Standalone validation receipts are recorded in
[verification/gram-defect-single-20261014](../../verification/gram-defect-single-20261014/):
[compilation](../../verification/gram-defect-single-20261014/compile.json),
[statement equality and axiom audit](../../verification/gram-defect-single-20261014/statement-kernel.json),
[independent replay](../../verification/gram-defect-single-20261014/independent-kernel.json),
the [complete local receipt](../../verification/gram-defect-single-20261014/full-local-verification.json),
and [contract snapshot](../../verification/gram-defect-single-20261014/contract-snapshot.json).
Local checks and repository publication do not mean that the website has
accepted the entry or that its resource checks have passed. Earlier upload
sources and verification receipts are preserved separately.

The [first whole-file failure log](../../verification/gram-defect-single-20261014/first-attempt/compile.log)
and [repair explanation](../../verification/gram-defect-single-20261014/first-attempt/README.md)
are retained for review. Explicit `by rfl` identities now map the trusted
counting definitions in both final wrappers. The passing receipts refer
to the repaired file and its exact SHA-256, rather than the earlier attempt.
