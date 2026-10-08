# Single-file proof packaging

Author: Li Xiang ([lixiang90](https://github.com/lixiang90)).

The website accepts one UTF-8 Lean file of at most 2,000,000 bytes. Development
modules are bundled in their actual local-import order; each module is wrapped
in an ordinary named section so local options, scopes and namespace commands
have the same boundaries. Original copyright and license notices are retained.

Three source transformations reduce size without adding mathematical premises:

- Large hexadecimal and ASCII64 literals are decoded to the same natural number
  and represented by shorter ASCII92 literals or decimal notation. The Lean
  macro returns an ordinary numeral syntax node.
- Seven fixed `Nat` operations use zero-argument syntax abbreviations referring
  directly to the original fully qualified constants.
- Repeated numeral strings share a private string dictionary. Each use is
  expanded to an ordinary numeral syntax node; invalid indices are rejected.

String literals, nested comments and ordinary declaration identifiers are
excluded from operation rewriting. Python verifies every numeral roundtrip.
These checks do not replace compilation of the resulting complete Lean file.

## Checks completed

`verification/analytic-single-file-fixed-calls.json` records an actual exit-0
single-file compilation of the analytic implication and the exact website
counting identities, with 29 selected transitive axiom audits. It uses only
`propext`, `Quot.sound` and `Classical.choice`. This implication still requires
the genuine uniform finite certificate; it is not the complete result.

`verification/finite-definitions-source-encoding.json` records an actual exit-0
check of the corrected computational definitions and Floyd weakening lemmas
with the complete numeral encoding and dictionary. It checks the source
representation, not all 1,224 numerical certificate propositions.

Failed checks remain labelled as failures. In particular, the first finite
encoding run used two nonexistent audit names; its overall exit was nonzero.
The first full numeric run after the speed improvement had an invalid parser
syntax atom and also exited nonzero. Neither is counted as a passed proof.

## Complete draft under check

The first complete draft is generated with:

```powershell
python -X utf8 scripts/bundle_solution.py --entry submission/candidate-entry.lean.in --compact-layout --compact-nat-calls --compact-numeral-dictionary --output tmp/bundles/Solution.final-candidate-draft.lean
```

The locked draft generated on 2026-10-09 has 1,996,162 bytes and SHA256
`cefc97d33679bdca271d54332364716855b9cf65c88c18557a58996fcef7a5ca`.
Its manifest binds every source module and the candidate entry. It contains the
original 1,224 integer check propositions, the actual continuous W9 certificate,
and the three unconditional website declarations. That first complete attempt was stopped after an actual Geometry module build
identified a missing `noncomputable` qualification. Its exit-15 record and
termination evidence are retained; it did not complete. Its generation or the
presence of theorem names does not establish a complete verification pass.

The numerical proof first attempts a cheaper primitive-box bound. A proved
monotonicity theorem transports that bound to the original Floyd-based check;
when the attempt fails, the original exact check is evaluated instead. The
saved certificate, multipliers, original lower-bound definitions and claimed
ratio remain unchanged. This is a proof-evaluation improvement, not new
mathematical research.

The complete check uses `scripts/verify_bundle.py`. It records actual process
exit, source hashes before and after compilation, and the selected transitive
axiom dependencies. Independent nanoda replay and official website Comparator
acceptance are separate steps. No upload or accepted record is implied by a
local compilation record.

## Fixed second draft and independent checks

The complete Data module now has an actual exit-0 build and fresh axiom audit
for all 1,224 original conclusions: see
`verification/finite-data-fast-kernel-v2.json`. Point also passed its full
module build and 12 axiom audits. Geometry and Row passed after adding only the
required Geometry `noncomputable` marker. Their proofs and all numeric data
are unchanged; earlier failed builds remain explicitly failed.

The fixed second draft has 1,996,187 bytes and SHA256
`d52f013f7edcc8536a28ef3908e64a967e5b9184d6546952cb5a541dc6d65e8a`.
It uses ordinary Lean asynchronous scheduling only in the imported AM section
and four Lean workers. These scheduling settings add no premise and disable no
kernel check. Its actual whole-file compilation and four transitive axiom audits
passed in 3,099.12 seconds, with all inputs unchanged. The exact source is
published in submission/proof/Solution.lean; the record is
verification/whole-candidate-second-attempt.json. This local Lean pass exceeds
nearly all of the official total time allowance before the remaining checks.

The fixed site deploys four CPUs and 8,192 MB of memory, with a 3,200-second
Comparator timeout. Both source size and full verification runtime matter.
Partial timings or checks do not establish that the full candidate fits.

The public `scripts/verify_independent_nanoda.py` fixes the site's three-axiom
policy with `unpermitted_axiom_hard_error=true`. Its actual replay of 71,610
analytic/count declarations is recorded in
`verification/analytic-independent-nanoda-driver.json`. That replay is limited
to the analytic implication and counting identities, not the final W9 result.

`tools/ComparatorCoreAudit.lean` uses the pinned Comparator's statement,
dependency, primitive and transitive-axiom checks, followed by the same Lean
default-kernel replay. `scripts/verify_comparator_core.py` binds the tool and
parser pins, artifacts, exports and input hashes. A strict-improvement positive
test passed and a changed-statement negative test was rejected. Single-target
tests do not establish the three-target candidate, and this local core driver
does not claim Linux sandbox or official website acceptance.


## Complete modular result and remaining resource work

The unconditional W9 finite certificate now passed its full module build and
five fresh axiom audits. The named simple-zero dyadic and cumulative corollaries
also passed, using the actual Zeta23 simple and multiplicity counts with no
remaining numeric or analytic premises.

All three website declarations compiled from that complete module chain:
see verification/three-website-declarations-modular.json. A fresh independent
replay of the same compiled candidate passed for all 79,699 declarations:
see verification/three-website-declarations-modular-nanoda.json. Its observed
axioms are exactly propext, Classical.choice and Quot.sound. These are complete
modular proofs; they do not certify the single-file artifact or a website record.

The independent replay used four threads: 713.468 seconds of wall time,
2,780.58 seconds of user CPU time and 6,527,392 KiB maximum resident memory.
The pinned Comparator's Main.lean does not set num_threads in its nanoda
configuration. In the pinned nanoda, that field defaults to zero, and a value
at most one selects serial checking (src/util.rs and src/tc.rs). Consequently,
the four-thread wall time does not establish the official 3,200-second budget.
The actual four-thread AM compilation diagnostic also exceeded the site's
8,192 MB memory allowance. Proof-evaluation cost and full-process memory must
be reduced or checked under the actual official configuration before upload.
All mathematical inputs and the ratio remain fixed during that engineering.
