# W10 conditional submission draft

**Not ready for website submission. No higher unconditional bound is claimed.**

The exact candidate is `3338842690820594373879991756052499665323/4956700000000000000000000000000000000000`, or **67.3601930885588067440029002371033079533358887969818629329997780781568382189763350616337483%**.
The website truncates this to **67.3601930885%**; the rounded value is **67.3601930886%**.
It would exceed [attempt-024](https://www.riemannzeta.fun/submissions/attempt-024)
by **0.0020623177092726177911780464808968542776149092142970525370293301724216617704377616678384 percentage points** if the remaining finite premise is discharged.

The exact admissibility, pressure and conditional simple/distinct zero-count
transfer have passed ordinary Lean checks. The complete finite data still
require their own full Lean proof. A candidate field draft is available in
[submission-fields.draft.json](submission-fields.draft.json); it is not a
submission manifest and must not be uploaded as a verified result.

The [self-contained conditional base](proof/ConditionalBase.lean) has passed
ordinary Lean compilation in a trusted-package-only environment. Its exact
[readable expansion](uncompressed/ExpandedConditionalBase.lean) and
[byte-bound compilation receipt](conditional-base-verification.json) are
included. This file retains the explicit local-floor hypothesis and is not
the website's unconditional `Solution.lean`.

The [conditional replay receipt](../../verification/w10-20261016/conditional/verification.json)
records successful default Lean kernel and independent nanoda replay of the
modular conditional roots. The sealed single-file conditional roots also
passed their own default-kernel replay, transitive axiom check and nanoda
replay. Both remain conditional.

The strict standalone-versus-modular comparison **failed** at
`FinalConditional.SeparatedFloor`: the first detected difference is that real
numeral instances refer to different proof constants after single-file
elaboration. The diagnostic and failure
log are preserved with the receipt. No successful strict cross-version or
website-statement comparison is claimed.


Read the [mathematical note](MATHEMATICAL-NOTE.zh-CN.md) and
[conditional counting module](../../StructuralW10Cert20261016/FinalConditional.lean).
The precise analytic premise is `FinalConditional.SeparatedFloor`.
[FiniteConditional.lean](../../StructuralW10Cert20261016/FiniteConditional.lean)
reduces it to an explicit executable finite-check premise; it does not assert
the successful evaluation of the full concrete data.

The website requires one UTF-8 Lean file of at most 2,000,000 bytes and the three
unconditional fixed declarations. The current modular research files do not
satisfy this submission boundary. Final materials are generated only by
`prepare_materials.py` after the exact upload passes all required checks.

The complete finite partition has 95,778 branches, 95,615 numerical leaves,
163 empty leaves and one reflection leaf. Its complete independent integer
audit passed with no unresolved frontier. See the
[reproduction commands](../../research-20261016-w10-cert/REPRODUCE-CERTIFICATE.txt)
and the [full audit receipt](../../research-20261016-w10-cert/independent-audit-complete.json).
The currently assembled complete source is 5,777,945 bytes. It still needs a
full concrete Lean check and a substantially smaller submission encoding.
