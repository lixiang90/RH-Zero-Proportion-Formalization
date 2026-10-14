# Final single-file local verification

The final upload source is
[Solution.lean](../../submission/gram-defect-20261014/proof/Solution.lean):
1,939,197 UTF-8 bytes, SHA-256
`11520f8af2d31186fc1b2b0304f2e72de29ec90e397b4f36d5792c4ec5190b48`.

The fresh run checked the three fixed root declarations against the current
trusted website templates and the exact submitted fraction. It used only
the fresh candidate/definition overlay and the pinned upstream package
paths, with no repository proof-library fallback.

- [Whole-file compilation](compile.json): passed, 509.250 seconds for the
  candidate; the trusted definition layer and templates were also compiled
  freshly. Deprecated inherited tactic warnings are retained in
  [compile.log](compile.log).
- [Statement, dependency and axiom comparison, and default Lean kernel
  replay](statement-kernel.json): passed. The complete fixed Comparator
  core transcript is in [comparator.log](comparator.log).
- [Independent nanoda replay](independent-kernel.json): **74,955 declarations
  checked with no errors**, allowing exactly `propext`, `Quot.sound` and
  `Classical.choice`; see [nanoda.log](nanoda.log).
- [Full original run receipt](full-local-verification.json): all bound
  sources, artifacts, tools and the checked exports remained unchanged.
  The solution export had 674,681,105 bytes; its SHA-256 is recorded in this
  receipt. The large export is retained locally and can be reproduced with
  the verification script.

[bundle.json](bundle.json) records assembly provenance, including separate
raw and LF-normalized source hashes. [contract-snapshot.json](contract-snapshot.json)
is the earlier **static** contract audit; its false runtime-check fields mean
that this static audit did not perform those checks. The successful runtime
checks are recorded separately above. The [trusted](trusted/) directory
contains the generated definition and statement inputs; `sorry` in the
trusted challenge template supplies only the comparison statements, never
the candidate's proof. The submitted source contains no `sorry`, `admit`,
new axioms or `native_decide`.

The [initial failed assembly](first-attempt/) and its narrowly scoped counting
interface repair are preserved. Its receipt is not evidence for the final
source. Earlier modular receipts concern different root sets and do not
replace this whole-file run.

These are completed local checks, not an upload or website acceptance. The
run does not reproduce the website sandbox or certify its resource limits.
The independently built native performance probe was unnecessary after the
original verification process completed; the recorded successful Comparator
run is the unchanged `lean --run` driver.
