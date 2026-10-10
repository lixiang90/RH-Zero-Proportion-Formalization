# Prepared primitiveBound_sound shadow probes

Source-only diagnostic preparation. No Lean, WSL, cache, or imported proof
artifact was read or executed by this preparation. The two files have not been
tested. Runtime ownership remains with the whole-driver agent.

`prepare.py` reads the hash-bound frozen r6 source and extracts the original
declaration at bytes [1933916,1936778), lines 23115–23182. It verifies exact
signature preservation and four guarded replacement lines. Its Windows output
is `PrimitiveOriginal.lean` and `PrimitiveExplicit.lean`, with equal-length
shadow names in the original namespace. The full file byte difference is +101.
All mathematical types and hypotheses are copied unchanged. Neither body calls
the existing `primitiveBound_sound` theorem.

Both files import `Solution.Candidate`. They copy the original explicit active
namespace, opens and options: global async=false, maxRecDepth=100000,
maxHeartbeats=0, the bundle/noncomputable sections, BigOperators, AMW opens and
FiniteCertificateData open. Other module-local options/opens are not imported
as source context. Identical BEGIN/END instrumentation waits for the checked
environment, emits a monotonic millisecond marker, and prints the probe type and
transitive axioms. The owner should bind the same actual r6 artifact family,
use matching CLI flags, and record the import phase separately.

The static post-target suffix audit found no explicit later attribute or
annotation command, instance, syntax extension, initialize command, or option.
The later `open AMW.Cert.PC8CLData` is deliberately not copied into the
pre-target context; later opens are scoped source commands. No later `[simp]`
attribute was found to alter the pair. This is not a semantic parsed attribute
table: the imported complete module does contain later declarations, and both
probes share that post-module environment. Thus the pair is controlled against
one another, but is not an exact reproduction of in-situ prefix elaboration.

Runtime gates still needed: actual Lean syntax/type checking; exact type
equality to the old target; fresh permitted-axiom audit; used-constant audit
excluding the original target; source/artifact hashes before and after; actual
time/CPU/resource results. A failed source is to be preserved and must not be
silently repaired inside the controlled pair. No official-fit or replay-speed
claim follows from these two compile probes.

`metadata.json` provides complete hashes and source-only guard results.
`four-line-body.diff` shows only the proposal's four body changes.
`original-extracted-declaration.txt` preserves the exact frozen declaration.
