# Prepared r2 primitiveBound_sound shadow probe

This is an uncompiled file-only repair. The original baseline, r1 metadata,
and failed r1 explicit source are copied byte-for-byte. Nothing in r1 or in the
public submission is modified. Reproduce in a fresh directory by placing this
prepare.py there and invoking Windows Python; every frozen input is SHA-guarded.

Only probe line 43 changes from `simpa only [neg_mul] using hrev` to
`linear_combination hrev`. The normalized goal had moved the same Real terms
to the opposite side, so direct coefficient +1 is the intended algebraic proof.
The other three explicit tactics are unchanged. Static algebra does not establish
Lean acceptance: compile, exact theorem type, standard-only transitive axioms,
and exclusion of the original target from dependencies remain required.

The parent reports the original shadow proof and audit passed. The earlier
explicit proof failed, produced an environment with sorryAx, and had no fresh
artifact or audit. Its 0.499 seconds is not speed evidence. This repaired r2 has
not been tested. Independent tiny-probe timing cannot establish a whole-file,
default Lean replay, serial Nano, memory-fit, or website-acceptance improvement.

The new source is 8 bytes smaller than the failed explicit and 93 bytes larger
than the unchanged baseline. A raw four-line whole-source proposal would have
6070 bytes headroom, but no complete numeral-dictionary rebundling is performed.
The context, import, options, paired BEGIN/END instrumentation and post-import
environment limitations are preserved in metadata.json and r1-metadata.json.
