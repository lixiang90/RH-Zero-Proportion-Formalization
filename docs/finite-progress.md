# Fixed expanded certificate: finite Lean formalization

New mathematical research is paused. The target remains
`805260/100000000`, yielding `66812491/99194740`.
The submission contract permits only `propext`, `Quot.sound`, and
`Classical.choice`; no native decision procedure, custom mathematical
axiom, or placeholder is used in these new modules.

The fixed full input is `output/am-expanded-nine-point-certificate.json`,
canonical LF SHA256
`3a3c8b24015162a4835f5c1d8633a4f9f8bdace26d711631dd6374c689bce04f`.
Its 2399 labelled domains have 1224 reflection orbits, including 49 fixed
ones. The generator checks every domain's reflected partner and both
original lower bounds. It preserves the input and all original parameters.
Only representative duals are stored in the new Lean data: 32054 positive
integer numerators over `10^9`, using a 9472-value dictionary.

`FiniteCertificateData.lean` has actual kernel proofs of every one of the
2399 orbit mappings, label reflection involution, and the count of 49
fixed representatives. Checks are split into blocks of 32 and assembled
through proved generic coverage. The version before numeric reconstruction,
2432 lines / 449615 LF bytes / SHA256
`796b0f119d324f853b7a91961ebdf8dbe6ff5711ae3bb13704812cc133801310`,
actually compiled with Lean v4.33.0-rc2, `--tstack=32768 -j1`, exit 0.
The generator `--check` actually returned exit 0 for that version.

Packing uses 22-bit geometry words, shared certified-point packets, a
frequency dictionary, and ASCII64 literals. The `n64%` term macro only
creates an ordinary numeral syntax node. All mathematical checks concern
the resulting numeral; no proof assumes correct macro decoding. The
transparent `decode64` definition and Python roundtrip are retained.
This representation avoids repeatedly reducing long string folds in kernel
arithmetic while keeping the submission source compact.

The data module now also contains the actual integer reconstruction:
ordered gap/span rows, all enabled old anchor rows, extra-point rows,
the complete two-frame objective, integer Floyd closure, and the full
box-residual lower bound. Its normalization is
`Y = 5*32768*g`, `Z = 5*10^10*32768*w`. Geometric-row multiplier
numerators are scaled by `10^10`; all multipliers have denominator `10^9`.
The exact target is `2*805260*(5*10^10*32768)*10^9`.
Numeric reconstruction is being compiled and checked; this is not yet a
proof of the physical row premises or the complete continuous theorem.

`FiniteCertificate.lean` contains real box-dual soundness, integer casting,
safe anchor-cut soundness, the exterior stronger-frame bound, rational
target arithmetic, actual F9/InCell reflection transport, and definitions
of W9 with its pressure, minimum pressure, pair mass and span budgets.
The fixed Lean and Mathlib environment is now installed. The generic
real core was independently compiled; the full layer is waiting on the
imported AM module and is not yet an admitted full certificate.

The remaining proof obligations are actual table/point guards for every
used row, closure and sparse-check transport to the real objective, all
representative dual checks, and the complete stronger-or-low-cell cover.
The old `PC8CL.walk_ok` proves the old reward predicate. It cannot directly
prove the stronger-or-low cover: that traversal must be generalized using
the original split, cursor, empty-cell and leaf guard soundness lemmas.
The captured 241 cells alone do not establish their completeness.

No uniform W9 theorem or accepted site submission is claimed here yet.

The production integer-check command now emits ordinary declarations and
saves an olean. It disables only editor information trees through Lean's
standard `withEnableInfoTree` wrapper. Error messages are preserved; each
installed individual theorem and the aggregate theorem are checked for
existence and absence of recovery placeholders. The earlier no-output run
was deliberately stopped after its PID and command line were verified;
it is not recorded as a complete certificate pass. Two short emitter API
errors were corrected before the current formal run.

`FiniteCertificate.lean` now contains the actual stronger-or-low leaf,
node and walk soundness. The original clear guards are retained: on the
actual separated domain, a single certified old kernel term is combined
with the full positive pressure lower bound 323480, which exceeds the
800 integer-unit increase in the stronger frame target. Thus two failed
stronger *single-term* clear guards are not silently treated as true.
The complete root transport explicitly consumes this pressure premise.
This written cover layer still awaits full compilation and instantiation.

## Correction of the numeric column transcription

The full run for Data SHA `917c0f7375dde03024957ea9b987030efbe5a2021f9c084a97c7559bd3ed7f2e`
was terminated after verifying PID 17668 and its exact `-o` command.
At termination it had used 4761.921875 CPU seconds and 11918147584 bytes
of working set. It did **not** complete or establish all 1224 checks.
A real objective-identity proof identified a manual transcription
error in the Lean generator: zero-based full columns 38/39 were `(5,8)/(6,8)` whereas the frozen
original problem insertion order requires `(5,7)/(5,8)`. All other columns
match. No claim from this numeric snapshot can be used to prove F9.
The earlier orbit/reflection/encoding facts concern their separate tables
and remain distinct from this failed numeric instantiation.

The generator now derives all 34 square-column positions from the original
ordered TERMS union, including both shifted frames, with explicit order and
set assertions. The frozen JSON hash, target, domains, sparse multipliers,
and point catalog remain unchanged. The next numeric source also splits
ordinary kernel declarations into real top-level batches of 16 and marks
pure data definitions explicitly noncomputable to avoid unnecessary runtime
code generation. This changes representation and compiler workload only;
the new continuous and numerical instantiation must still actually pass.

## Corrected real-layer milestones

The corrected-data isolated module `tmp/finite-stable-core.lean` has actually
compiled with `-o` and exit code 0. It proves W9 admissibility and pressure,
the genuine pair-mass upper bound, the complete 42-column objective identity,
continuous primitive bounds through Floyd closure, and generic strong-or-low
transport including the positive-pressure clear branches. The tightened
span-bound proof also compiled with `-o` and exit code 0. Exact snapshot pins
and excluded scope are recorded in `verification/finite-stable-core-isolated.json`.
These diagnostic modules do not establish the complete numeric family or
the final unconditional W9 certificate.
