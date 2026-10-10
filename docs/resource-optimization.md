# Verification resource engineering

The result and all numeric inputs are fixed. This work changes how ordinary
proofs are checked so the eventual single-file submission can fit the site's
time and memory limits. No new zero-proportion estimate is being researched.

The pinned [inner launcher](https://github.com/josusanmartin/riemann/blob/6664d243005e12e155c19775b83f53721757414b/scripts/run-comparator-e2b.sh#L96)
allows 3,200 seconds for the whole Comparator invocation; the
[outer job](https://github.com/josusanmartin/riemann/blob/6664d243005e12e155c19775b83f53721757414b/e2b/run-verification-job.sh#L32)
has a 3,240-second timeout. Compilation, export, comparison, serial nanoda,
and the default Lean replay share that budget. A local proof pass establishes
neither the official resource limits nor website acceptance.

## Actual bounded comparison

| Same 64 original representative goals | Baseline | Classified two-edge route |
|---|---:|---:|
| Lean proof phases | 119.710 s | 81.620 s |
| Complete scratch module compile wall | 211.532 s | 175.777 s |
| Fresh transitive axiom audit | 65 roots passed | 68 roots passed |
| Serial nanoda replay wall | 69.359 s | 53.781 s |
| Exported declarations checked | 4,317 | 4,425 |

Only subsets of propext, Classical.choice and Quot.sound were used. Input/source
hashes remained unchanged. The ordinary proof-phase reduction was 31.8%;
the serial replay reduction was 22.5%. Both are sample measurements on a shared
host. They are not whole-file speedups or an official deadline result.
See [the combined record](../verification/finite-two-edge-64-cost-comparison.json)
and its referenced independent replay records.

The primitive edge bound already pays 1,169 of the 1,224 representatives.
The new ten-candidate bound takes the original edge and all nine primitive
two-edge paths. A generic kernel theorem proves that the original full
Floyd9 entry is at most this bound, even without a no-negative-cycle premise.
The lower-box correction is monotone, so 49 representatives can use that
cheaper check. Six keep the original full closure. Classification chooses
proof syntax; it is never a hypothesis. Every conclusion remains the original
integerCertificateCheck index=true, so a wrong classification fails checking.

The generic helper is [FloydTwoEdge.lean](../RecordProportion/FloydTwoEdge.lean);
its formal module build and five fresh axiom audits passed:
[verification](../verification/floyd-two-edge-formal-module.json).
The complete isolated 1,224-target candidate also passed: ordinary compilation
exited 0, and a fresh audit of all original representative goals, the aggregate
and three transport bridges (1,228 roots) exited 0. All 58 original computational
definitions, including the full lower bound and its Boolean check, remained
byte-for-byte unchanged. Compilation took 1,538.310 seconds and the fresh audit
20.610 seconds. The archived baseline compile-plus-audit took 1,672.840 seconds;
these are different shared-host runs with different audit workloads, so the
113.920-second difference is an observation rather than a controlled full-stage
speedup estimate. See [the full-family record](../verification/finite-two-edge-full-candidate.json).

Both complete Data dependency graphs then passed actual serial independent
nanoda replay with the same 33 roots and the same configuration. The original
graph checked 6,908 declarations in 1077.766 seconds; the
two-edge graph checked 7,016 in 934.157 seconds, saving
143.609 seconds (13.3%). Both exited 0, retained their input hashes and used
only the three permitted axioms. This is a full-family replay comparison,
rather than an extrapolation from the 64-goal sample; it still covers only the
Data graph, on a shared host. The baseline reused a validated byte-for-byte
export, but actually replayed its proofs again. Export wall time is not being
compared. See [the complete replay comparison](../verification/finite-two-edge-1224-serial-comparison.json).

The public [reproduction generator](../scripts/generate_two_edge_candidate.py)
reads the committed, hash-pinned Data and generic helper. It writes only under
the ignored tmp directory and retains every original integer-check target.
Its default output uses the public formal helper import; that header variant
has not been separately compiled by the isolated record. The historical header
can reproduce the exact compiled candidate, but its scratch helper import needs
the corresponding ordinary helper artifact. Generating source alone proves
nothing; every generated original goal still needs kernel verification.

## Complete point-reflection comparison

A generic theorem proves frameCheck(label+241)=frameCheck(label) for label<241.
The candidate numerically checks the 241 original cells and transports their
results to the full original 482-label statement. Every original computational
definition and the complete extra-point and semantic suffix remain byte-for-byte
unchanged. The new Point source does not import the old Point numeric proofs.

[FrameReflection](../RecordProportion/FrameReflection.lean) passed an ordinary
formal-module build and four fresh transitive axiom audits. The complete Point
candidate compiled in 212.323 seconds; a fresh audit of the exact original
12 interfaces passed in 19.945 seconds, using only the permitted three axioms.
See [the complete candidate record](../verification/point-reflected-full-candidate.json)
and [the public helper check](../verification/frame-reflection-formal-kernel.json).
The old archived module time is not an exclusive-host controlled comparison.

Actual serial independent replay of the same 12 interfaces then gave:

| Complete Point dependency graphs | Original | Reflection |
|---|---:|---:|
| nanoda wall time | 228.141 s | 184.250 s |
| User CPU time | 223.45 s | 180.28 s |
| Declarations checked | 46,464 | 46,470 |
| Exit status / unchanged snapshots | 0 / yes | 0 / yes |

The observed wall reduction is 19.2%. The original run initially overlapped the
Data tests and whole compile; the reflected run overlapped only the whole
compile. Both used the same fixed executable, configuration and interface roots.
This is a shared-host component measurement, not a whole-submission saving.
See [the comparison](../verification/point-reflection-serial-comparison.json).
The [Point generator](../scripts/generate_reflected_point_candidate.py) now
reproduces the checked f7d766f8 source from public inputs, including actual
rejection of an isolated redirected tmp-root test.

## Earlier optimized-source reproduction

The [guarded bundler](../scripts/bundle_optimized_candidate.py) reads only
committed, hash-pinned inputs. It composes two-edge proof routing, synchronous
AM elaboration, the checked 21-declaration source pruning and existing exact
numeric compression. Its optional reflection mode inlines the checked Point
helper body. It writes into a fresh ignored tree and rejects nonempty output,
active-overlay paths, formal-source paths and disabled assertions.

```powershell
python -B -X utf8 scripts/bundle_optimized_candidate.py --reflection --output-dir tmp/optimized-repro/combined
```

The combined source has 1,998,462 bytes, leaving 1,538 bytes under the site's
2,000,000-byte source limit. Its SHA256 is
642f68af1c2f4a44db4ca7ef8955a8a5b2bbbefa81c47e69cce4d4438c69d2f0.
Generation and guarded reproduction passed; this combined single file has
not received a fresh full compilation, independent replay or Comparator pass.
The manifest states that scope explicitly.
See [the generator record](../verification/optimized-candidate-generator-perron.json).

Without reflection, the generator exactly reproduces the separately tested
1,994,836-byte source, SHA256
583c5becafd39bc083240afa64d4468be15df67a86d819ac4544b18e2bfd98c7.
That local one-thread Windows compile/audit attempt was deliberately stopped
at 3,200.500 seconds by its experimental wall guard, before a complete result
or the final four axiom audits. It reached all 1,224 integer representatives
and their aggregate, but that partial progress is not a full proof pass.
The sampled owned-process tree peaked at 8,372,035,584 bytes; the observed Lean
working-set peak was 8,343,334,912 bytes. These local observations do not establish
Linux resource compliance or an official timeout failure.
See [the cutoff summary](../verification/whole-optimized-sync-cutoff-summary.json)
and [resource trace](../verification/whole-optimized-sync-resources.json).

## Rejected and unconfirmed alternatives

Directly constructing kernel-checked reflexivity terms for four original goals
took 4.702 seconds versus 4.633 for decide+kernel and was rejected.
[Its record](../verification/direct-reflexivity-isolated-cost.json) preserves
the failed first universe choice and the repaired fresh audit path ordering.

Bare norm_num variants left the actual packed Array/List-fold expression
unsolved in a bounded basic0 trial. Failed tactic timings are not proof
speedups, and recovery placeholders were not admitted. That trial gives no
general impossibility statement about proof reflection.

A 43-slot sparse difference accumulator has a generic equality proof:
one weighted row traversal, eight prefix entries and 34 square entries
reconstruct the original 42-column lower expression for arbitrary objective
and box bounds, without row-shape premises. Its actual four-goal test passed
the original conclusions and fresh axiom checks, but took 5.860 seconds versus
4.534 seconds for the existing primitive route (29.2% slower). Serial nanoda
also passed both groups and took 5.157 seconds versus 3.375 seconds. This Array
implementation is rejected; lower paper operation counts did not predict
kernel cost. The [Lean cost record](../verification/sparse-difference-four-representative-cost.json)
and [baseline](../verification/sparse-basic-four-serial-nanoda.json) /
[sparse replay](../verification/sparse-sparse-four-serial-nanoda.json) retain
the measurements. The separately checked generic equality is useful evidence,
but gives no general impossibility result for sparse methods.

## Linux AM memory and time comparison

After the first reported website attempt exited with code 137 during compilation,
resource work moved to the pinned native Linux compiler. The supplied log reports
683 seconds in `Solution.Candidate`; it contains no kernel OOM report or sandbox
memory counters. Memory exhaustion remains the leading diagnosis, rather than a
confirmed cause. See [the failed-attempt record](../verification/site-compilation-exit137/diagnosis.json).

The new AM variant preserves the numeric inputs and original theorem interfaces.
It includes the 21 checked source deletions and eight ordinary aliases to the
pinned Zeta23 helpers, and permits at most eight proof commands between waits for
the checked environment. Parser-derived command boundaries place 162 waits; the
last wait finishes the remaining commands, and the module restores synchronous
elaboration afterward. The scheduling change introduces no mathematical premise.

One controlled pair on the same Linux runtime gave:

| Complete AM module | Synchronous aliases | Bounded asynchronous elaboration |
|---|---:|---:|
| Measured direct-Lean compile phase | 553.329 s | 448.761 s |
| Cgroup CPU time | 533.275 s | 526.109 s |
| Sampled peak PSS | 7.51 GiB | 7.45 GiB |
| Fresh audited interface roots | 20 | 20 |
| OOM kills / swap / timeout | 0 / 0 / no | 0 / 0 / no |

The harness measures the direct Lean compilation phase, including startup,
sampling, process exit, residual cleanup and binding-file rehashing. It excludes the
prior cold preparation and the outer Windows/WSL runner. Exact child-process
start/end times were not recorded separately.

The observed wall-time reduction was 18.9%. This is one pair, so repeatability
has not been established. The PSS difference was only 59.7 MiB (0.8%); it does
not establish a significant memory improvement. Both cgroup peaks reached the
8 GiB limit without a failed charge or OOM kill, leaving no demonstrated memory
headroom for an entire 8 GiB VM. Both fresh 20-root audits imported their newly
compiled artifacts and used only subsets of `propext`, `Classical.choice` and
`Quot.sound`.

Each compile used `-j4`, the same pinned compiler and native dependency cache,
a four-CPU quota, an 8 GiB memory-plus-swap limit with swap disabled, and a
1,200-second guard. Imported-artifact pages were checked cold before each run;
cache preparation time is recorded separately. The surrounding WSL VM had
32 GiB. A bounded cgroup inside that host is not an exact reproduction of the
website's 8 GiB sandbox. The control's dependency and axiom validation resumed
after a session restart using the same source and compiled-artifact hashes;
the compile was not repeated. See [the AM evidence packet](../verification/linux-memory-time-20261010/am/README.md)
for the raw traces, exact hashes and phase-gap disclosure.

The selected single-file source combines bounded AM elaboration with the
previously checked two-edge and point-reflection routes. It has 1,993,809 bytes,
leaving 6,191 bytes under the source limit, and SHA256
`f40d0cb3566d4e71a6bb624a4d4375ca3ade977d3850e14e134a8a850f4abd50`.
Its reproduction from frozen public inputs has passed. The r5 native-Linux
full-file attempt was deliberately stopped with SIGTERM after failed memory
charges and persistent sampled page pressure. Its raw proof-stage elapsed was
2,733.628 seconds, and its enclosing compile phase took 2,770.896 seconds.
The actual shared clock, starting before the current-contract build, reached
2,854.274 seconds. The observed proof-stage sum excluding prebuilt tools was
2,765.057 seconds; scoped cold preparation contributed 64.608 seconds. These
partial measurements establish no whole-pipeline runtime or official deadline
compliance. See the [completed r5 records](../verification/linux-memory-time-20261010/whole/r5-completed/README.md).

The compile's sampled process-tree peak PSS was 8,317,437,952 bytes; the
8 GiB cgroup recorded 242 failed memory charges and zero OOM kills. The
separately sampled caller/supervisor peak outside that group was 173,293,568
bytes; peaks from different times are not added. The owned Lean exited -15,
the worker/harness 241 and the outer driver 1, with timeout false. This is an
intentional local resource cutoff, not an established mathematical rejection,
kernel OOM kill or website timeout. A single proc page-wait snapshot and
cumulative read-byte/fault counters do not identify a proof culprit or prove
deadlock. The experimental `-j4 --tstack=32768` invocation and separate phases
inside a 32 GiB WSL VM are not the official retained-strings sandbox pipeline.

No complete f40 compilation, fresh three-root axiom audit, independent replay,
export or current-contract Comparator pass was obtained. The allowed axiom set
remains `propext`, `Quot.sound` and `Classical.choice`; a missing audit is not a
pass. The original public `Solution.lean` with SHA256 `d52f013f...` is unchanged.
The completed r6 candidate (`5227a25e…`, 1,993,837 bytes) compiled successfully
in the local diagnostic: proof-process time 2,993.462 seconds, compiler-worker
time 2,993.015 seconds, phase time 3,023.454 seconds, and shared elapsed at the
end of compile 3,104.485 seconds. Its resource gate failed: 64 failed memory
charges, sampled process-tree peak PSS 7,997,991,936 bytes, and cgroup peak
8,589,938,688 bytes. No OOM kill, timeout or swap was observed. A successful
compiler exit does not establish resource fit.

Separately authorized fresh dependency and three-root axiom checks subsequently
passed, using the unchanged compiled artifact family and only `propext`,
`Quot.sound`, and `Classical.choice`. The observed shared clock through audit
was 3,471.979 seconds, while the supplied proof-stage sum excluding tools was
3,047.051 seconds and cold-preparation sum was 122.568 seconds. Shared elapsed
also includes wrappers and caller delays. Tools were prebuilt outside that
clock. Challenge/solution exports, Comparator/default-kernel replay, and Nanoda
were not run; the complete pipeline remains unverified.

These checks used the frozen historical current record `6735015/10000000`
at website commit `6664d243…`. The live accepted record observed during the
comparison was `66812491/99194876`, verified on 2026-10-09 at 17:13:57.608 UTC.
Our fixed score `66812491/99194740` is slightly larger, but these historical
dependency/audit checks do not validate the refreshed live contract.

The local environment used a 4 CPU/8 GiB/no-swap cgroup inside a configured
32 GiB WSL VM and compiler flags `-j4 --tstack=32768`. Cold preparation and
separately sampled caller/supervisor memory were outside the proof cgroup;
compile outside-group peak PSS was 145,674,240 bytes. Official stack/worker,
retained-string, sandbox and VM equivalence remains unestablished. The original
public d52 submission has not been replaced.

See the [completed r6 records](../verification/linux-memory-time-20261010/whole/r6-completed/README.md).

## Further finite probes

A selected two-edge pivot avoids the minimum over all nine two-edge paths for
49 representatives. The ordinary generic theorem proves the original closure
bound for every pivot; hints choose proof syntax and do not become hypotheses.
All 49 original Boolean conclusions and their fresh axiom audits passed. The
same 58 original computational definitions and three existing two-edge
definitions retained their exact bytes.

In one ordered full 49-goal pair, numeric proof time was 36.751 versus 33.881
seconds (7.81% lower), and complete component compilation was 62.098 versus
59.258 seconds (4.57% lower). No memory gain was established. Both variants
imported the same freshly checked generic environment, so this comparison does
not include the additional chosen-helper elaboration and replay cost in the
whole file. Earlier three-goal comparisons observed gains of 26.89% and 8.65%
in opposite orders, with substantial baseline variation. Those samples do not
establish a full-file speedup.

The optional selected-pivot whole source adds 4,553 bytes, leaving only
1,638 bytes of headroom. Its exact reproduction passed, but whole-file and
independent replay checks remain pending; it is not selected for adoption.
A six-field packet equality checkpoint saved only 5.86% after including its
preparation cost, with negligible PSS change, and was rejected for adoption.
See [the finite evidence and reproduction recipe](../verification/linux-memory-time-20261010/README.md).

The reproduction script generates source only. It rebuilds the numeral
dictionary from hash-pinned public inputs and writes into a fresh ignored
directory. The gzip components are review artifacts, not generator inputs;
source reproduction does not run Lean, Nano or Comparator and does not submit
anything.

## Primitive-bound shadow probe

An explicit linear-combination replacement was tested against the original
`primitiveBound_sound` proof in a post-module shadow environment. Both
successful runs passed a fresh exact-type check, a full dependency-closure
check excluding the original target, and a standard-three-axiom audit.
They reuse the exact r6 compiled dependency family; these are not fresh
whole-file or live-contract checks.

| Successful one-off runs | Original | Repaired explicit proof |
|---|---:|---:|
| Checked proof-body marker interval | 0.875 s | 0.528 s |
| Actual Lean compile + audit command sum | 29.110 s | 29.361 s |
| Complete owned-worker elapsed, including driver/bindings/cleanup | 29.763 s | 29.677 s |
| Sampled peak PSS | 7,129,774,080 B | 7,151,198,208 B |

The runs crossed a system reboot. The 0.086-second worker difference is
not a pure Lean speedup; the actual Lean command sum increased by 0.251
seconds and no memory saving was observed. The sub-second body difference
does not identify the bottleneck of the 2993-second whole compile. The
initial explicit version failed a source type mismatch, printed `sorryAx`
during failed elaboration and produced no `.olean` or fresh audit; its
timing is excluded from successful comparisons. All three records are
[preserved](../verification/linux-memory-time-20261010/primitive-bound-shadow/README.md).
The replacement is not adopted.

## Review and next step

The exact rational result and numeric inputs remain fixed. The earlier complete
Data and Point comparisons passed ordinary Lean proofs, fresh axiom audits and
serial independent replay. Two-edge routing reduced Data replay by 13.3%;
reflection reduced Point replay by 19.2%. Their percentages cannot be added or
applied to a whole pipeline. Direct reflexivity and the current Array sparse
accumulator did not reduce cost.

The eight AM aliases found by the earlier [bounded probe](../verification/am-helper-alias-bounded-probe.json)
are now included in the complete Linux AM variants. Both full AM compiles and
fresh 20-root audits passed, using only permitted axioms. A single same-Linux
pair observed an 18.9% AM wall-time reduction from bounded asynchronous
elaboration; the small PSS difference does not establish a significant memory
gain. The selected-pivot finite component also passed all 49 original goals
and fresh audits, but its whole-file helper cost and independent replay remain
unresolved. The bounded AM source without that extension remains the default.

The global-synchronous candidate has now passed complete local Lean compilation
and fresh standard-axiom checks. Its configured memory gate failed, and no
export, serial independent replay or Comparator/default-kernel result was
obtained. Before adoption it needs lower resource costs and fresh checks
against the updated server contract. Independent cold phases in a 32 GiB WSL
VM cannot establish official 8 GiB sandbox compliance.

Further changes should follow the complete run's measured failure point or
dominant kernel cost. The original checked submission remains published until
a replacement passes its own complete checks. Mathematical research remains
paused, and no website acceptance is asserted.

## Published candidate

The verified public Solution.lean is still the original 1,996,187-byte file,
SHA256 d52f013f7edcc8536a28ef3908e64a967e5b9184d6546952cb5a541dc6d65e8a.
Its ordinary kernel and independent checks passed. Its resource compliance
remains unconfirmed. A replacement needs fresh full compilation, transitive
axiom checks, independent replay and the exact website contract comparison.
No optimization sample authorizes a website acceptance claim.

## Accepted public proof comparison

The [master-of-puppets proof](https://github.com/josusanmartin/riemann/blob/d95a6d7d11d7836306ec7ec1eb5be3478663718e/submissions/master-of-puppets/proof/Solution.lean)
uses reward 805124/100000000, versus our fixed 805260/100000000. Its pressure
and HW floor match ours, giving denominators 99194876 and 99194740 respectively.
Our nine-point, 1224-representative certificate is used to prove the extra
136/100000000 reward; its absence from that proof does not make it removable
here. No safe 135 KB deletion was established. The static review found only
24 conservative unused-name candidates, at most 7650 raw bytes, which still
require semantic dependency checks. See the [source comparison](../verification/linux-memory-time-20261010/review/accepted-source-comparison.md).
