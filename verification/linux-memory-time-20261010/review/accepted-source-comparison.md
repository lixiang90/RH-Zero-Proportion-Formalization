# Accepted public proof: static resource comparison

This review downloaded the exact public files at commit
`d95a6d7d11d7836306ec7ec1eb5be3478663718e`. It read only Windows source/text
files and public network responses. No Lean, WSL, runtime cache, active r6 log,
candidate edit, new mathematical argument or message to another author was used.

The [live submission](https://www.riemannzeta.fun/submissions/master-of-puppets)
reports `66812491/99194876`, author `arun-chandru`, verified at
`2026-10-09T17:13:57.608Z`. Its [fixed proof source](https://github.com/josusanmartin/riemann/blob/d95a6d7d11d7836306ec7ec1eb5be3478663718e/submissions/master-of-puppets/proof/Solution.lean)
is preserved exactly as `public/Solution.lean`: 1,858,713 bytes, SHA256
`f7ef331e72e8c34804e196a4cc0c6fdd69bb1c6947a51dfbf60b88a6343aad9d`.
The pinned submission JSON declares Apache-2.0; the proof header also declares
Apache-2.0 and retains upstream notices and license text. The repository root
LICENSE is MIT. These distinct source-level notices have been retained verbatim
in the downloads. No authorship conclusion is drawn from shared material.

## The numerical difference is a required certificate improvement

| Closed constant | Accepted public proof | Our frozen r6 source |
|---|---:|---:|
| Local reward/floor | 805124/100000000 | 805260/100000000 |
| Pressure sum | 404350/100000000 | 404350/100000000 |
| Energy/window floor | 67216841/100000000 | 67216841/100000000 |
| Result | 66812491/99194876 | 66812491/99194740 |

The numerator is the common difference `67216841 - 404350`. The denominator
is `100000000 - localRewardNumerator`. Thus the 136 denominator improvement
comes from our additional reward, not a decimal or rounding convention.
The exact positive gap is `1135812347/1229951241769030`, about
`9.234612791368617e-7` in proportion, or `0.00009234612791368618` percentage
points. These are exact rational calculations on the two published constants.

The public proof closes its actual-defect estimate with `RiemannFail.W8`, its
admissibility, pressure identity and `RiemannFail.cert_AM`, then passes through
`Opeth.AMCounting` to the three official declaration names. Its final theorem
types contain no remaining finite-certificate or defect hypothesis. The
downloaded public attestation says kernel-verified, and its completed public
verifier log reports all three final roots using only `propext`, `Quot.sound`
and `Classical.choice`, then successful nanoda and Lean kernel checks. This
review preserves that evidence; it does not independently replay or authenticate
the verification service's internal run.

Our stronger reward is supplied by `W9_local_certificate`, which uses our
1224 integer representative conclusions and their shape/orbit/dual/row/box
transport. The public file has no exact `1224` token, `pairPacks`,
`integerCertificateCheck`, `all_integer_representatives`, `extraSpanChecks` or
`W9_local_certificate`. Our module 11 occupies 85,009 source bytes. Its final
certificate is on the explicit source path to `RHWeilSubmission.local_certificate`
and the dyadic/cumulative roots. Deleting that module or replacing its floor by
the accepted eight-point floor would lose our fixed result.

Shared AM/PC8 material is substantial, but the full finite data is not identical.
The accepted namespace `PC8C5BF` and ours `PC8CL` have different tree/leaf
organization and packed-literal representations. For example the same basename
`PTL_154` has four public table pairs but two in ours, and the downstream
`PTs52_54` selects different leaf indices. A name missing from one file is not an
unused declaration: our `PTL_153` and its proof are explicitly consumed by our
tree. Namespace renaming, numeric-token agreement or masked-string matching
must not be used to assert equality of these certificates. The strict inventory
preserves string literal contents for declaration hashes; full kernel/semantic
equivalence remains outside this static review.

## Resource ideas that transfer, and their limits

The accepted source has 135,124 fewer bytes than our r6, but this is not a
measured pruning benefit for our stronger certificate. It also contains a
different final assembly and lacks the new nine-point data and transport.
Its header describes pruning old linear/tau/square-root/edge-window consumers
after exported final-root dependency audits. After normalizing the PC8 namespace
label only, our retained common AM/bridge layer differs mostly by representation
helpers; the remaining small analytic additions are explicitly consumed, including
`wfunAM_le_one` in our nine-point tail. There is no justified 135KB deletion
recipe from this comparison.

The useful transferable procedure is to prune only after checking the completed
final-root export/dependency closure. `static-unused-proof-candidates.json` lists
24 conservative single-name-occurrence proof declarations, at most 7,650 raw
block bytes. Examples include generic count-transport wrappers and duplicate
integer/scaled-certificate soundness wrappers. This is a proposal, not proof
that they are unused: implicit tactic searches, attributes and generated
references still need review. The minimal future recipe would remove only
confirmed unreachable theorem/lemma declarations, leaving every numeric
definition/table, all 1224 integer conclusions, the W9 assembly, root types,
hypotheses and attribution notices unchanged. No Lean candidate was generated.
It requires fresh complete verification and resource measurement before adoption.

The accepted source sets global `Elab.async false` and contains no asynchronous
true region. Our r6 has global false but retains the bounded-eight asynchronous
AM region and its 162 waits. Full synchronous scheduling is a possible separate
resource experiment; its effectiveness is not established by acceptance of a
different source. Our recorded AM comparison already found the synchronous
component slower, so this does not justify switching the current source.

Public intermediate axiom-print pruning offers no new saving: ours already has
zero such source commands, versus the public file's three final prints. No
`axiom`, `sorry`, `admit`, `native_decide` or `unsafe` syntax was found outside
comments/strings in the public file; that is a lexical observation, not a
transitive axiom audit. Public source compression uses long hex literal data;
ours uses base92 literal/dictionary macros and has already compressed some
Boolean proof syntax. The public gzip size is 489,654 bytes versus r6's 792,568,
but gzip reduces transport/storage only and does not establish fewer Lean
declarations, smaller live environments or compliance with the raw 2MB source
limit. No decoded-natural equality or useful syntax transplant is claimed here.

## Exact resource scripts and current repository head

Both scripts are from the same pinned d95 commit:

| File | Bytes | SHA256 | Limit |
|---|---:|---|---|
| `public/run-comparator-e2b.sh` | 2818 | `86308ed0ed625524e8ed26f08dd8087d3046f5729da0d7e4d1cd5199a41dbde0` | Inner Comparator 3200s; TERM, kill-after 15s |
| `public/run-verification-job.sh` | 2084 | `4a072eebbbb1bf0e230f38755ea2f11b38a5e650e0986179dac17c973dd47aaa` | Outer verifier job 3240s; TERM, kill-after 15s |

The scripts alone do not set CPU/memory. The same-commit
`public/e2b-build-template.ts`, lines 14–15, supplies `cpuCount: 4` and
`memoryMB: 8192`. Its SHA256 is
`439eeec3a8cb58f98083d635c8d62c6e79cc14b6c820c898183c9c0c3913cb0e`.
The template and verifier also preserve network/Landlock isolation and a clean
execution environment. This records configured template resources; it does not
substitute the local cgroup experiment for an official sandbox run.

The read-only GitHub `commits/main` response reported head
`78e95fb0f5fb987156c61d634c104f8bc752ece3`, committer date
`2026-10-09T17:56:43Z`. The exact API response is preserved, not a moving HEAD
assumption. The existing frozen local contract is not changed by this review.
Any future current-record comparison must distinguish the historical frozen
`6735015/10000000` contract from the live accepted `66812491/99194876` record.

`download-manifest.json` and `download-manifest-extra.json` bind all raw response
bytes. `static-comparison-strict.json`, strict declaration inventories and the
static pruning proposal bind the analysis to frozen source hashes. Earlier
masked inventories remain as preliminary records and must not be treated as
encoded-data equality evidence.
