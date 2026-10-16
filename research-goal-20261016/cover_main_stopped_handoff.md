# Stopped main and safe handoff boundary

Session1700 now returns `Unknown process id`. This is not an exit-code
report. The parent independently observed no PID46548 and no python.exe
in two elevated host-CIM queries at21:31UTC on2026-10-16. The search must
no longer be described as live. No exit code, final stderr or OOM evidence
was recovered; the cause is unknown.

The last available stdout in this agent is the130600-node progress line.
The complete atomic file later persisted132000 nodes at
21:21:54.146880UTC. Its912240992 bytes hash to
`2e50e2303ca3705ae9ba91e741764e84550c382049b88ae5cbd064247bba671d`.
The attached read-only audit checks the full byte hash, header/final JSON
tail, all25 frontier DBM closures and all frozen source hashes. It does not
parse the middle collections or replay their mathematical certificates.
There are65988 leaves,125968 Newton steps,996433 OBBT bounds and2540 support
records. Frontier size is not a domain-volume or remaining-work estimate.

The existing file was not renamed, copied, made OS-readonly or rewritten.
Its digest binds the observed snapshot bytes. Before any future producer
can overwrite the old filename, preserve those bytes or complete and
independently verify a lossless baseline-store migration. The original
checked-node endpoint is2022500, so1890500 nodes remain in the original
budget at this snapshot. No search is launched by this document.

The proposed SQLite prototype is a separate new storage implementation.
Its importer must open one stable snapshot handle and stream every old
collection entry into a transaction, retain all small metadata and the
exact ordered frontier, and publish only after the entire baseline is
durable. An independent second pass must compare entry order, canonical
JSON values/hashes and the total original byte digest. This would establish
storage fidelity, not semantic proof replay or compatibility of an actual
new search producer. Further adoption remains a separately reviewed step.
