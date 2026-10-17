# Research direction and review cadence

The human has requested a macro review every 4–8 main research rounds to
prevent local optimization and context compaction from losing the objective.
Use six main rounds by default, and never exceed eight without a review.

- At the start of a new main-agent research round, read
  `research-goal-20261016/DIRECTION.zh.md` and `direction-state.json`, then
  increment `main_rounds_since_review`. A compaction, tool call, subagent
  message or within-round user steering does not create another round.
- Review at round six. Review earlier, from round four, when evidence changes
  the route or progress is mainly bookkeeping. A major counterexample or
  promising certificate can also trigger an immediate review.
- Write the review with current file/receipt/commit evidence. Recheck the
  original unconditional proportion, complete formal proof, independent
  kernels, source-size contract, GitHub synchronization and submission
  materials. Numerical results and module counts do not satisfy these gates.
- Select a main route, its next proof-producing gate, explicit stop/redirect
  conditions, and the status of alternatives. Stop redundant trial families.
  Reset the counter only after the written review is complete; retain the
  review number and links in `direction-state.json` and the continuation file.
- Subagents must report evidence and its exact scope. They must not reset the
  main-round counter, start another optimization family or a compiler batch
  merely because their previous task ended.
- Keep the full human objective intact. A local exclusion, conditional bound,
  exact outer-model witness, static model, successful build or synchronized
  checkpoint is not completion of an unconditional zero-proportion record.

The current direction and latest written review are authoritative over old
continuation notes describing superseded next actions. Preserve frozen proof
sources, numerical packets, receipts and their hashes.
