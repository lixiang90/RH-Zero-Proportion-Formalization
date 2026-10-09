File-only publication review, 2026-10-10. No public files, Lean processes,
runtime caches or website state were changed by this review.

The finite packet's 130 inventory entries, 25 public-source pins, recipe
`e31ba797...` and wrapper `5b4ccbc4...` match. All 88 unique gzip archives have
matching compressed hashes. Decompressed hashes were additionally checked for
70 files at most 15 MB each; 18 large cold-residency records were left compressed
under the review bound. This limitation is explicit in `manifest-review.json`.
The 1,996,187-byte public Solution retains SHA256 `d52f013f...`. The user log has
19,250 bytes and SHA256 `79255b17...`; email, GitHub-token, bearer-header,
private-key and URL pattern counts are all zero.

The r2 source-only wrapper statically pins dynamically loaded generators,
refuses `-O`, verifies frozen tracked inputs, and writes only into a fresh
ignored tree. The old-Git ownership repair uses a temporary subprocess-local
Git configuration for read-only queries and leaves persistent configuration
unchanged. The wrapper's matching-source generation records prove reproducible
bytes, not Lean or independent-kernel validity. No rerun was needed for this
review.

Actionable publication corrections:

1. The finite proposal README AM row/footer and `proposal-status.json` still
   list same-OS AM comparison as pending. Replace these with the completed
   448.761/553.329-second comparison and its qualified scope.
2. The three-goal README row still says there is no complete 49-goal result.
   Replace that clause with a pointer to the separately checked 49-goal pair;
   retain the warning that helper cost and independent replay are unresolved.
3. AM logs are now available in the separate AM packet. Refresh prospective
   packet pending labels and inventory only after deciding their public paths.
4. The current resource doc's AM paragraph says the aliases are not included
   in either generated candidate. That is true only of its earlier candidates;
   mark those as historical and use the replacement review section.
5. Current overview links may use site commit `6664d243...`; existing archived
   measurements keep their original pinned site versions. Do not rewrite
   historical records to imply that their checks used the new best score.
6. The AM manifest deduplicates five references into the finite packet. Publish
   both packets and add a relocation map or explicit relative links. Preserve
   the original manifest and hashes when adding this mapping.
7. Final publication must reconcile the running f40 whole result with draft
   pending text. Do not upgrade compile failure, an interrupted run or a
   component pass to complete comparison or official acceptance.

The proposed doc fragments assume public targets
`verification/linux-memory-time-20261010/am/` and
`verification/linux-memory-time-20261010/` for the finite packet; full-file
evidence belongs under `whole/`. Whole-file status is intentionally
pending in the drafts. Earlier checked records remain intact.
