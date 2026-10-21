# Minimal consumer changes after canonical authorization

**Suggestion only. Production was not modified.** At preparation, root reported PR #355 still open and its merge attempt rejected. The actual canonical authorization must be obtained before editing/registering the governed consumers. The native tool preparation is independent of that policy gate.

## 1. Registry additions

After both real native executions and finalization, register the eighth overlay, fixed verifier and native evidence using their actual hashes in `fkrg_reuse.py`. Keep all seven previous overlay bytes/hashes and all frozen CSV, source-census and type-group files unchanged. `FreeInformationValue.lean` requires no edit or source-hash override.

The current `FKRG_REUSE_OVERLAY_V1` already permits `public_theorems` to name an existing module: `_parse_data` appends graph nodes independently from `added_modules`, and `verify_sources` verifies the module list separately. Therefore the historical helper can be the 53rd overlay registration while `added_modules` remains seven. Explicit `registration_kind` distinguishes `new_source_public` from `historical_public_repair`.

## 2. Validate the historical repair fields

Extend `load_overlays` with checks that apply only when repair fields are present. Old overlays lacking these fields retain their existing behavior.

- Require `historical_public_repair_certification.status == PASS` and `existing_proof_dependency_repair_certification.status == PASS`.
- Require the historical repair names to be a unique subset of `public_theorems`, with matching paths and `registration_kind`. Require the expected source hash to match the already registered module's pinned hash, accounting only for authorized existing overrides.
- Require the repair certificate's prior registered scope to equal the actual number of graph nodes before this overlay, currently 4,094; require its scan count to match that number. The prior node count can be accumulated from the immutable 3,793-node base and each previous overlay's registrations.
- Keep public-node edge certification unchanged: its edge count remains the sum of `source_theorem_deps` for the 53 public registrations. Validate existing-node repair edge counts separately from that sum.
- Bind the native artifact to the same exact names, source owners, public partitions, eight physical audit modules, actual comparison counters and narrow-scan caller set. The new exporter/fixed verifier already provide these fields; the pinned native artifact and verifier must be the actual finalized ones.

## 3. Apply existing-node edges additively in memory

Within `_parse_data`, maintain a name-to-row map while appending each overlay. Save `prior_names` before adding that overlay's public registrations. Once its registrations exist, apply its `existing_proof_dependency_repairs` to the corresponding **existing** rows, then build `graph` and `incoming` normally.

For each repair, fail closed unless all of the following hold:

1. `name` is unique among this overlay's repairs and belongs to `prior_names`; the source path, owner and line agree with that existing row.
2. `prior_source_theorem_deps` is a unique list of already registered names and equals the existing row's parsed dependency list exactly as a set. Do not silently replace the old list.
3. `added_source_theorem_deps` is nonempty, unique, disjoint from the prior set, and consists solely of this overlay's exact historical repair targets.
4. `actual_source_theorem_deps` equals the disjoint union of those lists and agrees with the pinned native narrow-scan row's filtered actual direct constants.
5. The existing caller's current source hash equals the pinned repair source hash. Its actual compiled owner and direct proof were checked by the fixed certificate; no lexical occurrence is promoted into a proof edge.

Update only the in-memory row's `source_theorem_deps_json` and `direct_existing_source_theorem_deps`. Retain the original list and overlay ID as repair provenance if exposed by the navigator. Do not rewrite any CSV. Do not overwrite `all_direct_project_scoped_constants`; that historical field is a separate census quantity. Rebuilding `incoming` from the final in-memory rows then exposes the real `p_ref_03 → integrable_finset_sup'` use and any other actual caller found.

The native result determines the number of repairs. Do not hardcode one merely because source inspection found one explicit use. The real narrow scan and fixed replay cover all 4,094 old registered proofs.

## 4. Keep reporting precise

- Expected live source modules after registration: 666; expected live registered graph nodes: `4094 + 52 + 1 = 4147` if all native gates pass.
- Preserve historical counts 3,793/4,094 and their evidence identities. Do not relabel the old graph 4,095.
- Report 52 new source theorems and one historical registration repair. `type_distinctness.new_theorems = 53` is retained for schema compatibility but explicitly means newly registered nodes; the new partition fields remove ambiguity.
- Report `overlay_registered_direct_edges` as before for outgoing edges of overlay registrations. Add a separate total for `existing_proof_dependency_repairs` instead of folding it silently into old evidence counts.
- A historical-repair node should display `HISTORICAL_PUBLIC_DECLARATION_REPAIR_UNCOUNTED` as its role rather than inheriting the new mathematical bridge family's label. Its source remains the unchanged existing module.
- Keep the frozen 106 P-ID categories, source mathematics and ledger counting unchanged. A restored graph node/edge is not a newly proved P-ID.

## 5. Focused consumer tests to add

Once registration is authorized and the actual artifact exists, extend `test_fkrg_reuse.py` with the following material cases. They complement, and do not replace, the full `knowledge/test_fkrg.py` and canonical preflight.

| Check | Required result |
|---|---|
| Historical source and CSV digests | All exact old hashes preserved |
| Node counts | 52 new declarations, 1 repair, 53 registrations, 4,147 live graph nodes |
| Module scopes | 7 added, 8 native audited, 666 full source modules; no duplicate existing module |
| Helper lookup and role | Exact trailing-apostrophe name is searchable and marked historical repair |
| Existing caller repair | Every actual narrow-scan caller's prior list plus exact delta appears in the live graph and reverse index |
| Native evidence | Actual 216,982 cross and 1,378 internal comparisons, including 52 mixed comparisons; no unreported collision |
| Axiom/owner scope | Both historical public theorems and all owned private/generated constants in eight modules are represented, under the unchanged whitelist |
| Invalid additive repair | Reject an unknown/new caller, a changed prior list, deletion, duplicate caller/edge, wrong owner/hash or an added edge outside the historical target set |
| Missing/unbound evidence | Reject pending repair status, count mismatch, missing native caller or changed pinned artifact |

Do not update `fkrg.py`, historical CSV files or `FreeInformationValue.lean` in this change. The exact name has been restored through a native-confirmed additive registration. A future parser repair would require its own real scope and governance review; it is not claimed here.
