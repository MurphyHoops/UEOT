# Unapplied additive historical repair consumer candidate

**This is a repository-external candidate, not an applied change or a canonical gate receipt.** It contains only the proposed `fkrg_reuse.py` and `test_fkrg_reuse.py` changes. Root owns final review/application after the actual policy authorization. No new overlay, verifier or native artifact hash is filled in. The old seven-overlay registry and frozen counters in the existing integration tests remain unchanged until actual registration evidence exists.

## Behavior

`apply_existing_proof_dependency_repairs` validates a new overlay's exact historical repair targets, native artifact binding and complete narrow-scan caller set. It checks the previous graph membership, previous effective source hashes, old dependency lists, actual native direct constants and exact additive delta. It rejects removal of an old edge, an invented or unrelated edge, a new/unknown caller, an unregistered target, source drift, uncertified proof/axiom/type status, an unmatched caller or changed native bytes.

Validation finishes before an existing row is mutated. The function changes only the in-memory graph row and appends provenance for its old list and additive delta. CSV files are never rewritten. The normal graph/reverse-index construction then observes the repaired edges. Existing all-direct-project-constant census fields retain their historical values.

`_parse_data` takes the prior name set and effective per-module source hashes before appending each overlay. It calls the repair validator after the new historical target has been registered. Overlays without repair fields retain their prior behavior. Repair source hashes are enforced even if a caller opts out of the generic full source-tree verification; an additive repair is not accepted against changed old proof inputs.

Historical helper nodes get the role `HISTORICAL_PUBLIC_DECLARATION_REPAIR_UNCOUNTED`. `overlay_registered_direct_edges` retains its old definition: outgoing edges from overlay public nodes. New status fields report historical repaired nodes and existing-node edge additions separately.

## Actual local checks

The candidate passed Python AST validation and 14 targeted regressions in `AdditiveHistoricalRepairTests`, with zero failures and zero errors. The harness copied the exact proposed consumer bytes into a temporary directory with the normal repository-relative layout, then ran only the new class extracted unchanged from the proposed test AST. Synthetic input files were temporary and were cleaned up. They are not native evidence.

The actual log and structured receipt are `targeted-attempt-1.log` and `targeted-attempt-1.json`. They explicitly record that production was unchanged, the patch was not applied, no Lean/native command ran, the full FKRG tests did not run, and no canonical gate was satisfied. Previous integration tests were not run or falsely relabeled as passing.

## Parent integration steps

1. Verify `BASE_FILES.json` against the actual consumer files; review `consumer-repair.patch`.
2. Obtain the required actual canonical authorization. This directory does not authorize a governed edit.
3. After real native/fixed execution and finalization, register the eighth overlay/verifier/native artifact with their actual hashes, including the observed repair list. Do not hardcode that list to one caller.
4. Apply the reviewed helper/test patch. Update existing integration-test totals only from the actual finalized artifact and live registered graph, keeping 52 new declarations and the historical repair separate.
5. Run the required actual-base parser/preflight and full FKRG gates. These fourteen local synthetic regressions are not substitutes.

The patch intentionally does not touch `fkrg.py`, `FreeInformationValue.lean`, historical CSVs, source-census snapshots, canonical ledgers or any physics files. It does not change the trailing-apostrophe parser and does not claim that bug has been repaired.
