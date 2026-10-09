# FKRG v1.1 — Codex review remediation and non-duplication contract

## Provenance and governance

- Original merged PRs: #305 (UMC proofs and audit tooling), #306 (FKRG v1), #307 (FKRG CI).
- Actual Codex review threads: #305 [4230103915](https://github.com/MurphyHoops/UEOT/pull/305#discussion_r4230103915), [4230103923](https://github.com/MurphyHoops/UEOT/pull/305#discussion_r4230103923); #306 [4230254261](https://github.com/MurphyHoops/UEOT/pull/306#discussion_r4230254261), [4230254265](https://github.com/MurphyHoops/UEOT/pull/306#discussion_r4230254265).
- #307 Codex review completed without inline findings.
- Explicit immutable-base Track TC L2 authorization: governance PR #308, scoped to precisely four existing scripts; no frozen Core source, counted theorem ledger, or past audit receipt changed.

## Four regression-backed repairs

1. **Receipt integrity, #305 / 4230103915:** non-`--full` checks return transient `NOT_RUN` statuses but no longer overwrite the previously committed full `UMC_LOCAL_EXACT_HEAD_AUDIT_V4.json`. `--full` remains the only full-evidence writer. Regression writes an immutable simulated full receipt, executes a real lightweight audit, and asserts byte identity.
2. **Branch portability, #305 / 4230103923:** `audit_local_branch_inventory.py` derives checkout branch and commit from real Git; detached HEAD and absence of the historical author-only ref are supported. Missing `origin/main` is allowed via fallback HEAD. Historical date-stamped `UMC_LOCAL_BRANCH_INVENTORY_2026-10-09.json` and Markdown receipt are no longer silently overwritten; new reports require explicit output path.
3. **Lean extraction correctness, #306 / 4230254261:** lexical source extraction now indexes inline attributed declarations and qualified identifiers; verified against actual `@[simp]` `Model.coe_discountNN` and `Interface.comp`. Both example symbols are also confirmed against Lean itself, not solely regex matches.
4. **Offline recovery, #306 / 4230254265:** FKRG offline `status` returns `cached_origin_main: null` if the local tracking ref is unavailable, preserving local HEAD/index/task information. It still explicitly marks live remote CI as unchecked.

## Additional cross-file repair

The UMC local diff allowlist now includes the already governed Track TC FKRG `knowledge/` namespace, not any other Track, so a real uncounted FKRG code fix does not make the local scientific audit misclassify a valid TC-only edit.

## Validation and scientific limits

Run after exact code checkout:

```bash
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/test_fkrg.py
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py build
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/fkrg.py status
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/audit_local_branch_inventory.py --output /tmp/umc-current-branch-inventory.json
```

Fifteen positive/negative tests include the four initial Codex failures, stale index, unknown symbol, and existing proof reuse. The 5,553 current records are **lexical candidates**, not 5,553 fully elaborated proofs. The existing Core 106/106 frozen count, Compression four counted generators, and P12 PARTIAL claim remain unchanged.

A new GitHub PR must be reviewed at its exact head, have **all review comments addressed and threads resolved**, and only be merged after required checks. Do not equate review submission with approval or unconditionally trust the bot summary; a completed code review with suggestions is a review with open work.

Open FKRG upgrades beyond v1.1: a machine-built declaration-level dependency DAG for all 5,553 candidates; mathematically typed hypothesis matching; mandatory *per-new-proof* reuse contract; independently grounded scientific source semantics. Do not claim those future tasks are completed.

## Exact-head PR #309 follow-up

- The first PR #309 CI exposed a genuine GitHub detached checkout without a local \`main\`: UMC fast audit now uses \`refs/heads/main\` or \`refs/remotes/origin/main\`, and fails closed if neither exists.
- The subsequent #309 Codex review [4230694470](https://github.com/MurphyHoops/UEOT/pull/309#discussion_r4230694470) caught the remaining ambiguity: when no main ref exists, **the branch inventory now reports UNKNOWN ancestry** and never claims a branch is already merged into main; even Markdown reports mark main as UNAVAILABLE.
- CI/no-main and historical-evidence immutability tests included in 15/15 FKRG regression suite.

- Second exact-head Codex review of #309 [4230799348](https://github.com/MurphyHoops/UEOT/pull/309#discussion_r4230799348) identified a leftover static Markdown paragraph that still asserted older branches were merged even when no main ref was available. The generated report now conditionally omits all such assertions in no-main mode and states explicit uncertainty; a regression asserts absent stale \`formal/p*\` / \`主线主动收窄\` claims.

- Third exact-head Codex review of #309 [4230869532](https://github.com/MurphyHoops/UEOT/pull/309#discussion_r4230869532) found that source-fingerprint-only caching fails to invalidate a database built by an older extractor. FKRG V2 now pins **both** Lean-source fingerprint and extractor-code SHA-256 (plus schema) and refuses old cache versions as stale.
- Independent source analysis found two private helpers called \`survivalProb_zero_eq_one_of_not_mem\` in distinct modules: these are **private** Lean declarations, not a single publicly reusable constant. The index now gives private candidates source-scoped synthetic identities and refuses a public \`lean-check\` for them. Negative regression tests cover both defects.
