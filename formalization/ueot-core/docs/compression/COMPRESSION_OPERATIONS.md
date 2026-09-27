# UEOT Core Compression Formalization — Operations Manual

## 0. Identity

- Repository: `MurphyHoops/UEOT`
- Integration branch: `main`
- Frozen Core v3 source theorem baseline: **106/106 FULL-GREEN**
- Compression LIVE STATE: GitHub Issue **#146**
- Machine ledger:
  `formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml`
- Human coverage view:
  `formalization/ueot-core/docs/compression/COMPRESSION_COVERAGE.md`
- Source theorem seed index:
  `formalization/ueot-core/docs/CORE_COMPRESSION_THEOREM_INDEX.csv`
- Official regression target: `lake build UEOT`

Compression is a post-106 meta-formalization mission. It must never alter the
meaning or counted status of the frozen 106 source P-IDs.

## 1. Authority hierarchy

When records disagree:

1. frozen Core v3 source controls original P-ID semantics;
2. `V3_COVERAGE_STATUS.md` on `main` controls the completed 106/106 proof
   baseline;
3. `COMPRESSION_LEDGER.yaml` on `main` controls counted compression claims;
4. live branches/PRs/Actions control code and CI facts;
5. Issue #146 body controls current active compression intent/blocker/next step;
6. active compression branch controls unfinished code;
7. prior chats/comments are supplemental history only.

## 2. IDs and state machines

Meta-generators use permanent IDs such as:

- `M-QD-01` — Quotient Descent;
- `M-TC-01` — Transport Certificate Calculus.

Generator states:

`candidate -> schema_locked -> lean_wip -> lean_green ->
cross_family_green -> integration_green -> main_green -> ledger_green ->
counted_generator`.

Mapping states:

`conjectured -> source_aligned -> statement_matched ->
lean_rederived_partial | lean_rederived -> assumption_audited -> main_green ->
counted`.

`rejected` is a valid terminal research result for a compression hypothesis.

## 3. Evidence discipline

A compression claim is not established merely because two theorems look
similar. A counted mapping requires:

1. frozen source statement identified;
2. generic M-ID theorem Lean-green;
3. explicit specialization/wrapper theorem;
4. assumption relation recorded;
5. conclusion relation recorded;
6. full source-facing conclusion recovered for `lean_rederived`;
7. feature exact-head CI green;
8. clean integration/PR/resulting-main CI green;
9. separate ledger promotion green.

`partial` may never be counted as a full P-ID rederivation.

## 4. Branch governance

Repository-wide governance in `docs/REPOSITORY_BRANCH_GOVERNANCE.md` remains
binding.

Compression branch classes:

- bootstrap/governance: `ops/core-compression-v0` (temporary);
- generator feature: `compression/<m-id-lower>-<topic>`;
- clean integration: `compression/<m-id-lower>-main-integration`;
- ledger promotion: `compression/ledger-<checkpoint>`;
- emergency quarantine only: `hold/compression-<topic>`.

Default: one active mutating branch per M-ID. Do not create `v2`, `fresh`,
`final`, or scratch branch families.

## 5. Branch creation preflight

Before any new compression branch:

1. fetch/prune remote state;
2. read this manual from `main`;
3. read `COMPRESSION_LEDGER.yaml` and `COMPRESSION_COVERAGE.md`;
4. read Issue #146 body;
5. list remote branches and open PRs;
6. verify the M-ID is not already active/integrated;
7. reuse the existing branch whenever one already represents the work;
8. verify repository branch count remains <= 8 target / <= 12 hard cap.

## 6. CI gates

Every compression feature head must pass:

1. Compression ledger/matrix validator;
2. protected baseline audit;
3. proof-escape scan in `UEOT/V3/Compression`;
4. `lake build UEOT.V3.Compression`;
5. compression theorem axiom print;
6. full `lake build UEOT`.

The general `UEOT Core Lean` workflow also runs on `compression/**` and the
bootstrap branch.

## 7. Promotion lifecycle

`CANDIDATE/SCHEMA -> FEATURE -> FEATURE CI -> SOURCE/ASSUMPTION RE-AUDIT ->
CLEAN INTEGRATION FROM LATEST MAIN -> INTEGRATION CI -> PR EXACT-HEAD CI ->
MERGE MAIN -> RESULTING-MAIN CI -> LEDGER-ONLY BRANCH/PR -> LEDGER MAIN CI ->
COUNTED`.

Feature green alone never changes counted compression coverage.

## 8. Issue #146 LIVE STATE

The Issue body, not comment tail, is the high-frequency recovery record.

Required fields:

- current Core baseline/main;
- compression counted metrics;
- active M-ID/lane;
- active branch/head;
- open PR;
- latest relevant CI;
- current scientific hypothesis;
- blocker/root cause;
- exact next action;
- do-not-repeat guards.

Comments are reserved for durable milestones/rejections/audits, not CI polling.

## 9. Cross-chat recovery

New chats execute `COMPRESSION_BOOTSTRAP.md`. Never open a replacement branch
merely because the chat or AI platform changed.

At handoff:

1. commit/push meaningful WIP on the same active branch;
2. update Issue #146 body;
3. persist architecture decisions not already in code/docs;
4. do not modify counted ledger files unless a real lifecycle transition
   occurred;
5. continue useful work if the current chat still has room.

## 10. Parallel conversations

Parallelism is allowed only for genuinely separate M-IDs or read-only audits.
Two chats must not mutate the same M-ID branch/file concurrently.

Recommended maximum:

- active mutating compression lanes: 2;
- open repository PRs: 2 total under repository governance;
- read-only theorem/source audits: may run without branches.

## 11. v4 gate

Do not write a compressed Core v4 merely from conceptual elegance. A v4
reorganization is justified only after the meta-layer has substantial
machine-backed source coverage, explicit residual adapters, and ablation
evidence.
