# UEOT Core 3 Lean Formalization — Cross-Chat Operations Manual

> Purpose: make UEOT Core 3 Lean formalization resumable across arbitrarily many ChatGPT conversations while keeping theorem semantics, coverage accounting, branches, CI and handoff state auditable. No chat and no temporary branch may become a single point of failure.

## 0. Project identity

- Repository: `MurphyHoops/UEOT`
- Formal integration branch: `main`
- Frozen source specification: `UEOT_Core_Mathematics_v3.0_Complete.md`
- Frozen source P-IDs: `106`
- Lean: `4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Official final target: `lake build UEOT`
- Counted coverage truth: `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`
- Single high-frequency live state: **GitHub Issue #56 body**
- Historical live-state comments: audit/milestone history only

`main` is the only integration branch. Never use `master` as a UEOT Core 3 integration target.

---

# 1. Ultimate completion criterion

The project is complete only when all 106 frozen source-level P-IDs are machine verified and counted:

`106/106`.

Proof lifecycle:

`SOURCE AUDIT -> PROOF CONTRACT -> EXISTING-CODE AUDIT -> LEAN DEVELOPMENT -> FEATURE GREEN -> SOURCE RE-AUDIT -> PROHIBITED-PROOF AUDIT -> CLEAN INTEGRATION -> INTEGRATION GREEN -> MAIN -> POST-MAIN GREEN -> LEDGER UPDATE -> LEDGER PR GREEN -> LEDGER MAIN GREEN -> COUNTED PROVED`.

Therefore:

- helper theorem green != source theorem proved;
- WIP checkpoint != feature green;
- feature green != counted coverage;
- PR open != proved;
- proof-main green != counted coverage;
- a theorem with stronger assumptions or weaker conclusion than the frozen source does not close the P-ID.

---

# 2. Authority hierarchy and persistence architecture

When sources disagree, use this order:

1. frozen source specification -> theorem semantics;
2. `V3_COVERAGE_STATUS.md` on `main` -> counted P-ID set;
3. live `main`, branches, PRs and Actions -> actual code/CI state;
4. **Issue #56 body** -> current construction intent, blocker and exact next action;
5. `PID_STATUS.yaml` / `FORMALIZATION_STATE.md` -> lower-frequency lifecycle metadata;
6. `HANDOFF_LATEST.md` -> fallback archival snapshot;
7. Issue #56 comments / prior chats -> historical reasoning only.

A stale comment or handoff document must never override current `main`, current coverage ledger, or the Issue #56 body.

The durable layers are:

- **Frozen source** — semantic authority.
- **`main`** — integrated proofs and low-frequency ledgers.
- **Issue #56 body** — one editable live recovery record.
- **Active feature branch** — unfinished code only.

`save work != claim theorem complete`.

---

# 3. Mandatory Recovery Protocol

At the start of a new chat:

1. Read this operations manual from `main`.
2. Read `V3_COVERAGE_STATUS.md` from `main`.
3. Read **Issue #56 body**. Do not scan all comments unless a historical ambiguity remains.
4. Query live GitHub:
   - current `main` SHA;
   - open PRs;
   - active branch/head named in Issue #56;
   - branch compare;
   - latest relevant CI.
5. Recover prior-chat reasoning only if it was not persisted in code or Issue #56.
6. Reconcile using the authority hierarchy in §2.
7. Return a compact Recovery Snapshot and immediately execute the exact next action.
8. Do not reopen a counted P-ID unless Issue #56 explicitly records a substantive source mismatch/regression and the ledger confirms the reopen.
9. Do not ask the user to restate previous progress unless repository recovery is genuinely impossible.

Expected snapshot:

```text
main: <sha>
coverage: <N>/106
active P-ID: <pid or none>
feature: <branch>@<sha or none>
open PR: <number or none>
latest CI: <run> <status>
state: proof | integration | promotion | audit | governance
blocker: <if any>
exact next action: <action>
```

---

# 4. Branch Creation Preflight — HARD GATE

**No new remote branch may be created before all checks below pass.**

1. Read `V3_COVERAGE_STATUS.md`: the target P-ID must be uncounted, unless an explicit reopen is recorded.
2. Read Issue #56 body: ensure another branch is not already the active lane.
3. Search existing branches for the same P-ID/topic.
4. Search open PRs for the same P-ID/topic.
5. Fetch live `main` SHA.
6. Reuse the existing active feature branch whenever possible.
7. If a previous branch is superseded, fold/capture needed work and delete the superseded branch before creating a replacement.

If any preflight check fails, **resume/reconcile existing work instead of creating another branch**.

This gate exists specifically to prevent the historical failure modes in which already-counted P-IDs (for example later wrapper audits) were accidentally treated as fresh work and one P-ID accumulated many scratch/version branches.

---

# 5. Branch Lifecycle Protocol

## 5.1 Branch classes and names

Only these remote branch classes are allowed:

- proof feature: `formal/<pid>-<topic>`;
- clean integration: `formal/<pid>-main-integration`;
- ledger promotion: `formal/ledger-<coverage>-<pid>`;
- repository governance/maintenance: `ops/<topic>`;
- explicit temporary quarantine: `hold/<topic>`.

Do **not** create permanent `scratch`, `tmp`, `test`, `v2`, `v3`, `v7`, `fresh`, `clean-v2` branch families. If a proof direction changes, update the same feature branch or delete the obsolete branch before replacing it.

Mathematical modularity belongs in Lean modules, not in permanent branch proliferation.

## 5.2 One-P-ID / one-feature invariant

Normally each active source P-ID has exactly **one** remote feature branch.

Helper lemmas, API experiments and submodules for that P-ID live on that branch. A second remote branch for the same P-ID requires an explicit reason in Issue #56 and must be removed once the experiment is resolved.

Remote scratch branches are prohibited by default. If an emergency remote WIP branch is unavoidable, use `hold/<pid>-<purpose>`, record it in Issue #56, and remove it within one working session after folding or rejecting the result.

## 5.3 Branch budget

Repository-wide target:

- normal remote branches: **<= 8**;
- hard cap: **12**;
- open PRs: normally **<= 2**;
- active theorem feature branches: normally **1**;
- independent source/API audit lane: preferably no branch until code is needed;
- integration/promotion/governance branches: ephemeral only.

If remote branch count exceeds 12, **stop opening theorem branches and perform hygiene first**.

## 5.4 Mandatory deletion points

A branch is disposable once the durable evidence it represented exists elsewhere.

Delete:

- `hold/*`: immediately after work is folded/rejected;
- clean-integration branch: after its PR merges and resulting-main CI is green;
- ledger branch: after ledger PR merges and resulting-main CI is green;
- feature branch: after the theorem is counted full-green and final theorem code is on `main`;
- docs/governance branch: after merge and resulting-main CI is green;
- abandoned/superseded branch: as soon as its needed head SHA/reason is recorded and any useful code is folded elsewhere;
- branches for already-counted P-IDs: unless an explicit reopen is active;
- obsolete default/legacy branches with no unique commits relative to `main`.

Merged PRs, `main`, CI runs, the coverage ledger and Issue #56 milestone comments are the durable proof/audit record. **Permanent feature branches are not an archive.**

## 5.5 Safe-deletion guard

Before deleting a non-obvious branch:

1. confirm there is no open PR from it;
2. confirm it is not named as active in Issue #56;
3. confirm its P-ID is counted or its work is superseded;
4. record branch name + head SHA if it contains unique historical work not already represented by a merged PR;
5. preserve unresolved pending-PID branches until their unique content is audited.

Automated hygiene may delete branches only under these guards and must log deleted branch names/head SHAs to Issue #56.

## 5.6 `main` safety

- never force-push `main`;
- never use `master` for Core 3 work;
- every clean integration starts from the exact latest full-green `main` unless the protocol explicitly says proof-main for the separate ledger stage;
- branch deletion must never target `main`.

---

# 6. Automatic checkpoint discipline

Checkpoint when loss would cause meaningful rework:

- stable proof lemma;
- compiler/API root cause identified and fixed;
- proof architecture materially changes;
- meaningful module milestone;
- before risky refactor.

Use descriptive commits:

```text
wip(P-XYZ): checkpoint before resolving <blocker>
proof(P-XYZ): establish <lemma>
fix(P-XYZ): repair <root cause>
```

Do not create a new branch merely to checkpoint. Keep the unpersisted-work window small on the existing feature branch.

---

# 7. Issue #56 LIVE STATE Protocol

Issue #56 **body**, not the tail of the comments, is the high-frequency live handoff.

The body must contain only current facts:

- full-green coverage + main SHA;
- staged promotion, if any;
- active P-ID/branch/head;
- open PR;
- latest relevant CI;
- blocker/root cause;
- exact next actions;
- do-not-repeat guards.

Update the body on material state transitions. Do not append a new comment for every CI poll or micro-fix.

Issue comments are reserved for durable milestones such as:

- new FULL-GREEN coverage checkpoint;
- theorem source contract locked;
- major proof architecture decision;
- branch-hygiene deletion manifest;
- substantive correction/root-cause postmortem.

Old comments are historical and may be stale. Recovery reads the body first.

---

# 8. Cross-chat handoff protocol

When the user asks for handoff, or a natural conversation boundary approaches:

1. checkpoint meaningful unfinished code on the existing active feature branch;
2. update Issue #56 body with current live fields;
3. persist important reasoning decisions not represented in code;
4. do not create a handoff-only branch unless a real repository change is needed;
5. do not update every low-frequency status file just because a chat is ending;
6. continue useful work after checkpointing if room remains.

Fallback order after unexpected termination:

`Issue #56 body -> active branch -> live PR/CI -> low-frequency ledgers -> milestone comments -> prior chat`.

---

# 9. Low-frequency status documents

These are NOT maintained every chat.

- `V3_COVERAGE_STATUS.md`: counted coverage authority; update only through valid promotion.
- `PID_STATUS.yaml`: major lifecycle transitions and durable audit facts.
- `FORMALIZATION_STATE.md`: project-stage transitions.
- `HANDOFF_LATEST.md`: fallback archive only; never live authority.
- `PID_AUDIT_MATRIX.yaml`: source-to-main audit.
- `LEAN_API_NOTES.md`: reusable API discoveries.

Do not create new state files when an existing authority already covers the information.

---

# 10. CI discipline

Feedback hierarchy:

1. direct module check when available;
2. affected dependency stack;
3. official `lake build UEOT` at source theorem closure, feature freeze, clean integration, PR/main, and ledger gates.

Do not intentionally use full CI as a trial-and-error Lean REPL. If the execution environment only exposes full remote CI, batch coherent fixes before pushing rather than creating branch/commit churn for each speculative edit.

If an ordinary P-ID accumulates roughly 3–5 full-CI failures, stop patching blindly and perform a root-cause / pinned-Mathlib API audit.

---

# 11. Correct parallelism

Preferred concurrent work:

- Lane A: one active proof P-ID;
- Lane B: source-to-main audit of a future P-ID, normally branchless;
- Lane C: API research or the current clean-integration/promotion gate.

Do not run multiple branches that mutate the same theorem/import surface. Do not use CI wait time to spawn speculative dependent branches.

---

# 12. Source-first rule

Before new proof work:

1. read the exact frozen source statement;
2. record assumptions, conclusion, scope and quantifier order;
3. record forbidden strengthening/weakening;
4. audit `V3_COVERAGE_STATUS.md` and current main code;
5. only then write new Lean.

Never silently narrow Standard-Borel to finite/countable, randomized to deterministic, general code spaces to fixed spaces, or a common-version theorem to unrelated per-protocol null sets.

---

# 13. Remaining-PID classification

For each uncounted P-ID classify:

- A — source-facing theorem already exists on `main`;
- B — substantial mathematics exists, wrapper/alignment gap remains;
- C — major components exist, bridge theorem remains;
- D — genuinely new formal mathematics required.

Prefer A -> B -> C -> D, adjusted by dependency unlock and reuse value.

`pending` means only “not counted”; it does not mean “no Lean exists”.

---

# 14. Clean integration and promotion protocol

Once a source-facing feature theorem is fully green:

1. freeze the feature;
2. fetch exact live full-green `main`;
3. create one clean integration branch;
4. replay only final validated files/imports;
5. compare integration vs main for unrelated changes;
6. run source semantic + prohibited-proof audit;
7. require full integration CI;
8. merge through PR;
9. require resulting-main full CI;
10. create one separate ledger branch from that proof-main;
11. ledger PR must change only the authoritative recovery/coverage documents;
12. require ledger PR CI, merge, then resulting-main CI;
13. only then increment FULL-GREEN coverage;
14. delete feature, integration and ledger branches according to §5.

Feature green must never directly increment coverage.

---

# 15. Prohibited-proof audit

Before promotion inspect the integrated diff for at least:

- `sorry`;
- Lean `admit`;
- `native_decide` used as a proof bypass;
- unsourced new axioms.

Audit semantically rather than by naive word count.

---

# 16. Governance health checks

At recovery and after each counted promotion, check:

- branch count <= 8 target / <= 12 hard cap;
- no stale open PR;
- Issue #56 body matches live GitHub;
- no active branch for a counted P-ID;
- no duplicate branch for an active P-ID;
- no ledger/integration branch left after its lifecycle closes;
- `main` is the only integration branch;
- authoritative coverage partition sums to 106.

If these fail, governance repair takes priority over opening new proof lanes.

---

# 17. Final operating loop

`RECOVER -> RECONCILE -> BRANCH PREFLIGHT -> AUDIT -> PROVE -> CHECKPOINT -> VERIFY -> CLEAN-INTEGRATE -> PROMOTE -> DELETE EPHEMERAL BRANCHES -> CONTINUE`.

Central invariants:

**A chat may end at any time; meaningful state must already exist outside that chat.**

**A branch may disappear after its lifecycle; durable truth must already exist in main, ledgers, PR/CI evidence and Issue #56.**
