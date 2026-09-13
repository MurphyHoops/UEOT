# UEOT Core 3 Lean Formalization — Cross-Chat Operations Manual

> Purpose: make UEOT Core 3 Lean formalization resumable across arbitrarily many ChatGPT conversations. No single chat may be a single point of failure.

## 0. Project identity

- Repository: `MurphyHoops/UEOT`
- Formal integration branch: `main`
- Frozen source specification: `UEOT_Core_Mathematics_v3.0_Complete.md`
- Frozen source P-IDs: `106`
- Lean: `4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Official final target: `lake build UEOT`
- Coverage truth: `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`
- Machine-readable lane state: `formalization/ueot-core/docs/PID_STATUS.yaml`
- Human-readable global state: `formalization/ueot-core/docs/FORMALIZATION_STATE.md`
- Dynamic construction handoff: `formalization/ueot-core/docs/HANDOFF_LATEST.md`

Important: GitHub repository metadata may still report `master` as default branch. All UEOT Core 3 recovery and formalization operations MUST explicitly use `main` unless a specific feature branch is named.

---

# 1. Ultimate completion criterion

The project is complete only when all 106 frozen source-level P-IDs are machine verified and counted:

`106/106`.

A theorem is not counted merely because a similarly named Lean declaration exists. A source P-ID is counted only after semantic matching to the frozen source statement, official import reachability, machine checking, clean integration into `main`, green post-main CI, prohibited-proof audit, and ledger synchronization.

The authoritative proof lifecycle is:

`SOURCE AUDIT -> PROOF CONTRACT -> EXISTING-CODE AUDIT -> LEAN DEVELOPMENT -> FEATURE GREEN -> SOURCE RE-AUDIT -> PROHIBITED-PROOF AUDIT -> CLEAN INTEGRATION -> INTEGRATION GREEN -> MAIN -> POST-MAIN GREEN -> LEDGER UPDATE -> COUNTED PROVED`.

Therefore:

- helper theorem green != source theorem proved;
- feature branch green != counted coverage;
- PR open != proved;
- PR merged without post-main verification != counted;
- a theorem with stronger assumptions or weaker conclusion than the frozen source does not close the P-ID.

---

# 2. Repository truth hierarchy

When information conflicts, use this priority order.

1. Frozen source specification: `UEOT_Core_Mathematics_v3.0_Complete.md`.
2. Actual GitHub `main` contents and branch SHAs.
3. `docs/V3_COVERAGE_STATUS.md` for counted coverage.
4. `docs/PID_STATUS.yaml` for machine-readable P-ID state.
5. `docs/FORMALIZATION_STATE.md` for human-readable project state.
6. `docs/HANDOFF_LATEST.md` for the latest construction checkpoint.
7. Previous ChatGPT conversations / recovered personal context.

Conversation history is auxiliary evidence only. GitHub and the frozen source are the durable project truth.

If `PID_STATUS.yaml` or `FORMALIZATION_STATE.md` is stale but GitHub and `HANDOFF_LATEST.md` show a newer branch/CI state, treat the stale fields as needing synchronization, not as authority over the actual branch.

---

# 3. Mandatory Recovery Protocol for every new chat

A new conversation MUST NOT immediately start writing Lean. It must first recover state.

## R0. Identify the project

Confirm the task is UEOT Core 3 Lean formalization, not UEOT-QM, UEOT-AI, an older v1.x/v2.x mathematics draft, or a physics application branch.

## R1. Recover the latest cross-chat work

Use available personal-context / conversation-recovery capability to retrieve the most recent UEOT Core 3 Lean conversation. Recover, if available:

- active P-ID;
- last active feature branch;
- latest commit SHA;
- latest CI run and status;
- last real Lean error;
- proof architecture already selected;
- exact next action;
- explicit do-not-repeat decisions.

Do not ask the user to restate information that can be recovered.

## R2. Read the durable operating state from `main`

Explicitly read these files from `ref=main`:

1. `formalization/ueot-core/docs/UEOT_CORE3_LEAN_OPERATIONS.md`
2. `formalization/ueot-core/docs/HANDOFF_LATEST.md`
3. `formalization/ueot-core/docs/PID_STATUS.yaml`
4. `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`
5. `formalization/ueot-core/docs/FORMALIZATION_STATE.md`

Do not omit `ref=main` merely because GitHub has a default branch.

## R3. Query live GitHub state

At minimum query:

- current `main` SHA;
- active feature branch SHA;
- `main...feature` compare;
- latest feature CI;
- latest main CI;
- any relevant open PR;
- integration branch if one exists.

Never assume SHAs written in this manual are still current.

## R4. Reconcile sources

Rules:

- theorem semantics: frozen Core 3 source wins;
- counted coverage: `V3_COVERAGE_STATUS.md` wins;
- branch head: GitHub live branch wins;
- CI status: live Actions status wins;
- exact next action: derive from live GitHub + `HANDOFF_LATEST.md` + recovered recent conversation.

## R5. Print a compact Recovery Snapshot

Before continuing actual work, report approximately:

```text
main: <sha>
coverage: <N>/106
active P-ID: <pid>
feature: <branch>@<sha>
latest CI: <run> <status>
state: proof | integration | promotion | audit
exact next action: <one concrete step>
```

Then immediately execute the next action. Do not stop at planning.

---

# 4. Standard new-chat bootstrap prompt

The user can paste the following into every new conversation:

```text
继续 UEOT Core 3 Lean 全形式化。

首先执行跨对话 Recovery Protocol：

1. 检索我过去对话中最近一次 UEOT Core 3 Lean formalization 的最新工作状态；
2. 显式从 GitHub MurphyHoops/UEOT 的 main 分支读取：
   formalization/ueot-core/docs/UEOT_CORE3_LEAN_OPERATIONS.md
   formalization/ueot-core/docs/HANDOFF_LATEST.md
   formalization/ueot-core/docs/PID_STATUS.yaml
   formalization/ueot-core/docs/V3_COVERAGE_STATUS.md
   formalization/ueot-core/docs/FORMALIZATION_STATE.md
3. 查询当前 main SHA、active feature branch、最新 CI、branch compare、PR；
4. 对 GitHub 状态、handoff 和上一轮聊天进行 reconciliation；
5. 给我一个简短 Recovery Snapshot；
6. 不要重新证明已经 green / integrated / counted 的内容；
7. 立即从上一轮 exact next action 接着推进；
8. 每个重要 checkpoint 更新 HANDOFF_LATEST.md；
9. feature green 不得直接增加 coverage；
10. 目标始终是冻结版 UEOT Core 3 的 106/106 source-level Lean machine verification；
11. 不要把 GitHub full CI 当 Lean REPL；先模块级检查，再 affected-stack，再 milestone full CI；
12. 恢复完成后立即执行实际 proof / fix / audit / integration，不要只给计划。
```

---

# 5. Dynamic handoff protocol

`HANDOFF_LATEST.md` is the cross-chat relay baton. It is intentionally high-frequency and may be updated much more often than coverage ledgers.

It MUST record:

- timestamp;
- current `main` SHA;
- counted coverage;
- active P-ID and exact frozen target;
- active branch and head;
- compare-to-main status;
- latest CI run/status;
- machine-checked milestones;
- current blocker or latest real Lean error;
- latest fix;
- exact next action;
- do-not-repeat items;
- pinned Mathlib/API facts learned during the lane;
- any reasoning from the current conversation not yet represented elsewhere.

Update `HANDOFF_LATEST.md` after any checkpoint whose loss would likely cause more than a few minutes of repeated work, especially:

- source interpretation changes;
- proof architecture changes;
- important theorem first becomes green;
- CI failure root cause is identified;
- feature proof becomes fully green;
- integration branch is created;
- integration CI succeeds;
- main is updated;
- post-main CI succeeds;
- coverage is promoted;
- active P-ID changes.

Do NOT wait until the chat is almost full. A conversation can terminate unexpectedly.

---

# 6. Proof-development efficiency model

The principal engineering failure mode to avoid is using GitHub full CI as a parser/typechecker.

Use three feedback tiers.

## Tier 1 — module check

Prefer a direct Lean or module build for the currently edited file/module, e.g. as appropriate for the repo:

- `lake env lean UEOT/V3/Foo.lean`
- or `lake build UEOT.V3.Foo`

Catch syntax, namespace, theorem-name, argument-order, typeclass and local elaboration failures here.

## Tier 2 — affected-stack check

If the dependency chain is `FooCore -> FooForward -> FooReverse -> FooSource`, build the affected stack only.

## Tier 3 — official full target

Run `lake build UEOT` only at important milestones:

- reusable foundation closure;
- source-facing theorem closure;
- feature freeze;
- integration candidate;
- main/post-main validation.

Target full-CI failure budget for ordinary P-IDs: no more than roughly 3–5 failures. If exceeded, pause trial-and-error and perform a root-cause/API audit.

---

# 7. Branch discipline

One active source P-ID should normally have one development branch:

`formal/<pid>-<topic>`.

Mathematical modularity should be expressed by Lean modules, not dozens of permanent Git branches.

Good:

- `FooCore.lean`
- `FooCanonical.lean`
- `FooForward.lean`
- `FooReverse.lean`
- `FooSource.lean`

Bad branch topology:

- `formal/foo-core`
- `formal/foo-forward`
- `formal/foo-fix1`
- `formal/foo-fix2`
- `formal/foo-clean-v3`

When a long development branch is ready, create a clean integration branch from latest `main` and replay only validated final files. Do not merge large stale feature history wholesale.

Recommended active-branch target: fewer than 20 branches. Historical evidence should live in commits/PRs/tags; merged or superseded branches should be deleted periodically.

If a feature branch is significantly behind `main` or has accumulated many experimental commits, prefer a clean-port integration rather than continued drift.

---

# 8. Correct parallelism

Parallelism means independent lanes, not duplicate edits to the same theorem.

Preferred pattern:

- Lane A: one active proof P-ID;
- Lane B: independent source-to-main audit of future P-IDs;
- Lane C: Mathlib/API investigation or integration work.

Avoid multiple branches simultaneously modifying the same theorem or the same import region.

While full CI is running, use the time for an independent source audit or API search, but do not stack speculative dependent fixes before the previous CI result is known.

---

# 9. Source-first proof contract

Before new Lean work on a P-ID:

1. read the exact frozen Core 3 source statement;
2. record assumptions, conclusion, scope, quantifier order and almost-sure conventions;
3. explicitly record forbidden strengthening/weakening;
4. audit existing `main` code;
5. only then design new lemmas.

Never let convenience in Lean silently narrow Standard-Borel to finite/countable, randomized to deterministic, general code spaces to fixed spaces, or common-version statements to protocol-by-protocol unrelated null sets.

---

# 10. Existing-code audit and remaining-PID classification

After the currently active P-ID closes, all remaining unclassified P-IDs should be audited before opening many new proof stacks.

Classify each as:

- A — source-facing theorem already exists on `main`; needs semantic audit/promotion only;
- B — substantial mathematics exists; source wrapper/assumption alignment missing;
- C — major components exist; one or more bridge theorems missing;
- D — genuinely new formal mathematics required.

Preferred closure order: A -> B -> C -> D, adjusted by dependency-unlock value.

A useful prioritization heuristic is roughly:

`priority = coverage_gain * reuse_factor * dependency_unlock / estimated_cost`.

Do not assume `pending` means `unformalized`.

---

# 11. Integration protocol

Once the feature source theorem is fully green, freeze it. Do not keep adding improvements.

1. fetch latest `main`;
2. create `formal/<pid>-main-integration` from that exact main;
3. replay only final validated files/imports;
4. compare integration vs `main` and verify there are no unrelated changes or accidental deletions;
5. run prohibited-proof audit (`sorry`, `admit`, `native_decide`, unsourced `axiom`);
6. run official full CI;
7. update/merge `main` only after integration green;
8. run post-main full CI;
9. only then update ledgers and coverage.

Feature green must never directly increment coverage.

---

# 12. Prohibited-proof audit

Before promotion, inspect the integrated diff for at least:

- `sorry`;
- `admit`;
- `native_decide` used to bypass core proof obligations;
- new unsourced axioms.

Not every occurrence of the English word `admit` in comments is a Lean placeholder. Audit semantically, not by naive string count alone.

---

# 13. Status-document roles

Keep responsibilities separated.

- `UEOT_CORE3_LEAN_OPERATIONS.md`: how the project operates; changes rarely.
- `HANDOFF_LATEST.md`: exact construction-site state; changes often.
- `V3_COVERAGE_STATUS.md`: counted source-level truth; change only after valid promotions.
- `PID_STATUS.yaml`: machine-readable P-ID lifecycle and proof contracts.
- `FORMALIZATION_STATE.md`: human-readable global snapshot.
- future `PID_AUDIT_MATRIX.yaml`: A/B/C/D audit of remaining P-IDs.
- future `LEAN_API_NOTES.md`: pinned Mathlib/Lean API facts learned from real failures.

---

# 14. Project-health targets

Track periodically:

- counted coverage;
- new-mathematics closure vs promotion-only closure;
- feature full-CI pass rate;
- full-CI failures per P-ID;
- active branch count;
- branch drift from `main`;
- status-file staleness;
- `main` build status.

Desired direction:

- active branches < 20;
- feature milestone full-CI pass rate > 70%;
- ordinary P-ID full-CI failures <= 5;
- clean integration branches based on latest `main`;
- handoff no more than one milestone stale.

---

# 15. Current verified snapshot — 2026-09-13

THIS SECTION IS A SNAPSHOT ONLY. Every new chat must re-query GitHub before acting.

At this synchronization:

- `main`: `4c2e20e493e0137c90fc0229f73cdc95ae3a29a0`;
- counted coverage: `54/106`;
- newest counted P-ID: `P-INFO-03`;
- active P-ID: `P-INT-01`;
- P-INT-01 feature branch: `formal/pint01-factorization-iff`;
- P-INT-01 verified feature head: `3943391af4d459a370ab840d1b15babcae26f82a`;
- P-INT-01 full-target CI: `34747270058`, success;
- feature vs current main at this checkpoint: ahead 24, behind 1;
- final feature delta is only 7 target files, so stale feature history must NOT be merged wholesale.

P-INT-01 feature proof currently contains the Core 3 scope required for promotion:

- general Standard-Borel predictive factorization iff;
- structured `H=(H^S,H^E)` specialization;
- `M=f(H^S)`, `U=g(H^E)`;
- countable protocol family;
- one common conull set;
- protocol-indexed Markov decoders;
- a common measurable decoder representation.

Therefore the P-INT-01 mathematical feature lane is frozen unless a source audit reveals a real mismatch.

Exact next action at this snapshot:

1. start from latest `main`;
2. use/create `formal/pint01-main-integration` from latest `main`;
3. replay only the final validated 7 files;
4. compare against `main` for accidental deletions/unrelated changes;
5. prohibited-proof audit;
6. full integration CI;
7. merge/fast-forward `main` only when green;
8. post-main full CI;
9. update `PID_STATUS.yaml`, `V3_COVERAGE_STATUS.md`, `FORMALIZATION_STATE.md`, and `HANDOFF_LATEST.md`;
10. only then move coverage `54/106 -> 55/106`.

Do NOT reopen the P-INT-01 single-protocol, canonicalization, forward, reverse or common-countable proofs without a real source mismatch/regression.

---

# 16. Immediately after P-INT-01

Do NOT randomly choose the next hard theorem.

Run a systematic source-to-main audit of the remaining 51 currently unclassified P-IDs and classify them A/B/C/D. The purpose is to identify fast promotions and shared bridge dependencies before starting expensive new proof stacks.

Recommended next artifacts:

- `docs/PID_AUDIT_MATRIX.yaml`;
- `docs/LEAN_API_NOTES.md`.

Then schedule work by dependency clusters and shortest validated closure paths.

---

# 17. Handoff invariant

The central invariant for the whole program is:

> Any individual ChatGPT conversation may disappear, but the UEOT Core 3 formalization state must remain reconstructible from GitHub.

Every work cycle follows:

`Recover -> Audit -> Prove -> Verify -> Integrate -> Promote -> Handoff`.

Every AI instance must optimize for final source-level machine verification `106/106`, not for number of commits, number of branches, or length of a conversation.
