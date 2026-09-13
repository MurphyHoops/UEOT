# UEOT Core 3 Lean Formalization — Cross-Chat Operations Manual

> Purpose: make UEOT Core 3 Lean formalization resumable across arbitrarily many ChatGPT conversations while minimizing status-maintenance overhead. No single chat may be a single point of failure.

## 0. Project identity

- Repository: `MurphyHoops/UEOT`
- Formal integration branch: `main`
- Frozen source specification: `UEOT_Core_Mathematics_v3.0_Complete.md`
- Frozen source P-IDs: `106`
- Lean: `4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Official final target: `lake build UEOT`
- Counted coverage truth: `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`
- Single high-frequency live construction state: GitHub Issue #56
- Unfinished code state: active feature branch WIP checkpoints

Important: repository metadata may still report `master` as default. Every UEOT Core 3 operation must explicitly use `main` unless a specific feature/integration branch is named.

---

# 1. Ultimate completion criterion

The project is complete only when all 106 frozen source-level P-IDs are machine verified and counted:

`106/106`.

Proof lifecycle:

`SOURCE AUDIT -> PROOF CONTRACT -> EXISTING-CODE AUDIT -> LEAN DEVELOPMENT -> FEATURE GREEN -> SOURCE RE-AUDIT -> PROHIBITED-PROOF AUDIT -> CLEAN INTEGRATION -> INTEGRATION GREEN -> MAIN -> POST-MAIN GREEN -> LEDGER UPDATE -> COUNTED PROVED`.

Therefore:

- helper theorem green != source theorem proved;
- WIP checkpoint != feature green;
- feature green != counted coverage;
- PR open != proved;
- a theorem with stronger assumptions or weaker conclusion than the frozen source does not close the P-ID.

---

# 2. Minimal persistence architecture

The project uses four durable layers.

## Layer A — Frozen source

`UEOT_Core_Mathematics_v3.0_Complete.md` determines theorem semantics.

## Layer B — `main`

`main` contains integrated formal code and low-frequency formal status/ledger documents.

## Layer C — GitHub Issue #56

Issue #56 is the **single high-frequency live construction-state anchor**. It records only what changes during active work:

- active P-ID;
- active feature/integration branch;
- latest checkpoint head;
- latest relevant CI;
- current blocker/root cause;
- exact next action;
- do-not-repeat notes;
- newly important pinned API facts.

Updating Issue #56 does not change `main` and does not trigger Lean CI.

## Layer D — active feature branch

Unfinished Lean code is preserved by WIP checkpoint commits on the active feature branch. A WIP commit may be red/non-final and never changes formal coverage.

This separation is mandatory:

`save work != claim theorem complete`.

Prior conversations are only an emergency supplement for reasoning not yet persisted.

---

# 3. Two user commands

The user should normally need only two commands.

## Start a new chat

```text
继续 UEOT Core 3 Lean 全形式化。执行仓库 Recovery Protocol，恢复上一轮施工现场并直接继续，不要让我重复说明。
```

## Before switching chats / near chat limit

```text
执行 UEOT Core 3 跨对话交接，然后继续做到当前聊天不能继续为止。
```

Everything else is the AI's responsibility.

---

# 4. Mandatory Recovery Protocol

When starting a new chat, the AI must:

1. Read this operations manual from `main`.
2. Read `V3_COVERAGE_STATUS.md` from `main` for counted coverage.
3. Read GitHub Issue #56 for live construction state.
4. Recover the most recent prior UEOT Core 3 Lean conversation to obtain reasoning that may not yet be checkpointed.
5. Query live GitHub:
   - current `main` SHA;
   - active branch/head named in Issue #56;
   - branch compare;
   - latest relevant CI;
   - PR/integration branch state.
6. Reconcile using:
   - frozen source -> theorem semantics;
   - `V3_COVERAGE_STATUS.md` -> counted coverage;
   - live branch/Actions -> actual code/CI state;
   - Issue #56 -> current construction intent/blocker/next action;
   - prior chat -> supplementary reasoning only.
7. Return a compact Recovery Snapshot and immediately execute the exact next action.
8. Do not ask the user to restate previous progress unless recovery is genuinely impossible.

Expected snapshot:

```text
main: <sha>
coverage: <N>/106
active P-ID: <pid>
feature: <branch>@<sha>
latest CI: <run> <status>
state: proof | integration | promotion | audit
blocker: <if any>
exact next action: <action>
```

---

# 5. Automatic checkpoint discipline

Do not wait for the end of a conversation. During normal work, checkpoint whenever loss would cause meaningful rework.

Checkpoint after events such as:

- a proof lemma becomes stable;
- a real compiler/CI root cause is identified and a fix is applied;
- proof architecture materially changes;
- a module reaches a meaningful stable point;
- before a risky refactor or a new major proof block.

Use descriptive commits:

```text
wip(P-XYZ): checkpoint before resolving <blocker>
proof(P-XYZ): establish <lemma>
fix(P-XYZ): repair <root cause>
```

A WIP commit may fail CI. It exists to preserve work, not to certify completion.

Meaningful edits that exist only in an ephemeral uncommitted working tree cannot be guaranteed recoverable in a new chat. Therefore keep the unpersisted-work window small.

---

# 6. Cross-chat handoff protocol

When the user asks for handoff, or when the AI is approaching a natural conversation boundary, the AI must:

1. Push meaningful unfinished code to the active feature branch as a WIP checkpoint.
2. Update Issue #56 with only materially changed live fields.
3. Persist important reasoning decisions not represented in code into Issue #56.
4. Do not update every formal status file merely because the conversation is ending.
5. Continue useful work after checkpointing if room remains; handoff creation is not a command to stop early.

If the conversation terminates unexpectedly, recovery falls back to:

`feature WIP commits -> Issue #56 -> live CI/PR -> prior chat reasoning`.

---

# 7. Low-frequency status documents

These are NOT maintained every chat.

- `V3_COVERAGE_STATUS.md`: update only after valid counted promotions.
- `PID_STATUS.yaml`: update at major lifecycle transitions such as proof -> integration -> proved, or significant audit state changes.
- `FORMALIZATION_STATE.md`: update at meaningful project-stage transitions.
- `HANDOFF_LATEST.md`: fallback archival snapshot only; Issue #56 is the live handoff.
- `PID_AUDIT_MATRIX.yaml`: update during remaining-PID source-to-main audit.
- `LEAN_API_NOTES.md`: update when an API discovery is reusable beyond the active lane.

Daily active work should require only:

`active branch checkpoint + Issue #56 update when state materially changes`.

---

# 8. Proof-development efficiency model

Use three feedback tiers.

## Tier 1 — module check

Prefer direct Lean/module builds for the edited module.

## Tier 2 — affected stack

Build only the dependency stack touched by the change.

## Tier 3 — official target

Run `lake build UEOT` only at important milestones such as source-theorem closure, feature freeze, integration, main, and post-main.

Do not use GitHub full CI as a Lean REPL.

If an ordinary P-ID exceeds roughly 3–5 full-CI failures, pause trial-and-error and perform a root-cause/API audit.

---

# 9. Branch discipline

One active source P-ID should normally have one development branch:

`formal/<pid>-<topic>`.

Mathematical modularity belongs in Lean modules, not many permanent branches.

When feature proof is ready, create a clean integration branch from live latest `main` and replay only final validated files. Do not merge a long stale development history wholesale.

Recommended active branch target: fewer than 20.

---

# 10. Correct parallelism

Preferred lanes:

- Lane A: one active proof P-ID;
- Lane B: independent source-to-main audit of future P-IDs;
- Lane C: Mathlib/API research or clean integration work.

Do not run multiple branches that independently mutate the same source theorem/import region.

While milestone CI runs, use time for independent audit/API work rather than stacking speculative dependent fixes.

---

# 11. Source-first rule

Before new proof work:

1. read the exact frozen source statement;
2. record assumptions, conclusion, scope and quantifier order;
3. record forbidden strengthening/weakening;
4. audit existing main code;
5. only then write new Lean.

Never silently narrow Standard-Borel to finite/countable, randomized to deterministic, general code spaces to fixed spaces, or a common-version theorem to unrelated per-protocol null sets.

---

# 12. Remaining-PID classification

After the active P-ID closes, audit all remaining unclassified P-IDs and classify:

- A — source-facing theorem already exists on `main`;
- B — substantial mathematics exists, wrapper/alignment gap remains;
- C — major components exist, bridge theorem remains;
- D — genuinely new formal mathematics required.

Prefer A -> B -> C -> D, adjusted by dependency unlock and reuse value.

Do not assume pending means unformalized.

---

# 13. Integration protocol

Once the source-facing feature theorem is fully green, freeze the feature.

1. fetch live latest `main`;
2. create/refresh `formal/<pid>-main-integration` from that exact main;
3. replay only final validated files/imports;
4. compare integration vs main for unrelated changes;
5. run prohibited-proof audit;
6. run official full CI;
7. integrate to main only after green;
8. run post-main full CI;
9. only then update ledgers and coverage.

Feature green must never directly increment coverage.

---

# 14. Prohibited-proof audit

Before promotion inspect the integrated diff for at least:

- `sorry`;
- Lean `admit`;
- `native_decide` used as a proof bypass;
- unsourced new axioms.

Audit semantically rather than by naive word count.

---

# 15. Current live recovery source

Do not treat a static SHA in this manual as current state. The live state is in Issue #56 plus actual GitHub branches/Actions.

At the time this manual was updated, counted coverage was still `54/106` and P-INT-01's feature proof had already passed its feature-level full target. A new chat must still re-query live GitHub before acting.

---

# 16. Final operating loop

`RECOVER -> AUDIT -> PROVE -> CHECKPOINT -> VERIFY -> INTEGRATE -> PROMOTE -> CONTINUE`.

The central invariant is:

**A chat may end at any time; meaningful formalization state must already exist outside that chat.**
