# UEOT Core 3 Lean — New Chat Bootstrap

This file defines the user-facing cross-chat workflow. The user should need only two short commands.

## A. Starting a new conversation

The preferred first message is simply:

```text
继续 UEOT Core 3 Lean 全形式化。执行仓库 Recovery Protocol，恢复上一轮施工现场并直接继续，不要让我重复说明。
```

The AI must then do all recovery and branch-governance work itself. For UEOT Core 3, **Recovery Protocol automatically includes Repository Branch Governance**; the user does not need to request branch management separately.

Mandatory startup chain:

`NEW_CHAT_BOOTSTRAP -> REPOSITORY_BRANCH_GOVERNANCE -> UEOT_CORE3_LEAN_OPERATIONS -> Issue #56 -> live GitHub reconciliation -> exact next action`

The AI must:

1. Read from `MurphyHoops/UEOT` `main`, in this order:
   - `docs/REPOSITORY_BRANCH_GOVERNANCE.md`
   - `formalization/ueot-core/docs/UEOT_CORE3_LEAN_OPERATIONS.md`
   - `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`
2. Read GitHub Issue #56:
   `[LIVE] UEOT Core 3 Lean Formalization — Current State & Cross-Chat Handoff`.
   This is the single high-frequency live construction-state anchor.
3. Recover the most recent prior UEOT Core 3 Lean conversation only for reasoning not already checkpointed in code/docs/Issue #56.
4. Query live GitHub before creating or changing branches:
   - current `main` SHA;
   - complete remote branch inventory and branch count;
   - active feature branch/head from Issue #56;
   - open PRs;
   - relevant branch compare;
   - latest relevant CI.
5. Run the repository governance health check automatically:
   - `main` is the only integration branch;
   - branch count is within the repository target/hard cap;
   - no duplicate active branches represent the same work item/P-ID;
   - no stale merged integration/ledger/governance branches remain;
   - no active branch corresponds to an already-counted P-ID unless an explicit reopen is recorded;
   - Issue #56 live fields agree with GitHub reality;
   - unknown/new namespaces remain protected from destructive cleanup.
6. Reconcile using the authority hierarchy:
   - frozen source controls theorem semantics;
   - `V3_COVERAGE_STATUS.md` controls counted coverage;
   - live `main`/branches/PRs/Actions control actual code and CI;
   - Issue #56 controls current construction intent/blocker/next action;
   - prior chat is supplemental only.
7. If the governance health check fails, repair/reconcile governance before opening new proof lanes. Do not create a new branch merely because a new chat or development platform started.
8. Apply the Branch Creation Preflight from `UEOT_CORE3_LEAN_OPERATIONS.md` before any new remote branch. Reuse an existing valid active branch whenever possible.
9. Return a compact Recovery Snapshot and immediately continue the exact next action.
10. Never ask the user to restate the previous chat unless repository recovery is genuinely impossible.

Expected snapshot:

```text
Recovery complete.
main: <sha>
coverage: <N>/106
remote branches: <count>
governance: healthy | repair-required
active P-ID: <pid or none>
feature: <branch>@<sha or none>
open PR: <number or none>
latest CI: <run> <status>
state: proof | integration | promotion | audit | governance
blocker: <if any>
exact next action: <action>
```

Then continue actual Lean/GitHub work immediately.

## B. When the current conversation is near its limit

The user can say only:

```text
执行 UEOT Core 3 跨对话交接，然后继续做到当前聊天不能继续为止。
```

The AI must then:

1. Preserve all meaningful unfinished code on the active feature branch with a descriptive WIP checkpoint commit and push it. A WIP commit may be red/non-final and MUST NOT change coverage.
2. Update Issue #56 with only materially changed live fields:
   - active P-ID;
   - active branch and latest checkpoint head;
   - latest relevant CI;
   - current blocker/root cause;
   - exact next action;
   - do-not-repeat notes / newly pinned API facts.
3. If there are important reasoning decisions that are not represented in code, add them to Issue #56.
4. Do NOT update all formal status documents merely because a chat is ending. `PID_STATUS.yaml`, `FORMALIZATION_STATE.md`, `HANDOFF_LATEST.md`, and `V3_COVERAGE_STATUS.md` are updated only at real lifecycle transitions such as feature freeze, integration, promotion, or global audit.
5. Do not create a handoff-only, scratch, fresh, or versioned replacement branch. The same durable work item continues on the same active branch unless the repository governance protocol records a justified replacement.
6. After checkpointing, continue useful work in the current chat if room remains. Do not stop merely because a handoff was created.

## C. Automatic checkpoint discipline during a long chat

Do not wait for the user to request handoff. During normal work the AI should checkpoint after any nontrivial change whose loss would cause substantial rework, especially after:

- a new proof lemma becomes stable;
- a real CI/compiler root cause is identified and a fix is applied;
- proof architecture materially changes;
- a module reaches a meaningful stable point;
- before beginning a risky refactor or a new major proof block.

Use descriptive commits such as:

```text
wip(P-XYZ): checkpoint before resolving <blocker>
proof(P-XYZ): establish <lemma>
fix(P-XYZ): repair <root cause>
```

Saving and completion are separate concepts:

`WIP checkpoint != feature green != main integration != counted proof`.

Checkpointing also does not justify creating a second remote branch for the same work item.

## D. If the conversation ends unexpectedly

Recovery uses the following redundancy:

1. repository branch-governance protocol — branch lifecycle and preflight authority;
2. active feature branch WIP commits — authoritative unfinished code state;
3. Issue #56 — current intent/blocker/next action;
4. live GitHub CI/PR state;
5. prior-chat recovery — emergency reasoning supplement.

Meaningful edits that exist only in an ephemeral uncommitted working tree cannot be guaranteed recoverable. Therefore the unpersisted-work window must be kept small through frequent WIP checkpoint commits.

## E. User-facing rule

In normal use the user only needs to remember:

**Start:**

```text
继续 UEOT Core 3 Lean 全形式化。执行仓库 Recovery Protocol，恢复上一轮施工现场并直接继续，不要让我重复说明。
```

This single command means both **recover the work state** and **automatically reconcile/manage branches according to repository governance**.

**Before switching chats:**

```text
执行 UEOT Core 3 跨对话交接，然后继续做到当前聊天不能继续为止。
```

Everything else is the AI's responsibility.
