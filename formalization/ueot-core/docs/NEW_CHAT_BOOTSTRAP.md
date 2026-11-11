# UEOT Core — Current Cross-Chat Bootstrap

Updated: **2026-11-11**. The current status index is
[core/status/CURRENT.md](../../../core/status/CURRENT.md); this page is its recovery procedure.
The original 106-P-ID construction workflow is retained below as history.

## 1. Start from the actual current task

A sufficient user prompt is:

```text
继续 UEOT Core。先刷新真实 main、工作树和当前任务，读取 core/status/CURRENT.md
及其对应合同、验收和必要补充；保留已完成状态，复用仍适用的证据，按本次授权目标继续。
不要按历史 SHA 回退，不从旧路线图重开已经完成的工作。
```

The assistant should:

1. Inspect current `main`, the actual worktree, applicable `AGENTS.md`, open work
   and current repository policy. Protect another session's uncommitted work.
2. Read [the current Core index](../../../core/status/CURRENT.md) and follow the exact adopted package
   for this request. A larger version label, attachment date or historical chat
   does not establish which contract is current.
3. Use [V3_COVERAGE_STATUS.md](V3_COVERAGE_STATUS.md) for the frozen 106 P-ID
   ledger only. The [classified Core](compression/theory_completion/unified_closure/core_theory_closure_v1/README.md), PR #446
   [reader hardening](../../../mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md) and PR #447 [growth classification](compression/theory_completion/unified_closure/core_growth_classification_v1/README.md)
   are completed packages with distinct evidence and scope.
4. Match the current implementation and book bytes to the relevant validation
   before reporting completion. The growth classification is no longer merely
   a suggested next task; its finite exponential contracts and internal-program
   iff results are in production Lean. The written 2/3/4 classification and
   source-specific rank-three supplement have a different proof status.
5. Inspect the relevant existing branch and PR before starting another one.
   Follow current branch ownership and protection rules; do not turn a new
   conversation into a global branch cleanup or an unsolicited new proof lane.
6. Reuse accepted evidence when its source and assumptions are unchanged.
   Validate actual changes under the current local-validation/CI policy and
   task contract; do not automatically re-enable or repeat global CI.
7. Report a concise factual recovery summary, then execute the authorized task.
   If the named package is already complete, report that fact and use the
   user's current objective rather than manufacturing another closure debt.

A useful recovery summary records the actual main/head/tree, working changes,
applicable package, completed results being reused, in-flight ownership,
remaining authorized work and the evidence needed for its exit.

## 2. Preserve a concrete handoff

At a meaningful stable point, preserve unfinished work and its source identity,
actual validation, remaining obligations and safe resumption location in the
current task's existing handoff. Keep old failures and review corrections.
Use the authorized publication/handoff workflow, and do not label a WIP commit
as a completed theorem or a merged package.

Issue #56 remains provenance for the original 106-P-ID lifecycle. Issue trackers
and older handoffs can locate evidence, but neither overrides current code,
adopted contracts, exact validation or the user's current instructions. A
completed package does not require another issue update or reconstruction just
because a new conversation begins.

## 3. Historical construction workflow

The following original text records the former 106-P-ID workflow. Its active
lane fields, Issue #56 routing and CI/promotion sequence are historical in this
context; they are not the post-106 startup procedure above. The frozen source
semantics and accepted proof evidence remain preserved.

<details>
<summary>Original Core 3 construction and handoff procedure</summary>

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

</details>
