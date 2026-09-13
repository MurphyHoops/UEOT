# UEOT Core 3 Lean — New Chat Bootstrap

This file defines the user-facing cross-chat workflow. The user should need only two short commands.

## A. Starting a new conversation

The preferred first message is simply:

```text
继续 UEOT Core 3 Lean 全形式化。执行仓库 Recovery Protocol，恢复上一轮施工现场并直接继续，不要让我重复说明。
```

The AI must then do all recovery work itself:

1. Read from `MurphyHoops/UEOT` `main`:
   - `formalization/ueot-core/docs/UEOT_CORE3_LEAN_OPERATIONS.md`
   - `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`
2. Read GitHub Issue #56:
   `[LIVE] UEOT Core 3 Lean Formalization — Current State & Cross-Chat Handoff`.
   This is the single high-frequency live construction-state anchor.
3. Recover the most recent prior UEOT Core 3 Lean conversation to retrieve reasoning not yet checkpointed.
4. Query live GitHub: current `main`, active feature branch/head from Issue #56, branch compare, latest CI, PR/integration branch.
5. Reconcile:
   - frozen source controls theorem semantics;
   - `V3_COVERAGE_STATUS.md` controls counted coverage;
   - live branches/Actions control actual code and CI;
   - Issue #56 controls current construction intent/blocker/next action;
   - prior chat is supplemental only.
6. Return a compact Recovery Snapshot and immediately continue the exact next action.
7. Never ask the user to restate the previous chat unless recovery is genuinely impossible.

Expected snapshot:

```text
Recovery complete.
main: <sha>
coverage: <N>/106
active P-ID: <pid>
feature: <branch>@<sha>
latest CI: <run> <status>
state: proof | integration | promotion | audit
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
5. After checkpointing, continue useful work in the current chat if room remains. Do not stop merely because a handoff was created.

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

## D. If the conversation ends unexpectedly

Recovery uses the following redundancy:

1. active feature branch WIP commits — authoritative unfinished code state;
2. Issue #56 — current intent/blocker/next action;
3. live GitHub CI/PR state;
4. prior-chat recovery — emergency reasoning supplement.

Meaningful edits that exist only in an ephemeral uncommitted working tree cannot be guaranteed recoverable. Therefore the unpersisted-work window must be kept small through frequent WIP checkpoint commits.

## E. User-facing rule

In normal use the user only needs to remember:

**Start:**

```text
继续 UEOT Core 3 Lean 全形式化。执行仓库 Recovery Protocol，恢复上一轮施工现场并直接继续，不要让我重复说明。
```

**Before switching chats:**

```text
执行 UEOT Core 3 跨对话交接，然后继续做到当前聊天不能继续为止。
```

Everything else is the AI's responsibility.
