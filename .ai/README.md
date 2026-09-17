# UEOT Persistent Agent Runtime

This directory is the machine-readable recovery layer for long-running AI development.
It exists so a task can survive a short Work run, a dead browser session, or a brand-new
ChatGPT conversation without reconstructing state from chat history.

It does **not** replace repository governance. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`
remains controlling: Issue = durable objective/live state, branch = temporary work
surface, PR = integration candidate, `main` = integrated truth.

## Truth order

When sources disagree, use this order:

1. Current repository facts: source, refs, PR diff, commit/check/CI results.
2. The durable GitHub Issue body for the active work item.
3. `.ai/tasks/<task>/STATE.json` as the machine recovery mirror.
4. Project instructions and durable architecture documents.
5. Conversation memory or hand-written chat summaries.

Never overwrite a higher-ranked fact with stale lower-ranked context.

## Runtime model

A ChatGPT/Work conversation is a disposable worker. The persistent agent is the
combination of repository policy, durable task state, environment evidence, and a
transition protocol.

Each invocation performs one bounded transaction:

`LOAD -> RECONCILE -> ACT -> VERIFY/WAIT -> CHECKPOINT -> HANDOFF`

The worker must checkpoint before its run ends. Waiting for CI is not productive work:
commit/push a `WAITING_CI` checkpoint and allow an external GitHub event to wake the next
worker.

## Layout

- `SYSTEM.md` — global startup/recovery invariants.
- `protocols/BUILDER.md` — code-producing worker protocol.
- `protocols/REVIEWER.md` — independent review protocol.
- `schema/task-state.schema.json` — portable machine contract.
- `tasks/issue-*/STATE.json` — resumable machine state for durable objectives.
- `tasks/issue-*/GOAL.md` — stable objective/success criteria.

`STATE.json` is intentionally small. Large logs, diffs, source text, and reasoning traces
belong in GitHub/CI, not in the state file.
