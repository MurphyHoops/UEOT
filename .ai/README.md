# UEOT Persistent Agent Runtime

This directory is the recovery layer for long-running AI development. A Work run, browser
session, or chat may disappear; the durable work item must remain recoverable from GitHub.

It does **not** replace repository governance. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`
controls: Issue = durable objective/live state, branch = temporary implementation surface,
PR = integration candidate, `main` = integrated truth.

## Truth order

When sources disagree:

1. current GitHub facts: source, refs, PR diff, checks/CI and reviews;
2. durable GitHub Issue body/live state;
3. `.ai/tasks/<task>/STATE.json` machine mirror;
4. project/architecture documents;
5. conversation memory or chat summaries.

Never overwrite a higher-ranked fact with stale lower-ranked context.

## Runtime model

A ChatGPT/Work conversation is a disposable worker. Persistent identity lives in policy,
durable GitHub state, environment evidence and transition rules.

Each invocation is bounded:

`LOAD -> RECONCILE -> ACT/REVIEW -> PERSIST -> HANDOFF -> EXIT`

Waiting for future CI is not a reason to keep a chat alive.

## Layout

- `SYSTEM.md` — startup/recovery invariants.
- `protocols/BUILDER.md` — code-producing worker protocol.
- `protocols/REVIEWER.md` — independent review protocol.
- `protocols/EVENTS.md` — signal/review/consumption protocol.
- `OPERATIONS.md` — recovery, rollback, BLOCKED and merge operations.
- `WORK_SETUP.md` — ChatGPT Work event-trigger setup.
- `QUICKSTART.md` — normal user workflow.
- `schema/task-state.schema.json` — machine contract.
- `tasks/issue-*/STATE.json` — code-checkpoint recovery mirror.
- `tasks/issue-*/GOAL.md` — durable success criteria.

Large logs, diffs and reasoning traces belong in GitHub/CI, not state files.
