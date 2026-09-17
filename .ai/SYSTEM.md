# Persistent Agent System Protocol

## Purpose

Make UEOT development resumable across short-lived ChatGPT Work runs and across new
conversations. A worker may disappear; the work item must remain recoverable.

## Mandatory startup

Every Builder or Reviewer invocation must, before making changes:

1. Read `docs/REPOSITORY_BRANCH_GOVERNANCE.md` from current `main`.
2. Read this file and the role protocol under `.ai/protocols/`.
3. Identify the durable GitHub Issue for the work item.
4. Read the Issue body, task `GOAL.md`, and task `STATE.json`.
5. Fetch/reconcile current `main`, active branch, open PR, head SHA, and relevant CI.
6. Run `python scripts/ai/validate_task_state.py` conceptually or actually when a shell is available.
7. Resolve stale state by the truth order in `.ai/README.md`; do not guess.

A new conversation must never ask the user to reconstruct branch or iteration state if
GitHub contains the evidence.

## Bounded transaction

One invocation should complete one coherent state transition, not an unbounded epic.
The default budget is one implementation/review iteration. `STATE.json.iteration` must
increase only when a substantive Builder iteration is checkpointed.

Before the run ends, leave one of these durable states:

- `WAITING_CI` — code/state pushed; environment must finish checks.
- `REVIEWING` — required CI is settled and independent review is next.
- `CHANGES_REQUESTED` — Reviewer found concrete defects; Builder is next.
- `READY_TO_MERGE` — review/CI gates are satisfied; human merge gate remains.
- `BLOCKED` — a named external decision/resource is required.
- `DONE` — objective is integrated/closed according to governance.

Do not keep a Work run alive merely to poll CI. Do not invent a second branch for a new
conversation.

## Safety brakes

- Never write directly to `main`; use the one branch bound to the durable work item.
- Never create per-iteration, handoff, scratch, `v2`, or `fresh` branches.
- `iteration <= max_iterations` always.
- The same failure fingerprint may be retried at most `max_same_failure` times before `BLOCKED`.
- Consecutive CI failures may not exceed `max_consecutive_ci_failures` without human review.
- `last_event.key` is an idempotency key. A worker that receives the same event again must not repeat the mutation.
- Builder may not declare its own work independently reviewed.
- Final merge to `main` is a human gate unless repository governance is explicitly changed.

## Checkpoint discipline

A checkpoint contains facts, not chain-of-thought: objective id, branch, base/checkpoint
SHA, iteration, current problem, completed milestones, next action, latest CI summary,
and event/retry guards. Detailed evidence remains in commits, PRs, CI runs, and Issues.

At handoff, update the durable Issue live-state section as needed. The Issue remains the
human-readable authority; `STATE.json` mirrors the minimum machine state needed to resume.
