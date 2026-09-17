# Persistent Agent System Protocol v2

## Purpose

Keep UEOT development resumable across Work runtime limits, chat limits, missed webhooks and event-trigger gaps.

## Mandatory startup

Every Builder, Reviewer, event worker or Heartbeat invocation must:

1. read `docs/REPOSITORY_BRANCH_GOVERNANCE.md` from current `main`;
2. read `.ai/README.md`, this file, and the selected role protocol;
3. recover durable task candidates from GitHub Issue -> PR -> `.ai/tasks/*/STATE.json`;
4. reconcile current `main`, PR head SHA, complete relevant diff/source, required checks and structured reviews;
5. resolve stale state by the repository truth order; never reconstruct from chat memory.

## Bounded transaction

One invocation may execute at most one coherent task transition. Never keep a Work run alive waiting for future CI.

Builder checkpoints increment `STATE.json.iteration` once per substantive implementation iteration. Reviewer PASS does not create a state-only code commit.

## Liveness invariant

The runtime must remain recoverable if all GitHub event triggers fail.

- Primary liveness: recurring Heartbeat (`protocols/HEARTBEAT.md`).
- Optional acceleration: GitHub event-triggered Work (`protocols/EVENTS.md`).
- Manual fallback: any fresh chat can recover from GitHub and execute one bounded transition.

No correctness rule may require a specific chat URL, webhook delivery, bot comment delivery, or previous Work instance.

## Safety brakes

- one durable work item -> one active branch -> one PR;
- never write directly to `main` and never force-push;
- never create a replacement branch because a chat changed;
- reject stale SHA and duplicate work;
- `iteration <= max_iterations`;
- same root failure and consecutive CI failures obey task retry limits;
- Builder cannot self-approve;
- final merge is human-only in v2;
- Heartbeat selects at most one actionable task per run.

## Durable end states

`WAITING_CI`, `REVIEWING`, `CHANGES_REQUESTED`, `READY_TO_MERGE`, `BLOCKED`, or `DONE`.

`READY_TO_MERGE`, `BLOCKED`, and `DONE` are no-op states for Heartbeat unless new GitHub evidence changes the situation.
