# Heartbeat Protocol — Primary Liveness

The Heartbeat is the v2 reliability mechanism. It is a recurring ChatGPT scheduled task, not a long-running process.

## Semantics

Each scheduled run is a new disposable worker. On eligible paid ChatGPT plans the schedule may be hourly; the worker inspects GitHub, performs at most one bounded transition, persists the handoff, and exits.

A missed GitHub event can delay work until the next Heartbeat but cannot strand the task.

## Scan

1. Read governance/System/Event protocol.
2. Find active durable Issues with open task PRs/state.
3. Reconcile actual PR head, checks, current source/diff, structured reviews and state.
4. Ignore merged/closed PRs, `DONE`, `READY_TO_MERGE`, unresolved `BLOCKED`, stale task records, or tasks with no actionable transition.
5. Select at most ONE task, prioritizing:
   - current failed required CI;
   - current `CHANGES_REQUESTED` review;
   - green current-head CI with no valid current-head independent review;
   - explicit newly-resolved BLOCKED/human-resume state.

## Route

- required CI running/pending -> no mutation; exit;
- required CI failed -> one Builder repair;
- structured CHANGES_REQUESTED for current head -> one Builder repair;
- required CI green and no current-head review -> one independent Reviewer pass;
- current-head PASS + green required CI -> human merge gate; no mutation;
- no actionable task -> quiet no-op.

## Cost and loop controls

- never poll repeatedly inside one run;
- never process more than one task per heartbeat;
- never create bookkeeping-only code commits;
- never repeat an event/transition already represented by current GitHub evidence;
- event accelerators may cause a Heartbeat to find nothing to do; that is a valid no-op.

## Failure model

Heartbeat failure is recoverable at the next scheduled run or by manual fresh-chat recovery. The Heartbeat must never be the sole repository truth source.
