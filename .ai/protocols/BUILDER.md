# Builder Protocol

The Builder may modify the existing task branch. It is not the final reviewer.

## Start

Follow `.ai/SYSTEM.md`. Reconcile Issue, PR head/diff, task state, required checks, prior
structured reviews, and PR comments. Confirm one work item -> one active branch/PR.

Before mutation, derive the incoming event key. If `STATE.json.last_event.key` already
matches it, or a PR review artifact already consumes it, stop without repeating work.

## One bounded iteration

1. Select only the recorded next action or the smallest prerequisite needed to execute it.
2. Inspect the actual failing check/review evidence; do not repair from summaries alone.
3. Implement one coherent change on the existing branch.
4. Run available static/local checks where supported.
5. Update `STATE.json` in the same implementation checkpoint:
   - increment `iteration` once;
   - record the last observed head in `checkpoint_sha`;
   - copy the consumed event into `last_event`;
   - compactly update completed/current_problem/next_action and retry counters;
   - set `WAITING_CI` for a pushed implementation.
6. Commit/push. Update the durable Issue live state when branch/head/blocker/next action changed.
7. Exit. Do **not** emit a separate consumed-only PR comment; the state checkpoint is the
   Builder's durable consumption record and avoids an unnecessary Work wake-up.

## Routing

- CI/check failure -> inspect logs, fingerprint root failure, one repair iteration.
- structured `CHANGES_REQUESTED` -> address the concrete findings in one iteration.
- blocked/missing check -> repair CI/config if in scope; otherwise record precise BLOCKED state.
- green CI with no requested changes -> Builder no-ops; Reviewer owns that transition.

## Prohibitions

- no direct `main` writes or force-pushes;
- no new branch because a conversation changed;
- no claim that a required check passed without current-SHA evidence;
- no full logs/diffs/secrets/reasoning traces in state;
- no self-approval or auto-merge.
