# Builder Protocol

The Builder is allowed to modify the task branch. It is not the final reviewer.

## Start

Follow `.ai/SYSTEM.md` mandatory startup. Confirm that the branch in `STATE.json` is the
single active branch for the Issue and that no duplicate PR/branch represents the same
objective.

## One iteration

1. Reconcile `STATE.json` against Issue/branch/PR/CI reality.
2. If `last_event.key` equals the incoming event key, stop without repeating work.
3. Select only `next_action` (or the smallest prerequisite required to make it executable).
4. Inspect the minimum source/evidence required.
5. Implement a coherent change on the existing task branch.
6. Run available local/static checks when the environment supports them.
7. Update `STATE.json` in the same checkpoint as the implementation:
   - increment `iteration` once;
   - set `checkpoint_sha` to the last observed repository SHA from which this transition was derived;
   - record compact completed facts;
   - record current problem and exact next action;
   - update CI/event/retry metadata;
   - normally set `status` to `WAITING_CI` after a pushed implementation.
8. Commit and push. Update the Issue live-state section with branch/head/PR/CI/blocker/next action when those facts changed.
9. End the invocation instead of waiting indefinitely for CI.

## After CI wake-up

- Required checks all green -> set/route to `REVIEWING` and request independent Reviewer work.
- CI failed -> set `CI_FAILED`, inspect actual failing logs, fingerprint the root failure, then perform one repair iteration.
- CI cancelled/infrastructure-only failure -> do not edit source blindly; retry/recover infrastructure under the retry guards.

## Prohibitions

- No direct `main` edits or force-pushes.
- No duplicate branch because the chat changed.
- No claim that tests passed without CI/check evidence when CI is the required gate.
- No embedding logs, diffs, secrets, or reasoning traces in `STATE.json`.
- No self-approval. `READY_TO_MERGE` requires independent review evidence.
