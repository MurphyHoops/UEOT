# Persistent Agent Operations

## Fresh-chat recovery

A new worker needs no prior conversation. Read, in order:

1. `docs/REPOSITORY_BRANCH_GOVERNANCE.md` on `main`;
2. `.ai/SYSTEM.md` and event/role protocol;
3. durable live-state Issue;
4. active PR current head/diff/checks/reviews/comments;
5. task `GOAL.md` and `STATE.json` mirror.

Reconcile discrepancies by the truth hierarchy before acting.

## BLOCKED

Use BLOCKED when a required external decision/resource is unavailable, retry budgets are
exhausted, a required check never materializes, or the same root failure repeats beyond the
guard. Record exact blocker, evidence, and next human action in the Issue. Do not spin.

## Rollback / bad checkpoint

Do not force-push history. On the same task branch:

1. identify the last known-good commit and exact bad change;
2. revert or make a corrective forward commit;
3. repair task state in that same checkpoint;
4. push and let current-head CI establish new evidence;
5. record the rollback/correction in the durable Issue.

If `STATE.json` itself is invalid, repair it on the same branch/PR; never create a rescue
branch solely because state validation failed.

## Human merge gate

Before merge verify:

- PR head still equals the SHA reviewed by the latest `[UEOT-AI-REVIEW] PASS` artifact, or
  any later changes are non-substantive and explicitly re-reviewed;
- required CI is green for the integration candidate;
- no unresolved structured CHANGES_REQUESTED finding exists;
- durable Issue and PR describe the same objective/branch;
- merge target is `main`.

The runtime never auto-merges v1.

## After merge

Validate resulting `main`, update/close the durable Issue, and retire the temporary branch
under repository governance. The merged PR/commits/CI/Issue become history; a branch is not
permanent memory.
