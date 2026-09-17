# Event and Wake-up Protocol

The runtime is event-driven, not conversation-driven. GitHub activity wakes a disposable
worker; repository state decides whether that worker is allowed to act.

## Canonical event key

Every actionable wake-up event must have a stable idempotency key stored in
`STATE.json.last_event.key` after it is consumed.

Recommended forms:

- `ci-settled:<head-sha>:success`
- `ci-settled:<head-sha>:failure`
- `review:<review-id>:changes-requested`
- `review:<review-id>:pass`
- `human:<issue-or-comment-id>:resume`

If the incoming key equals `last_event.key`, the worker exits without mutating GitHub.

## CI-settled signal

`.github/workflows/ai-ci-signal.yml` is a narrow relay. It listens only to named GitHub
Actions workflows after pull-request-triggered runs complete. It does not check out or
execute PR code. It locates the task state bound to the PR and emits a signal only when:

1. the PR still points at the workflow run SHA (stale runs are ignored);
2. the task is currently `WAITING_CI` (state-only/review commits cannot create an echo loop);
3. every `required_checks` name has a completed current check run;
4. no signal marker already exists for the same SHA + aggregate result.

It then posts one structured PR comment:

```text
[UEOT-AI-SIGNAL]
event: ci-settled
event_key: ci-settled:<sha>:<success|failure>
task: issue-N
pr: N
sha: <sha>
aggregate: <success|failure>
```

An external ChatGPT Work GitHub-event trigger can watch PR comments and use this marker as
the wake-up source.

## Router

When a worker wakes:

1. Locate the task whose `open_pr` equals the PR number and whose `branch` equals PR head.
2. Reconcile current head SHA and CI instead of trusting the comment body.
3. Reject duplicate `event_key`.
4. Route by state/evidence:
   - CI failure -> Builder (`CI_FAILED` then one repair iteration).
   - CI success from `WAITING_CI` -> Reviewer path.
   - Reviewer changes -> Builder (`CHANGES_REQUESTED`).
   - Reviewer pass + green required CI -> `READY_TO_MERGE`.
5. Checkpoint and end. Do not keep the worker alive waiting for the next event.

Reviewer change requests should be submitted as an actual GitHub PR review or a
structured PR comment so the external Work trigger can wake a Builder without relying on
chat continuity.

## Race and loop prevention

- One durable work item has one branch and one open PR.
- The relay uses SHA-scoped concurrency and a hidden PR-comment marker to deduplicate.
- A task explicitly lists `required_checks`; an arbitrary first-finished workflow is never
  sufficient to declare CI settled.
- Only the newest check run for each required check name is used when reruns/duplicate
  contexts exist.
- If the PR head has advanced beyond the completed workflow SHA, the event is stale and is
  ignored.
- The relay acts only while state is `WAITING_CI`; `REVIEWING`, `CHANGES_REQUESTED`,
  `READY_TO_MERGE`, `BLOCKED`, and `DONE` do not emit another CI wake-up merely because a
  state-only commit ran validation.
- The relay only handles same-repository PR heads. Fork PRs are ignored.
- Final merge is never event-driven in v1; it remains a human gate.

## Bootstrap rule

GitHub resolves a `workflow_run` workflow from the repository default branch. Therefore a
new relay introduced by the same PR cannot fully exercise itself before that PR is merged
to `main`.

The first integration of this runtime is intentionally a bootstrap:

1. validate the branch/PR with the normal state guard;
2. independently review the relay source and permissions;
3. human-merge the bootstrap PR;
4. confirm the relay is visible on `main`;
5. enable the external ChatGPT Work GitHub-event subscription;
6. prove automatic wake-up on the next disposable test task/PR.

Never interpret "relay file exists on a feature branch" as "relay is already active".
