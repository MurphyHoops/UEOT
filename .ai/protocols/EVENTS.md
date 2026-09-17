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

`.github/workflows/ai-ci-signal.yml` acts as a narrow relay. It listens only to named
GitHub Actions workflows after pull-request-triggered runs complete. It does not check out
or execute PR code. It locates the task state bound to the PR, waits until every
`required_checks` name in that state has a completed check run, aggregates conclusions,
and posts one deduplicated structured PR comment:

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
   - CI success from `WAITING_CI` -> Reviewer path (`REVIEWING`).
   - Reviewer changes -> Builder (`CHANGES_REQUESTED`).
   - Reviewer pass + green required CI -> `READY_TO_MERGE`.
5. Checkpoint and end. Do not keep the worker alive waiting for the next event.

## Race prevention

- One durable work item has one branch and one open PR.
- The relay uses SHA-scoped concurrency and a hidden PR-comment marker to deduplicate.
- A task explicitly lists `required_checks`; an arbitrary first-finished workflow is never
  sufficient to declare CI settled.
- The relay only handles same-repository PR heads. Fork PRs are ignored.
- Final merge is never event-driven in v1; it remains a human gate.
