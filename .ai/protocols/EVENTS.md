# Event and Wake-up Protocol

The runtime is event-driven, not conversation-driven. GitHub activity wakes a disposable
worker; repository state decides whether that worker is allowed to act.

## Canonical event key

Every actionable wake-up event has a stable idempotency key, for example:

- `ci-settled:<head-sha>:success`
- `ci-settled:<head-sha>:failure`
- `ci-settled:<head-sha>:blocked`
- `review:<review-id>:changes-requested`
- `review:<review-id>:pass`
- `human:<issue-or-comment-id>:resume`

A worker must reject an already-consumed event. Consumption evidence may be the task live
state plus the durable PR/Issue event record; do not repeat a mutation merely because a
new ChatGPT conversation received the same GitHub event.

## CI-settled signal

`UEOT AI Agent State Guard` is also the PR orchestrator. On every persistent-task PR update
that changes `.ai/` state it:

1. validates all task state and validator regression tests;
2. reads the task bound to the current PR/head;
3. only proceeds when that task is `WAITING_CI`;
4. waits for every check named in `required_checks` to appear and finish;
5. verifies the PR head SHA has not moved while waiting;
6. posts exactly one deduplicated `[UEOT-AI-SIGNAL]` PR comment.

This design intentionally does **not** hard-code the names of UEOT-QM, UEOT-GI, Lean, or
future CI workflows. A new task declares the job/check names it needs in `required_checks`.
The orchestrator can therefore wait for new CI workflows without being edited every time.

If a required check never appears or does not settle within the bounded wait window, the
orchestrator emits `aggregate: blocked` rather than silently pretending CI is green.

## Router

When a Work invocation wakes:

1. Locate the task whose `open_pr` equals the PR and whose `branch` equals its head branch.
2. Reconcile the current PR head, source, checks, Issue, and review state; never trust the
   wake-up comment as correctness evidence.
3. Reject stale SHAs and duplicate event keys.
4. Route by evidence:
   - `aggregate: failure` -> Builder repair;
   - `aggregate: blocked` -> Builder/configuration recovery or human decision;
   - `aggregate: success` + `WAITING_CI` -> independent Reviewer;
   - review changes requested -> Builder;
   - review pass + green required CI -> human merge gate.
5. Perform one bounded transition and stop. Do not wait in-chat for the next event.

## Race prevention

- One durable work item has one branch and one open PR.
- Branch-push duplicate state checks are avoided: feature branches validate through the PR;
  only `main` uses the push trigger.
- The signal job is SHA-pinned and exits if the PR head moves.
- Hidden PR-comment markers deduplicate CI-settled signals.
- The relay only has write permission to PR/Issue comments and never checks out or executes
  untrusted PR code in the signal job.
- Final merge is not event-driven; it remains a human gate.
