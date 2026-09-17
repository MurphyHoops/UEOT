# Event and Wake-up Protocol

The runtime is event-driven, not conversation-driven. GitHub activity wakes a disposable
worker; repository state decides whether that worker is allowed to act.

## Canonical event key

Every actionable wake-up event has a stable idempotency key, for example:

- `ci-settled:<head-sha>:success`
- `ci-settled:<head-sha>:failure`
- `ci-settled:<head-sha>:blocked`
- `state-guard:<head-sha>:failure`
- `review:<review-id>:changes-requested`
- `review:<review-id>:pass`
- `human:<issue-or-comment-id>:resume`

A worker must reject an already-consumed event. Never repeat a mutation merely because a
new ChatGPT conversation received the same GitHub event.

## Two-stage CI orchestration

The runtime deliberately separates untrusted PR validation from trusted signal emission.

### Stage A — `UEOT AI Agent State Guard`

Runs on the PR head with read-only repository permission. It validates all task state,
runs validator regression tests, and verifies the JSON schema. Feature branches validate
through the PR only; `main` additionally validates on push, avoiding duplicate same-SHA
branch/PR checks.

### Stage B — `UEOT AI CI Signal`

Runs from the default-branch workflow via GitHub `workflow_run` after Stage A completes.
Because it does not checkout or execute PR code, it can safely hold the narrow write
permission needed to post a PR wake-up comment. It then:

1. rejects stale PR head SHAs;
2. reads the task bound to the PR;
3. only continues for `WAITING_CI`;
4. waits for every task-declared `required_checks` check name to settle;
5. posts one deduplicated `[UEOT-AI-SIGNAL]` comment with `success`, `failure`, or `blocked`.

Only the fixed State Guard workflow name is wired into `workflow_run`. UEOT-QM, UEOT-GI,
Lean, and future validation workflows remain dynamic: tasks name their check jobs in
`required_checks`; the relay polls those checks without needing its trigger list changed.

If Stage A itself fails, the trusted relay emits a failure signal so an external worker can
repair invalid task state or validator regressions.

## Router

When a Work invocation wakes:

1. Locate/recover the task from PR, Issue and task state.
2. Reconcile current PR head, source, complete diff, checks and reviews; the wake-up comment
   is not correctness evidence.
3. Reject stale SHAs and duplicate event keys.
4. Route by evidence:
   - failure -> one Builder repair;
   - blocked -> gate/configuration recovery or precise human BLOCKED state;
   - success + `WAITING_CI` -> independent Reviewer;
   - review changes -> Builder;
   - review pass + green required CI -> human merge gate.
5. Persist the durable handoff and stop instead of waiting for the next event.

## Bootstrap boundary

`workflow_run` workflows must already exist on the default branch to activate. Therefore
the one-time bootstrap PR can validate Stage A but cannot prove Stage B end-to-end before
merge. After the reviewed bootstrap lands on `main`, run one disposable task to prove the
signal comment + ChatGPT Work wake-up path before relying on unattended continuation.

## Race/security guards

- one durable work item -> one branch -> one open PR;
- signal relay is SHA-pinned and exits if the PR head moves;
- hidden comment markers deduplicate signals;
- relay never checks out or executes PR code;
- same-repository PRs only;
- final merge remains a human gate.
