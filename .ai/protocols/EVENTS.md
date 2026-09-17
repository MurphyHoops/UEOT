# Event and Wake-up Protocol

The runtime is event-driven, not conversation-driven. GitHub activity wakes a disposable
worker; repository state decides whether that worker is allowed to act.

## Event keys and consumption

Actionable events use stable keys such as:

- `ci-settled:<head-sha>:success|failure|blocked`
- `state-guard:<head-sha>:failure`
- `review:<reviewed-sha>:pass|changes-requested`
- `human:<issue-or-comment-id>:resume`

CI emits a structured PR comment:

```text
[UEOT-AI-SIGNAL]
event_key: <key>
...
```

Consumption is recorded without creating an extra comment-only wake-up:

- **Builder:** the implementation checkpoint copies the incoming event key into
  `STATE.json.last_event.key`.
- **Reviewer:** the single structured review comment embeds the consumed CI key with
  `<!-- ueot-ai-consumed:<ci-event-key> -->`.

Before mutating anything, a worker checks both the task `last_event.key` and PR comments
for the consumed marker. Duplicate event delivery is therefore a no-op even when the
previous worker was a different chat.

## Two-stage CI orchestration

### Stage A — `UEOT AI Agent State Guard`

Runs on the PR head with read-only repository permission. It validates all task state,
runs validator regression tests, and verifies the JSON schema. Feature branches validate
through the PR only; `main` additionally validates on push.

### Stage B — `UEOT AI CI Signal`

Runs trusted default-branch code via `workflow_run` after Stage A. It never checks out or
executes PR code. It has only the narrow write scope needed to post a PR wake-up comment.
It rejects stale heads, reads the task bound to the PR, waits for every task-declared
`required_checks` name, and posts one deduplicated signal.

Only the State Guard workflow name is fixed. UEOT-QM, UEOT-GI, Lean and future validation
workflows remain dynamic through `required_checks`.

## Router

1. Recover task from PR -> durable Issue -> task state.
2. Reconcile current head SHA, complete diff/source, checks and prior structured reviews.
3. Reject stale SHA or an already-consumed event key.
4. Route:
   - CI failure -> one Builder repair;
   - CI blocked -> gate/configuration recovery or precise BLOCKED record;
   - CI success -> independent Reviewer;
   - structured `CHANGES_REQUESTED` review -> Builder;
   - structured PASS + green required CI -> human merge gate.
5. Persist the outcome using the role-specific consumption rule above, then exit.

## Review event

Reviewer output is one top-level PR comment, not a source/state commit. It consumes the
triggering CI signal in the same artifact.

PASS example:

```text
<!-- ueot-ai-consumed:ci-settled:<sha>:success -->
<!-- ueot-ai-review:review:<sha>:pass -->
[UEOT-AI-REVIEW]
event_key: review:<sha>:pass
consumes_event_key: ci-settled:<sha>:success
reviewed_sha: <sha>
result: PASS
findings: none
```

`CHANGES_REQUESTED` uses the same format with `result: CHANGES_REQUESTED` and concrete
findings. This avoids a state-only commit that invalidates the very head just reviewed.
It also works when the connected GitHub identity is the PR author and cannot submit a
native self-approval.

For no-code transitions (review pass, BLOCKED decision, human gate), the Issue/PR event
record is authoritative and the repository `STATE.json` mirror may lag until the next code
checkpoint. This follows repository governance: current Git/PR/Issue evidence ranks above
the state mirror.

## Work-trigger filtering

To avoid wasting Work invocations on bookkeeping comments, configure the external trigger
condition to start a worker only when a PR comment is either:

1. a `[UEOT-AI-SIGNAL]`, or
2. a `[UEOT-AI-REVIEW]` with `result: CHANGES_REQUESTED`.

A PASS review should not wake another worker; it simply exposes the human merge gate.

## Bootstrap boundary

`workflow_run` must exist on default branch. The bootstrap PR can prove State Guard CI but
cannot prove CI Signal end-to-end before merge. After bootstrap lands on `main`, use one
disposable task to verify signal comment -> Work invocation -> structured review/repair.

## Race/security guards

- one durable work item -> one branch -> one open PR;
- signal relay is SHA-pinned and exits when the head moves;
- signal/review/consumption markers are idempotent;
- trusted relay never executes PR code;
- same-repository PRs only;
- final merge remains a human gate.
