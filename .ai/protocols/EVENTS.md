# Event and Wake-up Protocol

The runtime is event-driven, not conversation-driven. GitHub activity wakes a disposable
worker; repository state decides whether that worker is allowed to act.

## Event keys and durable markers

Actionable events use stable keys such as:

- `ci-settled:<head-sha>:success|failure|blocked`
- `state-guard:<head-sha>:failure`
- `review:<reviewed-sha>:pass|changes-requested`
- `human:<issue-or-comment-id>:resume`

CI emits:

```text
[UEOT-AI-SIGNAL]
event_key: <key>
...
```

A Work invocation that successfully consumes an event records a top-level PR comment with:

```text
<!-- ueot-ai-consumed:<event-key> -->
[UEOT-AI-CONSUMED]
event_key: <event-key>
outcome: <short outcome>
```

Before mutating anything, a worker checks for that hidden consumed marker. Duplicate event
delivery therefore becomes a no-op even when the previous worker was a different chat.
Builder code checkpoints also copy the consumed event into `STATE.json.last_event`.

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
3. Reject stale SHA or an existing `ueot-ai-consumed:<event-key>` marker.
4. Route:
   - CI failure -> one Builder repair;
   - CI blocked -> gate/configuration recovery or precise BLOCKED record;
   - CI success -> independent Reviewer;
   - structured review changes -> Builder;
   - structured review pass + green required CI -> human merge gate.
5. Persist outcome and consumed marker, then exit.

## Review event

Reviewer output is a top-level PR comment, not a source/state commit:

```text
<!-- ueot-ai-review:review:<reviewed-sha>:pass -->
[UEOT-AI-REVIEW]
event_key: review:<reviewed-sha>:pass
reviewed_sha: <sha>
result: PASS
findings: none
```

or `result: CHANGES_REQUESTED` followed by concrete findings. This avoids a state-only
commit that would invalidate the very head just reviewed. It also works when the connected
GitHub identity is the PR author and therefore cannot submit a native self-approval.

For no-code transitions (review pass, BLOCKED decision, human gate), the Issue/PR event
record is authoritative and the repository `STATE.json` mirror is allowed to lag until the
next code checkpoint. This follows repository governance: Issue/PR/current Git reality rank
above the state mirror.

## Bootstrap boundary

`workflow_run` must exist on default branch. The bootstrap PR can prove State Guard CI but
cannot prove CI Signal end-to-end before merge. After bootstrap lands on `main`, use one
disposable task to verify signal comment -> Work invocation -> consumed/review marker.

## Race/security guards

- one durable work item -> one branch -> one open PR;
- signal relay is SHA-pinned and exits when the head moves;
- signal and consumed markers are idempotent;
- trusted relay never executes PR code;
- same-repository PRs only;
- final merge remains a human gate.
