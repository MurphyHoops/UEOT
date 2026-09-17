# Event Protocol v2 — Optional Acceleration

GitHub event-triggered Work is an optimization, not the liveness foundation.

## Product-boundary assumption

Supported GitHub PR activity may trigger ChatGPT Work, but marker-text filtering may occur only after invocation and bot-generated activity may not reliably wake Work. Therefore event delivery is never required for eventual progress.

## Structured artifacts

Trusted CI may emit a PR artifact such as:

```text
[UEOT-AI-SIGNAL]
event_key: ci-settled:<sha>:<success|failure|blocked>
sha: <sha>
aggregate: <result>
```

Reviewer may emit:

```text
[UEOT-AI-REVIEW]
reviewed_sha: <sha>
result: PASS|CHANGES_REQUESTED
```

These are durable navigation/evidence artifacts. They are not the sole wake-up channel.

## Event worker

When Work is invoked from supported PR activity:

1. re-read GitHub; never trust event text as correctness evidence;
2. reject stale SHA or already-completed transition;
3. route success to Reviewer, failure/CHANGES_REQUESTED to Builder, blocked to gate diagnosis;
4. execute one bounded transition and exit;
5. PASS/bookkeeping/ordinary comments are no-op.

If no event invocation occurs, Heartbeat later derives the same transition directly from GitHub state.
