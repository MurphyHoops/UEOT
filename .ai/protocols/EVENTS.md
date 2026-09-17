# Event Protocol v3 — Optional Work Acceleration

GitHub event-triggered Work is optional. v3 does not depend on it for liveness, correctness or recovery.

## Product boundary

Supported GitHub PR activity may trigger Work, but trigger-side marker filtering and bot-origin wake-ups may be incomplete. Because Work also consumes agentic resources, the default v3 deployment leaves the event task paused.

## Structured artifacts

Trusted CI may emit:

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
reviewed_by: <actual-github-login>
result: PASS|CHANGES_REQUESTED
```

Review markers are durable evidence only after the actual GitHub author is authenticated against `.ai/TRUSTED_REVIEWERS.json`. Marker text from an untrusted author is ordinary commentary and must not route Builder or satisfy the merge gate.

## Optional event worker

If the user deliberately enables event-triggered Work:

1. re-read GitHub; never trust event text as correctness evidence;
2. authenticate structured review author metadata against `.ai/TRUSTED_REVIEWERS.json`;
3. reject stale SHA, duplicate or already-completed transitions;
4. perform at most one bounded Builder/Reviewer transition;
5. PASS, ordinary comments, untrusted markers, bookkeeping and no-action states are immediate no-op;
6. persist durable handoff and exit.

If no Work invocation occurs, a later ordinary Chat `/ueot-resume` derives the same transition directly from GitHub state.
