# UEOT Persistent Agent Runtime v2

The runtime makes ChatGPT/Work invocations disposable while keeping development state durable in GitHub.

## v2 liveness model

GitHub is the canonical state substrate. Liveness is provided by two independent wake-up paths:

1. **Heartbeat (primary / reliable fallback):** a recurring ChatGPT scheduled task inspects GitHub at most once per hour and advances at most one actionable task.
2. **GitHub Event Trigger (optional accelerator):** supported PR activity may wake Work earlier, but the runtime never depends on event delivery for correctness or eventual recovery.

A missed event therefore increases latency; it does not kill the agent.

## Truth order

1. current GitHub facts: source, refs, PR diff, checks/CI and reviews;
2. durable GitHub Issue body/live state;
3. `.ai/tasks/<task>/STATE.json` machine mirror;
4. project/architecture documents;
5. conversation memory or chat summaries.

## Runtime identity

`Persistent Agent = policy + GitHub state + verification + transition protocol + liveness`

A chat is only one compute instance. Each invocation performs one bounded transaction and exits.

## Layout

- `SYSTEM.md` — global invariants.
- `protocols/BUILDER.md` — code-producing worker.
- `protocols/REVIEWER.md` — independent review.
- `protocols/EVENTS.md` — best-effort event acceleration.
- `protocols/HEARTBEAT.md` — primary liveness/recovery loop.
- `WORK_SETUP.md` — ChatGPT Work/Scheduled configuration.
- `OPERATIONS.md` — rollback, BLOCKED and merge operations.
- `QUICKSTART.md` — user workflow.
- `tasks/issue-*/STATE.json` — compact code-checkpoint state.

Large logs, diffs, secrets and reasoning traces never belong in task state.
