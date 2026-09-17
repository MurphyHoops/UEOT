# UEOT Persistent Agent Runtime v3

The runtime makes ChatGPT conversations disposable while keeping development state durable in GitHub.

## v3 execution model

GitHub is the canonical state substrate. The default worker is an ordinary ChatGPT conversation with the GitHub connector.

1. **Primary execution:** normal ChatGPT Chat + GitHub connector.
2. **Deterministic execution/verification:** GitHub Actions.
3. **Primary continuation:** user opens any fresh ordinary Chat and invokes `/ueot-resume`.
4. **Optional automation:** Work, scheduled Heartbeat and GitHub Event Trigger are disabled by default and may be enabled only as deliberate agentic-cost accelerators.
5. **Optional escalation:** Codex is reserved for tasks whose interactive coding value justifies its resource use.

v3 optimizes for resumability and resource efficiency, not unattended autonomy.

`/ueot-resume` is a repository protocol alias, not a built-in ChatGPT slash command. Typing it means: load `.ai/protocols/CHAT.md` and execute its recovery procedure.

## Truth order

1. current GitHub facts: source, refs, PR diff, checks/CI and reviews;
2. durable GitHub Issue body/live state;
3. `.ai/tasks/<task>/STATE.json` machine mirror;
4. project/architecture documents;
5. conversation memory or chat summaries.

## Review artifact trust

Structured `[UEOT-AI-REVIEW]` text is not self-authenticating. A PASS/CHANGES_REQUESTED artifact is authoritative only when GitHub API metadata shows that its actual author login is listed in `.ai/TRUSTED_REVIEWERS.json`. A body field claiming a reviewer identity is informational only.

Trusted identity is necessary but does not prove role independence. The fresh/independent Reviewer rule remains a separate process invariant and final merge remains human-gated.

## Runtime identity

`Persistent Agent = policy + GitHub state + verification + transition protocol`

A chat is only one compute instance. Each invocation performs one bounded transaction and exits.

## Layout

- `SYSTEM.md` — global invariants.
- `RESOURCE_POLICY.md` — default Chat-first resource policy.
- `TRUSTED_REVIEWERS.json` — allowlist for authoritative structured review artifacts.
- `protocols/CHAT.md` — primary resume/execution protocol.
- `protocols/BUILDER.md` — code-producing worker.
- `protocols/REVIEWER.md` — independent review.
- `protocols/EVENTS.md` — optional Work event acceleration.
- `protocols/HEARTBEAT.md` — optional scheduled Work acceleration.
- `WORK_SETUP.md` — optional Work configuration only.
- `OPERATIONS.md` — rollback, BLOCKED and merge operations.
- `QUICKSTART.md` — normal user workflow.
- `tasks/issue-*/STATE.json` — compact recovery mirror.

Large logs, diffs, secrets and reasoning traces never belong in task state.
