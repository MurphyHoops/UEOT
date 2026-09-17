# UEOT Persistent Agent Runtime v3

The runtime makes ChatGPT conversations disposable while keeping development state durable in GitHub.

## v3 execution model

1. **Primary execution:** ordinary ChatGPT Chat + GitHub connector.
2. **Deterministic execution/verification:** GitHub Actions.
3. **Primary continuation:** fresh ordinary Chat + `/ueot-resume`.
4. **Optional automation:** Work Event/Heartbeat, disabled by default.
5. **Optional escalation:** Codex only when its extra value justifies agentic usage.

v3 guarantees resumability, not unattended autonomy.

`/ueot-resume` is a repository protocol alias, not a built-in slash command.

## Truth order

1. current GitHub facts: source, refs, PR diff, checks/CI and review metadata;
2. **authorization trust root from `.ai/TRUST_POLICY.json` at the PR base SHA / integrated main**;
3. durable GitHub Issue body/live state;
4. `.ai/tasks/<task>/STATE.json` machine mirror;
5. project/architecture docs;
6. conversation memory or summaries.

Candidate HEAD may describe behavior, but it cannot define the authorization rules that approve itself.

## Trust model

- reviewer authorization is read from the PR base policy, not candidate content;
- protected CI requirements are derived from base policy + actual changed paths;
- candidate `STATE.required_checks` is only a declaration mirror and must include protected job names;
- a protected gate is bound to a base-approved workflow path + job name;
- protected workflow and runner-input blobs must match the base revision;
- trust-policy changes become effective only after merge;
- missing base policy means initial bootstrap and therefore human-only authorization.

This blocks both candidate-controlled reviewer allowlists and same-name / weakened CI gate attacks.

## Runtime identity

`Persistent Agent = policy + GitHub state + verification + transition protocol`

## Layout

- `SYSTEM.md` — global invariants and trust-root rules.
- `RESOURCE_POLICY.md` — Chat-first resource policy.
- `TRUST_POLICY.json` — integrated reviewer/CI authorization policy; consumers resolve it from PR base.
- `protocols/CHAT.md` — primary resume/execution protocol.
- `protocols/BUILDER.md` — code-producing worker.
- `protocols/REVIEWER.md` — independent review.
- `protocols/EVENTS.md` — optional Work event acceleration.
- `protocols/HEARTBEAT.md` — optional scheduled acceleration.
- `OPERATIONS.md` — rollback, BLOCKED, trust evolution and merge operations.
- `WORK_SETUP.md` — optional Work configuration.
- `QUICKSTART.md` — user workflow.

Large logs, diffs, secrets and reasoning traces never belong in task state.
