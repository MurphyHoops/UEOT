# UEOT Persistent Agent Runtime v3

The runtime makes ChatGPT conversations disposable while GitHub carries durable development state.

## Execution model

1. **Primary worker:** ordinary ChatGPT Chat + GitHub connector.
2. **Deterministic verification:** GitHub Actions.
3. **Primary continuation:** fresh ordinary Chat + `/ueot-resume`.
4. **Integration authority:** AI-autonomous after required CI/elevated review and independent PASS.
5. **Optional automation:** Work Event/Heartbeat, disabled by default.
6. **Optional escalation:** Codex only when its value justifies agentic usage.

`/ueot-resume` is a repository protocol alias, not a built-in slash command.

## Truth order

1. current GitHub facts: source, refs, PR diff, checks/CI, comments and review metadata;
2. authorization trust root from `.ai/TRUST_POLICY.json` at the PR base SHA / integrated `main`;
3. repository-owner authorization artifacts in GitHub;
4. durable Issue live state;
5. `.ai/tasks/<task>/STATE.json` machine mirror;
6. project docs;
7. chat memory/summaries.

Candidate HEAD never defines the rules that authorize itself.

## Governance model

- repository owner delegates full development authority to AI;
- normal integration is reviewed PR -> AI merge to `main`;
- Builder cannot self-approve;
- direct-main writes are allowed only as explicit recovery/maintenance exceptions;
- trust/runtime changes use elevated independent review when old protected-CI semantics cannot safely validate the candidate;
- evidence binds the exact `(base_sha, head_sha)` pair;
- bootstrap requires owner authorization from GitHub plus independent bootstrap review.

## Layout

- `SYSTEM.md` — global runtime/governance invariants.
- `RESOURCE_POLICY.md` — Chat-first resource policy.
- `TRUST_POLICY.json` — integrated reviewer/CI/merge authority policy; consumers resolve it from PR base.
- `protocols/CHAT.md` — primary resume/execution protocol.
- `protocols/BUILDER.md` — code-producing worker.
- `protocols/REVIEWER.md` — independent review.
- `protocols/EVENTS.md` — optional Work event acceleration.
- `protocols/HEARTBEAT.md` — optional scheduled acceleration.
- `OPERATIONS.md` — rollback, elevated review, merge and direct-main exception operations.
- `WORK_SETUP.md` — optional Work configuration.
- `QUICKSTART.md` — normal user workflow.

Large logs, diffs, secrets and hidden reasoning traces never belong in task state.
