# Issue #100 — Persistent GitOps Agent Runtime v3

## Goal

Make long-running UEOT development survive ordinary ChatGPT conversation limits without requiring the user to reconstruct context, while minimizing reliance on agentic Work/Codex resources.

A fresh ordinary Chat must recover the exact next action from GitHub alone while authorization is anchored outside the candidate being reviewed.

## v3 architecture

- Primary execution: ordinary ChatGPT Chat + GitHub connector.
- Deterministic execution/verification: GitHub Actions.
- Primary continuation: fresh ordinary Chat + `/ueot-resume`.
- Authorization: trust policy from PR base / integrated main, never candidate HEAD.
- Optional automation: Work Event Trigger / scheduled Heartbeat, disabled by default.
- Optional escalation: Codex only when justified.

## Success criteria

1. Repository truth/Issue/state hierarchy is explicit and compatible with branch governance.
2. Builder and Reviewer have separate bounded protocols.
3. State is machine-validated with bounded retry/loop guards.
4. Disabling Work/Event/Heartbeat/Codex does not make an active task unrecoverable.
5. A fresh ordinary Chat can reconstruct the task and execute exactly one correct bounded next transition from GitHub alone.
6. Reviewer authorization and mandatory CI are resolved from PR base / integrated trust policy, not candidate HEAD/state.
7. Trust-critical runtime/policy/validator/privileged-workflow changes fail closed to human-only under the previous/base policy.
8. Protected CI gate identity binds workflow path + job and protected build-control inputs; Lean build semantics cannot be silently weakened by changing root imports/toolchain/Lake control files while retaining an automated green gate.
9. Structured signal/review identity binds the exact `(base_sha, head_sha)` pair; base movement invalidates old evidence, and arbitrary commenter markers cannot suppress trusted relay output.
10. Before runtime activation, GitHub platform enforcement on `main` provides the external PR-only/no-force-push/no-automation-bypass boundary required by policy; missing/unverifiable enforcement fails closed to human-only.
11. Current-pair PASS + protected CI reaches a human merge gate without state-only commit loops.
12. Initial trust-root installation is explicit human bootstrap; candidate policy cannot authorize itself.

## Non-goals

- Removing ChatGPT product limits.
- Keeping one conversation alive indefinitely.
- Guaranteeing unattended autonomous progress in baseline configuration.
- Replacing GitHub platform branch/ruleset enforcement with repository prose.
- Autonomous merge to `main`.
- Cryptographically proving fresh ChatGPT worker identity when the same GitHub user acts through multiple sessions.
- Storing chain-of-thought, full logs or large diffs in task state.
