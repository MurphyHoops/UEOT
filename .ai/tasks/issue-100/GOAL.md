# Issue #100 — Persistent GitOps Agent Runtime v3

## Goal

Make long-running UEOT development survive ordinary ChatGPT conversation limits without requiring the user to reconstruct context, while minimizing reliance on agentic Work/Codex resources.

A fresh ordinary ChatGPT conversation must be able to recover the exact next action from GitHub: repository state, durable Issue, task state, PR, CI evidence and authenticated structured reviews.

## v3 architecture

- Primary execution: ordinary ChatGPT Chat + GitHub connector.
- Deterministic execution/verification: GitHub Actions.
- Primary continuation: fresh ordinary Chat + `/ueot-resume`.
- Optional automation: Work Event Trigger / scheduled Heartbeat, disabled by default.
- Optional escalation: Codex for tasks that justify extra agentic usage.
- Canonical state: GitHub repository/Issue/PR/CI, never a chat URL or webhook delivery.

## Success criteria

1. Repository truth/Issue/state hierarchy is explicit and compatible with branch governance.
2. Builder and Reviewer have separate bounded protocols.
3. Machine task state contains iteration, branch/SHA, idempotency, retry brakes, CI summary and next action.
4. State is validated in GitHub Actions with no third-party Python dependency.
5. Disabling all Work/Event/Heartbeat automation cannot make an active task unrecoverable.
6. A fresh ordinary Chat can recover the task and execute exactly one correct bounded next transition from GitHub alone.
7. Current-head PASS + green CI reaches a human merge gate without a state-only commit loop.
8. Structured review artifacts cannot satisfy routing or merge gates solely by spoofing marker text; authoritative review provenance must be authenticated from GitHub metadata against a repository allowlist.
9. Optional automation, when enabled, obeys the same truth, idempotency and bounded-transition rules.

## Non-goals

- Removing ChatGPT product limits.
- Keeping one conversation alive indefinitely.
- Guaranteeing unattended autonomous progress in the default configuration.
- Replacing GitHub Issue governance.
- Autonomous merge to `main`.
- Cryptographically proving that two fresh ChatGPT conversations are distinct workers when both act through the same trusted GitHub account; role independence remains a process invariant plus human merge gate.
- Storing chain-of-thought, full logs or diffs in task state.
