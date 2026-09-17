# Issue #100 — Persistent GitOps Agent Runtime v2

## Goal

Make long-running UEOT development survive ChatGPT Work run limits, conversation limits, missed GitHub event triggers, and bot-origin trigger gaps without requiring the user to reconstruct context.

A fresh worker must be able to recover the exact next action from GitHub: repository state, durable Issue, task state, PR, CI evidence and structured reviews.

## v2 liveness architecture

- Primary liveness: recurring ChatGPT Heartbeat scheduled task.
- Optional acceleration: supported GitHub PR event-triggered Work.
- Manual fallback: any fresh ChatGPT/Work conversation can recover from GitHub.
- Canonical state: GitHub repository/Issue/PR/CI, never a chat URL or webhook delivery.

## Success criteria

1. Repository truth/Issue/state hierarchy is explicit and compatible with branch governance.
2. Builder and Reviewer have separate bounded protocols.
3. Machine task state contains iteration, branch/SHA, event idempotency, retry brakes, CI summary and next action.
4. State is validated in GitHub Actions with no third-party Python dependency.
5. Event-trigger failure cannot strand an otherwise actionable task.
6. Heartbeat advances at most one actionable task per invocation and no-ops when nothing is actionable.
7. Current-head PASS + green CI reaches a human merge gate without a state-only commit loop.
8. This objective dogfoods fresh-chat recovery.

## Non-goals

- Removing ChatGPT product runtime or account usage limits.
- Keeping one conversation alive indefinitely.
- Replacing GitHub Issue governance.
- Autonomous merge to `main`.
- Storing chain-of-thought, full logs or diffs in task state.
