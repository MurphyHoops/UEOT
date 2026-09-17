# Issue #100 — Persistent GitOps Agent Runtime

## Goal

Make long-running UEOT development survive ChatGPT Work run limits and conversation
limits without requiring the user to manually reconstruct context.

A fresh worker must be able to recover the exact next action from GitHub: repository
state, Issue #100, task state, PR, and CI evidence.

## Phase-1 success criteria

1. Repository truth/Issue/state hierarchy is explicit and compatible with existing branch governance.
2. Builder and Reviewer have separate bounded protocols.
3. Machine task state contains iteration, branch/SHA, event idempotency, retry brakes, CI summary, and next action.
4. Task state is validated in GitHub Actions with no third-party Python dependency.
5. This task itself uses the mechanism (dogfooding).
6. Integration happens through one PR; final merge remains a human gate.

## Non-goals for Phase 1

- Removing ChatGPT product runtime limits.
- Keeping one conversation alive indefinitely.
- Replacing GitHub Issue governance.
- Autonomous merge to `main`.
- Storing chain-of-thought, full logs, or diffs in task state.
