# Issue #100 — Persistent GitOps Agent Runtime v3

## Goal

Make long-running UEOT development survive ordinary ChatGPT conversation limits without requiring the user to reconstruct context, while minimizing reliance on agentic Work/Codex resources.

A fresh ordinary ChatGPT conversation must be able to recover the exact next action from GitHub: repository state, durable Issue, task state, PR base/head, protected CI evidence and authenticated structured reviews.

## v3 architecture

- Primary execution: ordinary ChatGPT Chat + GitHub connector.
- Deterministic execution/verification: GitHub Actions.
- Primary continuation: fresh ordinary Chat + `/ueot-resume`.
- Optional automation: Work Event Trigger / scheduled Heartbeat, disabled by default.
- Optional escalation: Codex only when justified.
- Authorization trust root: `.ai/TRUST_POLICY.json` from PR base / integrated main, never candidate HEAD.

## Success criteria

1. Repository truth/Issue/state hierarchy is explicit and compatible with branch governance.
2. Builder and Reviewer have separate bounded protocols.
3. Machine task state contains iteration, branch/SHA, idempotency, retry brakes, CI summary and next action.
4. State is validated in GitHub Actions with no third-party Python dependency.
5. Disabling all Work/Event/Heartbeat automation cannot make an active task unrecoverable.
6. A fresh ordinary Chat can recover the task and execute exactly one correct bounded next transition from GitHub alone.
7. Candidate HEAD cannot authorize its own structured review authors; reviewer authorization is resolved from PR base policy.
8. Candidate HEAD cannot weaken or impersonate minimum CI gates; mandatory gates derive from base policy + changed paths and bind to trusted workflow/job identity with protected base blobs.
9. Trust-policy changes are evaluated under the previous/base policy and become effective only after merge.
10. Missing base policy, unmatched changed paths, or changes to protected trust infrastructure degrade to explicit human-only handling rather than implicit success.
11. Current-head authoritative PASS + protected CI reaches a human merge gate without a state-only commit loop.
12. Optional automation, when enabled, obeys the same truth, trust, idempotency and bounded-transition rules.

## Bootstrap condition

PR #102 is the initial installation: its base does not contain `.ai/TRUST_POLICY.json`. Therefore its independent AI review and CI are advisory evidence; no candidate-supplied review/CI policy can authorize this PR. The bootstrap merge must be an explicit human decision that establishes the trust root for subsequent PRs.

## Non-goals

- Removing ChatGPT product limits.
- Keeping one conversation alive indefinitely.
- Guaranteeing unattended autonomous progress by default.
- Replacing GitHub Issue governance.
- Autonomous merge to `main`.
- Cryptographically proving ChatGPT-worker independence when both use the same trusted GitHub account; human merge remains the final process gate.
- Storing chain-of-thought, full logs or diffs in task state.
