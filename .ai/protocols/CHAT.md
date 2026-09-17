# Chat-First Execution Protocol — Primary Path

Persistent Agent v3 uses an ordinary ChatGPT conversation with the GitHub connector as the default worker. GitHub is durable state; the conversation is disposable compute.

## Resume command

Canonical entry point: `/ueot-resume`

Equivalent: recover the active UEOT task from GitHub, reconcile current Issue/PR/base/head/CI/reviews/state, execute exactly one bounded next transition, persist the handoff, and stop.

## Startup

1. Read repository governance and candidate runtime docs.
2. Recover active work from durable Issue -> open PR -> `.ai/tasks/*/STATE.json`.
3. Reconcile current `main`, PR base/head SHA, complete relevant diff/source and GitHub Actions evidence.
4. Fetch `.ai/TRUST_POLICY.json` from the PR **base SHA**. Never use candidate HEAD as an authorization root.
5. If base policy is absent, mark this as bootstrap-human-only: structured review/CI artifacts may inform the human but cannot authorize the candidate.
6. Derive mandatory CI gates from base policy + actual changed paths. Treat candidate `required_checks` only as a declaration mirror that must include protected job names; it cannot weaken policy.
7. Authenticate structured review authors from GitHub metadata against the base-policy allowlist.
8. Select exactly one actionable transition.

## Route

- protected CI pending/running -> report `WAITING_CI`; do not poll indefinitely;
- protected CI failed -> one bounded Builder repair;
- trusted current-head `CHANGES_REQUESTED` under base policy -> one bounded Builder repair;
- protected CI green with no valid independent review -> one independent Reviewer pass;
- authoritative current-head PASS + protected CI green -> human merge gate;
- bootstrap-human-only, protected trust input changed, unmatched policy path, `BLOCKED`, `DONE`, merged/closed -> no autonomous authorization.

## Resource policy

Normal Chat + GitHub connector is the default execution path. Work, scheduled tasks, event triggers and Codex are optional escalation resources, not required for correctness or recovery.
