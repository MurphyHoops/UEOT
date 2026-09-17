# Chat-First Execution Protocol — Primary Path

Persistent Agent v3 uses an ordinary ChatGPT conversation with the GitHub connector as the default worker. GitHub is durable state; the conversation is disposable compute.

## Resume command

The canonical user entry point is:

`/ueot-resume`

Equivalent natural language:

> Recover the active UEOT task from GitHub, reconcile current Issue/PR/head/CI/reviews/state, execute exactly one bounded next transition, persist the handoff, and stop. Do not rely on previous conversation history.

## Startup

1. Read `docs/REPOSITORY_BRANCH_GOVERNANCE.md`, `.ai/README.md`, `.ai/SYSTEM.md`, and the selected role protocol.
2. Recover active work from durable Issue -> open PR -> `.ai/tasks/*/STATE.json`.
3. Reconcile current `main`, PR head SHA, complete relevant diff/source, required checks, CI and structured reviews.
4. Apply the repository truth order. Chat memory is navigation only.
5. Select exactly one actionable transition.

## Route

- required CI pending/running -> report `WAITING_CI`; do not poll indefinitely;
- required CI failed -> one bounded Builder repair;
- current-head `CHANGES_REQUESTED` -> one bounded Builder repair;
- green current-head CI without valid independent review -> one independent Reviewer pass;
- current-head PASS + green CI -> human merge gate; no mutation;
- `BLOCKED`, `DONE`, merged/closed or no actionable work -> no-op.

## Resource policy

Normal Chat + GitHub connector is the default execution path. Work, scheduled tasks, event triggers and Codex are optional escalation resources, not required for correctness or recovery.

The runtime optimizes for durable resumability rather than unattended autonomy.
