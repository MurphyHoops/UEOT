# Chat-First Execution Protocol — Primary Path

Persistent Agent v3 uses an ordinary ChatGPT conversation with the GitHub connector as the default worker. GitHub is durable state; each conversation is disposable compute.

## Resume command

Canonical entry point: `/ueot-resume`

Equivalent: recover the active UEOT task from GitHub, reconcile current Issue/PR/base/head/CI/reviews/state, execute exactly one bounded next transition, persist the handoff, and stop.

## Startup

1. read repository governance and candidate runtime docs;
2. recover active work from durable Issue -> open PR -> `.ai/tasks/*/STATE.json`;
3. reconcile current `main`, PR base/head, complete relevant diff/source and GitHub Actions evidence;
4. fetch `.ai/TRUST_POLICY.json` from the PR base SHA; never use candidate HEAD as its own authorization root;
5. derive protected CI or elevated-review requirements from base policy + actual changed paths;
6. authenticate structured review and owner-authorization artifacts from GitHub metadata;
7. require current evidence to bind the exact `(base_sha, head_sha)` pair;
8. select exactly one actionable transition.

## Route

- protected CI pending/running -> report `WAITING_CI`; do not poll indefinitely;
- protected CI failed -> one bounded Builder repair;
- current-pair CHANGES_REQUESTED -> one bounded Builder repair;
- trust/runtime/unmatched/protected-input change -> independent elevated review;
- ordinary protected CI green without valid review -> independent protected-ci review;
- valid bootstrap owner authorization + no base policy -> independent bootstrap-owner-authorized review;
- authoritative current-pair PASS with applicable evidence -> merge-capable AI invocation may merge PR to `main` using the reviewed head SHA;
- merged/closed/DONE/no-action -> no-op or post-merge validation as appropriate.

## Merge authority

Repository owner delegates AI authority to complete integration. The normal merge transition is PR-based and evidence-gated. Direct-main writes are allowed only under the explicit recovery/maintenance exception in `.ai/OPERATIONS.md`.

## Resource policy

Normal Chat + GitHub connector is the default execution path. Work, scheduled tasks, event triggers and Codex are optional resources, not requirements for correctness or recovery.
