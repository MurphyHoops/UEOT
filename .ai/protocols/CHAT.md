# Chat-First Execution Protocol — Primary Path

Persistent Agent v3 uses an ordinary ChatGPT conversation with the GitHub connector as the default worker. GitHub is durable state; the conversation is disposable compute.

## Resume command

Canonical entry point: `/ueot-resume`

Equivalent: recover the active UEOT task from GitHub, reconcile Issue/PR/current `(base, head)`/CI/reviews/state, execute exactly one bounded next transition, persist the handoff, and stop.

## Startup

1. Read repository governance and candidate runtime docs for navigation.
2. Recover active work from durable Issue -> open PR -> `.ai/tasks/*/STATE.json`.
3. Reconcile current `main`, PR base SHA, head SHA, complete relevant diff/source and GitHub Actions evidence.
4. Fetch `.ai/TRUST_POLICY.json` from the PR **base SHA**. Never use candidate HEAD as the authorization root.
5. Verify base-policy platform requirements against GitHub branch protection/rulesets. Missing or unverifiable enforcement => human-only.
6. If base policy is absent, mark bootstrap-human-only.
7. Derive mandatory gates from base policy + actual changed paths. Candidate `required_checks` cannot weaken them.
8. If any changed path matches base-policy `human_only_paths`, do not grant automated authorization.
9. Verify protected workflow/job identity and protected runner-input blobs against base.
10. Authenticate structured review authors from GitHub metadata against the base-policy allowlist.
11. Accept a signal/review only when both artifact base SHA and head SHA equal the PR's current `(base, head)`.
12. Select exactly one actionable transition.

## Route

- protected CI pending/running -> `WAITING_CI`; do not poll indefinitely;
- protected CI failed -> one bounded Builder repair;
- authoritative current-pair `CHANGES_REQUESTED` -> one bounded Builder repair;
- protected CI green with no valid current-pair independent review -> one independent Reviewer pass;
- authoritative current-pair PASS + protected CI green + verified platform enforcement -> human merge gate;
- bootstrap-human-only, trust-critical change, changed protected input, unmatched path, unverified platform enforcement, `BLOCKED`, `DONE`, merged/closed -> no autonomous authorization.

## Stale and duplicate handling

The identity of evidence is `(base_sha, head_sha)`, not head SHA alone. If `main` advances or the PR base changes while the head stays the same, old CI signals and reviews are stale. Do not consume them.

Duplicate markers from ordinary commenters are not trusted relay provenance and cannot suppress a later trusted signal.

## Resource policy

Normal Chat + GitHub connector is the default execution path. Work, scheduled tasks, event triggers and Codex are optional escalation resources, not required for correctness or recovery.
