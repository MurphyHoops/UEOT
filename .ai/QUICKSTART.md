# Persistent Agent v3 Quickstart

## Default path

`ordinary ChatGPT Chat + GitHub connector + GitHub Actions`

Continuation after a conversation ends:

`new ordinary Chat -> /ueot-resume`

Work/Event/Heartbeat/Codex are optional and disabled by default.

## Bootstrap

PR #102 is the initial trust-root installation. Because its base does not contain `.ai/TRUST_POLICY.json`, it is **bootstrap-human-only**: independent AI review and observed CI are evidence, but candidate policy cannot authorize its own merge.

Before declaring the runtime activated, configure GitHub platform protection on `main` so normal integration is PR-only, force pushes are disabled, and automation identities cannot bypass the direct-push boundary. If this cannot be verified, remain human-only.

## Normal loop

1. ordinary Chat reconciles Issue/PR/current `(base_sha, head_sha)`/diff/current CI;
2. load trust policy from PR base SHA;
3. verify required GitHub platform enforcement;
4. derive `human_only_paths` and protected gates from base policy + actual changed paths;
5. Builder performs one bounded change and checkpoints state;
6. GitHub Actions runs;
7. later `/ueot-resume` verifies protected workflow/job evidence and review provenance for the same `(base, head)` pair;
8. authoritative current-pair PASS + protected CI + platform enforcement reaches the human merge gate.

Candidate `STATE.required_checks` cannot define or weaken the protected gate set.

## Trust-policy / runtime changes

A PR may propose a new `.ai/TRUST_POLICY.json`, runtime protocol, validator, schema or privileged AI workflow, but base-policy `human_only_paths` makes trust-infrastructure changes human-only. New policy becomes authoritative only after merge.

## Evidence identity

A head SHA alone is insufficient. If the PR base moves while head stays unchanged, old CI/review artifacts are stale. Current artifacts bind both base and head.

## Canonical resume

`/ueot-resume`

Equivalent prompt:

> Recover the active UEOT task from GitHub. Load `.ai/TRUST_POLICY.json` from the current PR base SHA, verify GitHub platform enforcement, reconcile current Issue/PR/base/head/diff/protected CI/review metadata/state, execute exactly one bounded next transition, persist the handoff, and stop. Do not rely on previous conversation history.
