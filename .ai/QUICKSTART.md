# Persistent Agent v3 Quickstart

## Default path

`ordinary ChatGPT Chat + GitHub connector + GitHub Actions`

Continuation after any conversation ends:

`new ordinary Chat -> /ueot-resume`

Work/Event/Heartbeat/Codex are optional and disabled by default.

## Bootstrap

PR #102 is the initial trust-root installation. Because its base does not yet contain `.ai/TRUST_POLICY.json`, it is **bootstrap-human-only**: independent AI review and observed CI are evidence, but candidate-supplied policy cannot authorize its own merge. A human explicitly decides whether to merge and thereby establish the trust root.

After bootstrap, every later PR resolves `.ai/TRUST_POLICY.json` from its PR base SHA.

## Normal loop

1. ordinary Chat reconciles Issue/PR/base/head/diff/current CI;
2. it loads base trust policy and derives protected gates from actual changed paths;
3. Builder performs one bounded change and checkpoints state;
4. GitHub Actions runs;
5. later `/ueot-resume` verifies protected workflow/job evidence and review provenance;
6. current-head protected CI + authoritative independent PASS reaches the human merge gate.

Candidate `STATE.required_checks` cannot define or weaken the protected gate set. It is only a declaration mirror and must include the protected job names derived from base policy.

## Trust-policy changes

A PR may propose a new `.ai/TRUST_POLICY.json`, but that PR is still governed by the old policy from its base. The new policy takes effect only after merge. Changes to protected workflows or protected validator inputs degrade automated authorization to human-only.

## Canonical resume

`/ueot-resume`

Equivalent prompt:

> Recover the active UEOT task from GitHub. Read governance and candidate runtime docs, then load `.ai/TRUST_POLICY.json` from the PR base SHA. Reconcile current Issue/PR/base/head/diff/protected CI/review metadata/state, execute exactly one bounded next transition, persist the handoff, and stop. Do not rely on previous conversation history.
