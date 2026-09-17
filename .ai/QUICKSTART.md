# Persistent Agent v3 Quickstart

## Default path

`ordinary ChatGPT Chat + GitHub connector + GitHub Actions`

After a conversation ends:

`new ordinary Chat -> /ueot-resume`

Work/Event/Heartbeat/Codex remain optional and disabled by default.

## Owner-delegated merge authority

Repository owner has delegated full development authority to AI.

Normal path:

`task branch -> PR -> protected CI or elevated review -> independent Reviewer PASS -> AI merge main`

Builder self-approval remains forbidden. Direct `main` writes are allowed only for recovery or explicitly justified maintenance.

## Bootstrap PR #102

Because PR #102 base does not contain `.ai/TRUST_POLICY.json`, candidate policy cannot authorize itself. Bootstrap authority comes from a GitHub `[UEOT-OWNER-AUTHORIZATION]` comment authored by the repository owner. A fresh independent bootstrap review of the exact current `(base_sha, head_sha)` pair is still required before AI merge.

## Normal loop

1. ordinary Chat reconciles Issue/PR/current `(base_sha, head_sha)`/diff/state;
2. load trust policy from PR base SHA;
3. derive protected gates and elevated-review requirements from base policy + actual changed paths;
4. Builder performs one bounded change and checkpoints state;
5. GitHub Actions runs;
6. `/ueot-resume` verifies CI/review evidence for the same pair;
7. independent PASS moves the task to merge eligibility;
8. AI merges with `expected_head_sha` equal to the reviewed head;
9. validate resulting `main` and close/update the durable task.

## Trust/runtime changes

Changes to trust policy, runtime protocols, validators/schema, privileged AI workflows or protected build-control inputs route to **elevated independent review**. They are not blocked merely because no human is present, but ordinary protected-CI success must not be misrepresented as proof when the candidate changes the proof machinery itself.

## Canonical resume

`/ueot-resume`

Equivalent prompt:

> Recover the active UEOT task from GitHub. Load `.ai/TRUST_POLICY.json` from the current PR base SHA, reconcile current Issue/PR/base/head/diff/CI/review metadata/state, execute exactly one bounded next transition, persist the handoff, and stop. If merge conditions are satisfied under the repository policy, AI is authorized to merge to `main`. Do not rely on previous conversation history.
