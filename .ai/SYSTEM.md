# Persistent Agent System Protocol v3

## Purpose

Keep UEOT development resumable across ordinary ChatGPT conversation limits while allowing repository development AI to execute the complete lifecycle, including merging reviewed work into `main`.

## Mandatory startup

Every Builder, Reviewer or resume invocation must:

1. read repository governance from integrated `main`;
2. recover durable task candidates from GitHub Issue -> PR -> `.ai/tasks/*/STATE.json`;
3. reconcile current `main`, PR `base_sha + head_sha`, complete diff/source, checks and structured reviews;
4. fetch `.ai/TRUST_POLICY.json` from the PR **base SHA** (or integrated `main` when no PR exists), never candidate HEAD;
5. derive protected CI/elevated-review requirements from that base policy and actual changed paths;
6. authenticate review/owner-authorization artifacts from GitHub metadata, not body text alone;
7. reject stale `(base_sha, head_sha)` evidence and duplicate transitions;
8. execute at most one coherent transition and persist the handoff.

## Owner-delegated authority

Repository owner `MurphyHoops` delegates full development authority to repository AI agents.

- merge mode: `ai-autonomous`;
- normal integration path: branch -> PR -> CI/elevated review -> independent Reviewer -> AI merge to `main`;
- Builder may never self-approve;
- direct writes to `main` are authorized only for recovery or explicitly justified maintenance when the normal PR path is unsuitable;
- force-push is not a normal recovery mechanism; prefer forward correction/revert commits.

Full authority does not mean bypassing evidence. The normal audited path remains mandatory unless an explicit direct-main exception is recorded.

## Bootstrap rule

If the PR base has no `.ai/TRUST_POLICY.json`, candidate policy cannot authorize itself. Bootstrap is permitted only when GitHub contains a `[UEOT-OWNER-AUTHORIZATION]` artifact authored by the repository owner delegating AI merge authority. The bootstrap candidate then still requires a fresh independent technical review of the exact `(base, head)` pair before AI merge.

## Trust-policy evolution

A candidate change to `.ai/TRUST_POLICY.json` is evaluated under the old/base policy and becomes effective only after merge.

Trust/runtime infrastructure changes use `elevated-review`, not ordinary protected-CI authorization. This preserves the external trust root while still allowing AI to evolve the runtime without a human merge gate.

## Protected CI semantics

- minimum normal gates come from base policy + actual changed paths, not candidate state;
- protected gate identity is workflow path + job name;
- protected workflow and declared runner-input blobs must match base for normal protected-CI authorization;
- if trust/runtime infrastructure or protected inputs change, route to `elevated-review` instead of pretending the old CI semantics still prove the candidate;
- Lean build-control inputs remain protected so the candidate cannot silently weaken what `lake build UEOT` means.

## Artifact identity

Currentness is the exact pair `(base_sha, head_sha)`.

- CI: `ci-settled:<base_sha>:<head_sha>:<aggregate>`;
- review: `review:<base_sha>:<head_sha>:<result>`;
- base movement invalidates old evidence even if head is unchanged;
- duplicate relay markers count only with trusted GitHub provenance.

## Merge transition

AI may merge a PR when all applicable conditions are satisfied:

1. current base/head pair still matches the reviewed pair;
2. no unresolved current-pair CHANGES_REQUESTED remains;
3. Reviewer independence is respected;
4. either protected CI is green for ordinary code, or elevated review explicitly covers the trust/runtime change;
5. the authoritative PASS artifact is from an allowed reviewer under base policy, or for initial bootstrap the repository-owner authorization artifact is present and the independent bootstrap review passes;
6. merge uses GitHub expected-head protection so a moved head cannot be merged accidentally.

## Continuation invariant

The runtime remains recoverable with Work, scheduled tasks and event-triggered Work disabled.

- Primary worker: ordinary ChatGPT Chat + GitHub connector.
- Primary continuation: fresh ordinary Chat + `/ueot-resume`.
- Optional acceleration: Work Event/Heartbeat.
- Optional coding escalation: Codex.

## Durable end states

`WAITING_CI`, `REVIEWING`, `CHANGES_REQUESTED`, `READY_TO_MERGE`, `BLOCKED`, or `DONE`.
