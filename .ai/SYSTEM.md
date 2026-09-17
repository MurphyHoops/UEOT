# Persistent Agent System Protocol v3

## Purpose

Keep UEOT development resumable across ordinary ChatGPT conversation limits while minimizing dependence on agentic Work/Codex execution.

## Mandatory startup

Every Builder, Reviewer or resume invocation must:

1. read `docs/REPOSITORY_BRANCH_GOVERNANCE.md` from integrated `main`;
2. read candidate runtime docs only as behavior/navigation, never as authorization roots;
3. recover durable task candidates from GitHub Issue -> PR -> `.ai/tasks/*/STATE.json`;
4. reconcile current `main`, PR **base SHA + head SHA**, complete diff/source, current checks and structured reviews;
5. fetch `.ai/TRUST_POLICY.json` from the PR **base SHA** (or integrated `main` when no PR exists), never candidate HEAD;
6. verify the platform controls required by that base policy; if branch protection/ruleset enforcement cannot be verified, authorization is human-only;
7. derive protected CI gates from base policy + actual changed paths; candidate `STATE.required_checks` is only a declaration mirror and cannot weaken base-derived gates;
8. authenticate structured review artifacts using actual GitHub author metadata against the **base-policy** reviewer allowlist;
9. require every signal/review artifact used for routing or merge to bind the current `(base_sha, head_sha)` pair;
10. reject stale/duplicate evidence and resolve discrepancies by repository truth order, never chat memory.

## Bootstrap rule

If the PR base does not contain `.ai/TRUST_POLICY.json`, the candidate is installing the trust root and cannot authorize itself. AI review and candidate CI are advisory evidence only. Bootstrap merge is explicit human action.

A change to `.ai/TRUST_POLICY.json` is evaluated under the old policy from the PR base and becomes effective only after merge.

## Platform-enforcement rule

Repository protocol is not a substitute for GitHub enforcement. Before the runtime is considered activated, the base policy requires platform controls on `main` that enforce PR-only integration, disable force pushes, and prevent automation identities from bypassing direct-push restrictions. If those controls are missing or cannot be verified from GitHub, the runtime must fail closed to human-only and must not claim an authoritative automatic merge gate.

## Trust-critical surface

The base policy defines `ci.human_only_paths`. Any candidate change matching those paths is trust-infrastructure work and degrades automated authorization to human-only for that PR. This includes the trust policy, runtime authorization protocols, validators/schema, and privileged AI workflows.

## Protected CI semantics

- minimum gates come from base policy + actual changed paths, not candidate state;
- gate identity is base-approved workflow path + job name;
- protected workflow and declared runner-input blobs must match base;
- Lean build-control inputs (`UEOT.lean`, `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`) are protected so a candidate cannot silently change which proof graph/toolchain/dependencies the trusted build means;
- unmatched paths fail closed to human-only.

## Artifact identity

Currentness is a pair, not a head SHA alone.

- CI signal key: `ci-settled:<base_sha>:<head_sha>:<aggregate>`.
- Review key: `review:<base_sha>:<head_sha>:<result>`.
- Review artifacts must include both `reviewed_base_sha` and `reviewed_sha`.
- A base movement invalidates prior signals/reviews even if head SHA is unchanged.
- Duplicate suppression must trust the relay's actual GitHub provenance; arbitrary marker text from ordinary commenters cannot suppress a trusted relay signal.

## Bounded transaction

One invocation may execute at most one coherent task transition. Do not keep a conversation alive merely to wait for future CI. Reviewer PASS never creates a state-only commit.

## Continuation invariant

The runtime remains recoverable with Work, scheduled tasks and event-triggered Work disabled.

- Primary worker: ordinary ChatGPT Chat + GitHub connector.
- Primary continuation: fresh ordinary Chat + `/ueot-resume`.
- Optional acceleration: Work Event/Heartbeat.
- Optional coding escalation: Codex.

## Safety brakes

- one durable work item -> one active branch -> one PR;
- never write directly to `main` and never force-push;
- never create a replacement branch because a chat changed;
- reject stale `(base, head)` and duplicate work;
- retry budgets remain bounded;
- Builder cannot self-approve;
- final merge is human-only unless governance is explicitly changed;
- optional automation obeys the same one-transition bound.

## Durable end states

`WAITING_CI`, `REVIEWING`, `CHANGES_REQUESTED`, `READY_TO_MERGE`, `BLOCKED`, or `DONE`.
