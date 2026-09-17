# Builder Protocol

The Builder may modify the existing task branch. It is not the final reviewer.

## Start

Follow `.ai/SYSTEM.md`. Reconcile Issue, current PR **base SHA + head SHA**, full diff, task state, prior reviews and current CI. Fetch `.ai/TRUST_POLICY.json` from the PR base SHA. Candidate state/policy never weakens that root.

Before mutation, reject stale/duplicate work and confirm one work item -> one active branch/PR.

## One bounded iteration

1. Select only the recorded next action or smallest prerequisite.
2. Inspect actual protected CI/review evidence, not summaries.
3. Implement one coherent change on the existing branch.
4. Update `STATE.json` in the same checkpoint: increment iteration, record compact problem/next action/retries, and set `WAITING_CI` for pushed implementation.
5. `required_checks` is only a declaration mirror: include all protected job names derived from base policy; never omit them.
6. Commit/push, update durable Issue when branch/head/blocker/next action changes, then exit.

## Routing

- protected CI failure for current `(base, head)` -> one repair;
- authoritative current-pair CHANGES_REQUESTED -> one repair;
- trust-critical path, changed protected input, unmatched path, or unverifiable platform enforcement -> record human-only/BLOCKED; never invent a weaker gate;
- green protected CI -> Builder no-ops; Reviewer owns review transition;
- bootstrap with no base trust policy -> implementation may proceed, but no candidate artifact can authorize merge.

## Currentness

Builder must not consume a review or CI artifact unless both the artifact base SHA and head SHA equal the current PR pair. If base moves while head stays constant, prior review/CI authorization evidence is stale.

## Prohibitions

- no direct `main` writes or force-pushes;
- no replacement branch because a conversation changed;
- no candidate-defined reviewer/CI trust root;
- no claim of protected CI success without base-policy workflow/job evidence;
- no attempt to bypass `human_only_paths` or missing platform protection;
- no self-approval or auto-merge.
