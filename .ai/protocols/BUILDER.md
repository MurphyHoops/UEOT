# Builder Protocol

The Builder may modify the existing task branch. It is not the final reviewer.

## Start

Follow `.ai/SYSTEM.md`. Reconcile Issue, PR base/head/diff, task state, prior reviews and current CI. Fetch `.ai/TRUST_POLICY.json` from the PR **base SHA** to determine protected reviewer/CI rules. Candidate state or policy never weakens that trust root.

Before mutation, reject stale/duplicate work and confirm one work item -> one active branch/PR.

## One bounded iteration

1. Select only the recorded next action or smallest prerequisite.
2. Inspect actual failing protected CI/review evidence, not summaries.
3. Implement one coherent change on the existing branch.
4. Update `STATE.json` in the same checkpoint: increment iteration, record last observed head/event, compactly update problem/next action/retries, set `WAITING_CI` for pushed implementation.
5. `required_checks` is a candidate declaration mirror: include all protected job names derived from base policy; it may not omit them. It does not itself define authorization.
6. Commit/push, update durable Issue when branch/head/blocker/next action changes, then exit.

## Routing

- protected CI failure -> one repair;
- authoritative current-head CHANGES_REQUESTED under base policy -> one repair;
- protected gate unavailable because policy path is unmatched or trust infrastructure changed -> record human-only/BLOCKED, do not invent a weaker gate;
- green protected CI -> Builder no-ops; Reviewer owns review transition;
- bootstrap PR with no base trust policy -> implementation may proceed, but no candidate artifact can authorize merge.

## Prohibitions

- no direct `main` writes or force-pushes;
- no replacement branch because a conversation changed;
- no candidate-defined reviewer/CI trust root;
- no claim of protected CI success without base-policy workflow/job evidence;
- no self-approval or auto-merge.
