# Persistent Agent Operations

## Fresh-chat recovery

A new worker needs no prior conversation. Read governance, durable Issue, active PR/current base+head/diff/checks/reviews/comments, candidate runtime docs and task state. Resolve authorization from `.ai/TRUST_POLICY.json` at the PR **base SHA**, never candidate HEAD.

## Owner authority

GitHub owner authorization may delegate full repository development authority to AI. For this repository the intended mode is `ai-autonomous`.

The normal path is still PR-based because it preserves review/CI evidence. Direct `main` writes are allowed only for recovery or explicitly justified maintenance and must record why the normal PR path was unsuitable plus the rollback strategy.

## Trust-policy evolution

- Base policy governs the PR being reviewed.
- Candidate policy changes take effect only after merge.
- Base-policy `elevated_review_paths`, unmatched paths, changed protected workflows or changed protected runner inputs require independent elevated review rather than ordinary protected-CI authorization.
- Elevated review is an AI gate, not a human-only gate.

## Evidence currentness

A signal/review is current only when both artifact values match the PR now:

- `base_sha` / `reviewed_base_sha` == current `pr.base.sha`;
- `sha` / `reviewed_sha` == current `pr.head.sha`.

Any base movement invalidates earlier authorization evidence even if head is unchanged.

Duplicate signal markers count only when GitHub metadata proves trusted relay provenance. Copied marker text is ignored.

## BLOCKED

Use BLOCKED only when evidence/resources are genuinely unavailable, retry budgets are exhausted, repository permissions prevent a required transition, or the same root failure repeats beyond the guard. Trust/runtime changes normally route to elevated review rather than BLOCKED.

## Rollback / bad checkpoint

Prefer forward correction or revert commits. Do not force-push normal task history. Repair state in the same checkpoint, push, and let current-pair evidence establish the new truth.

## AI merge gate

For a normal post-bootstrap PR, the merging AI must verify:

- trust policy loaded from current PR base SHA;
- current `(base, head)` equals the independently reviewed pair;
- no unresolved current-pair CHANGES_REQUESTED exists;
- Reviewer independence was respected;
- ordinary code: all applicable base-policy protected gates are green;
- elevated-review code: Reviewer explicitly states that trust/runtime/build-control changes were examined and PASS applies despite ordinary protected-CI semantics being intentionally inapplicable;
- review author provenance is valid under base policy;
- target is `main` and Issue/PR objective/branch agree.

Merge with `expected_head_sha` equal to the reviewed current head. If GitHub rejects because head moved, stop and re-review; never merge a different head by inference.

## Bootstrap merge

When base policy is absent:

1. verify a `[UEOT-OWNER-AUTHORIZATION]` PR comment exists and GitHub metadata shows the repository owner authored it;
2. verify that artifact delegates `merge_mode: ai-autonomous` and keeps independent review required;
3. obtain a fresh independent bootstrap review of the exact current `(base, head)` pair;
4. if PASS and current CI/evidence is coherent, AI may merge the bootstrap PR with `expected_head_sha`.

Candidate policy alone never supplies bootstrap authority; the owner artifact does.

## Direct-main exception

AI is authorized to modify `main` directly only for recovery or explicitly justified maintenance. Before doing so it must record: objective, why PR flow is unsuitable, exact intended mutation, validation plan and rollback plan. Use a forward commit, never an unreviewed force rewrite.

## After merge

Validate resulting `main`, update/close the durable Issue, and retire the temporary branch. The merged policy governs later PRs. If post-merge validation fails, immediately create a corrective/revert path using the same audit rules.
