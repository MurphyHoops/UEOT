# Persistent Agent Operations

## Fresh-chat recovery

A new worker needs no prior conversation. Read governance, candidate runtime docs, durable Issue, active PR/base/head/diff/checks/reviews/comments, and task state. Resolve authorization from `.ai/TRUST_POLICY.json` at the PR **base SHA**, never from candidate HEAD.

## Trust-policy evolution

- The base policy is the authority for the PR being reviewed.
- A candidate change to `.ai/TRUST_POLICY.json` becomes effective only after merge.
- If base policy is absent, the PR is the initial bootstrap and is human-only.
- If a protected workflow or protected runner input differs from base, automated CI authorization degrades to human-only.
- If changed paths are not classified by base policy, automated CI authorization degrades to human-only.

This prevents a candidate from changing who may review it or which minimum CI gates it must satisfy.

## BLOCKED

Use BLOCKED when a required external decision/resource is unavailable, retry budgets are exhausted, a protected gate cannot be established, a trust-policy path is unmatched, or the same root failure repeats beyond the guard. Record exact blocker/evidence/next human action. Do not spin.

## Rollback / bad checkpoint

Do not force-push history. On the same task branch, identify the bad change, revert or make a corrective forward commit, repair state in that checkpoint, push, and let current-head CI establish new evidence.

## Human merge gate

For a normal post-bootstrap PR, before merge verify:

- `.ai/TRUST_POLICY.json` was loaded from the PR base SHA;
- the latest authoritative PASS author is allowlisted by that base policy and `reviewed_sha` equals current head;
- every mandatory base-policy CI gate applicable to the changed paths is green;
- each gate came from the base-approved workflow path/job and protected workflow/runner inputs match base blobs;
- candidate `required_checks` did not omit any protected job;
- no unresolved authoritative CHANGES_REQUESTED exists;
- Issue/PR objective and branch agree;
- target is `main`;
- Reviewer independence was respected.

For the initial bootstrap where base policy is absent, no candidate-supplied PASS or CI policy can authorize the merge. The human must explicitly inspect the candidate, the independent review, and observed CI, then decide whether to establish this trust root by merging.

The runtime never auto-merges.

## After merge

Validate resulting `main`, update/close the durable Issue, and retire the temporary branch. A merged trust-policy change governs only later PRs.
