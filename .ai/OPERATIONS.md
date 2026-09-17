# Persistent Agent Operations

## Fresh-chat recovery

A new worker needs no prior conversation. Read governance, candidate runtime docs, durable Issue, active PR/current base+head/diff/checks/reviews/comments, and task state. Resolve authorization from `.ai/TRUST_POLICY.json` at the PR **base SHA**, never candidate HEAD.

## Trust-policy evolution

- The base policy governs the PR being reviewed.
- A candidate change to `.ai/TRUST_POLICY.json` becomes effective only after merge.
- If base policy is absent, the PR is initial bootstrap and human-only.
- Candidate changes matching base-policy `human_only_paths` are human-only.
- Changed protected workflow/runner inputs are human-only.
- Unmatched changed paths are human-only.

## Platform activation gate

Repository protocol alone is not a security boundary. Before post-bootstrap runtime authorization is considered active, verify GitHub platform enforcement on `main`:

- integration is PR-only for normal development;
- force pushes are disabled;
- automation identities cannot directly push to `main` or bypass the protection used as the runtime's merge boundary;
- required checks/review controls are configured as appropriate to repository governance.

If these controls are missing or cannot be verified, record `BLOCKED`/human-only. Do not claim READY_TO_MERGE based only on repository text.

## Evidence currentness

A signal/review is current only when both recorded values equal the PR now:

- artifact `base_sha` / `reviewed_base_sha` == current `pr.base.sha`;
- artifact `sha` / `reviewed_sha` == current `pr.head.sha`.

Any base movement invalidates earlier authorization evidence even if head does not move.

Duplicate signal markers count only when actual GitHub metadata shows the trusted relay identity. Copied marker text from ordinary commenters is ignored for deduplication.

## BLOCKED

Use BLOCKED when a required external decision/resource is unavailable, retry budgets are exhausted, a protected gate cannot be established, platform enforcement cannot be verified, a trust-critical/unmatched path requires human review, or the same root failure repeats beyond the guard. Record exact blocker/evidence/next human action. Do not spin.

## Rollback / bad checkpoint

Do not force-push history. On the same task branch, identify the bad change, revert or make a corrective forward commit, repair state in that checkpoint, push, and let current-pair CI establish new evidence.

## Human merge gate

For a normal post-bootstrap PR, verify:

- trust policy loaded from current PR base SHA;
- required platform enforcement is active;
- latest authoritative PASS binds the current `(base, head)` pair and actual author is allowlisted by base policy;
- every mandatory base-policy CI gate applicable to changed paths is green;
- each gate came from base-approved workflow path/job and protected workflow/runner inputs match base;
- no changed path matches base-policy `human_only_paths` for an automated authorization attempt;
- candidate `required_checks` did not omit protected jobs;
- no unresolved authoritative current-pair CHANGES_REQUESTED exists;
- Issue/PR objective and branch agree;
- target is `main`;
- Reviewer independence was respected.

For initial bootstrap, no candidate PASS or CI policy can authorize merge. The human explicitly inspects candidate, independent review, observed CI, and platform protection before deciding whether to establish the trust root.

The runtime never auto-merges.

## After merge

Validate resulting `main`, verify platform protection is still active, update/close durable Issue, and retire the temporary branch. A merged trust-policy change governs only later PRs.
