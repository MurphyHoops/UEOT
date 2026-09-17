# Independent Reviewer Protocol

The Reviewer is a fresh/independent worker. It does not modify implementation source during the review.

## Evidence order

1. durable Issue + frozen success criteria;
2. current PR **base SHA + head SHA** and complete diff;
3. base-anchored trust policy, GitHub platform enforcement, and protected CI evidence;
4. changed source plus affected callers/tests/specification;
5. prior Builder state only as navigation, never proof.

## Trust root

Fetch `.ai/TRUST_POLICY.json` from the PR **base SHA**, never candidate HEAD.

- actual GitHub review author must be allowlisted by the base policy;
- candidate trust-policy changes become effective only after merge;
- mandatory CI derives from base policy + actual changed paths;
- candidate `STATE.required_checks` cannot reduce protected gates;
- protected gate identity is workflow path + job name, with protected workflow/runner inputs matching base;
- candidate changes matching `ci.human_only_paths` are human-only;
- required GitHub branch/ruleset controls must be verified before authoritative post-bootstrap PASS can reach a merge gate.

If base policy is absent, this is initial bootstrap. Technical PASS is advisory only and cannot authorize merge.

## Currentness

Review identity is the exact `(base_sha, head_sha)` pair. Re-read both immediately before publishing. A base movement invalidates an earlier review even when the head SHA is unchanged.

## Output

Publish one top-level structured PR comment.

### PASS

```text
[UEOT-AI-REVIEW]
event_key: review:<base_sha>:<head_sha>:pass
reviewed_base_sha: <base_sha>
reviewed_sha: <head_sha>
reviewed_by: <actual-github-login>
trust_policy_sha: <base-sha-or-bootstrap>
trust_mode: base-policy|bootstrap-advisory
result: PASS
findings: none
```

For `trust_mode: base-policy`, PASS requires current-pair protected CI green, verified required platform controls, success criteria met, coherent diff, no material unresolved finding, trusted GitHub-author provenance, and Reviewer independence.

For `trust_mode: bootstrap-advisory`, PASS is evidence for the human bootstrap decision only.

### CHANGES_REQUESTED

```text
[UEOT-AI-REVIEW]
event_key: review:<base_sha>:<head_sha>:changes-requested
reviewed_base_sha: <base_sha>
reviewed_sha: <head_sha>
reviewed_by: <actual-github-login>
trust_policy_sha: <base-sha-or-bootstrap>
trust_mode: base-policy|bootstrap-advisory
result: CHANGES_REQUESTED
```

Follow with concrete file/symbol/evidence findings and the expected property. During bootstrap, material findings remain blocking for the human.

## Artifact validation

A consumer must verify:

- `reviewed_base_sha == current PR base SHA`;
- `reviewed_sha == current PR head SHA`;
- actual GitHub author is allowlisted by base policy for normal mode;
- `reviewed_by` matches actual author;
- marker/body text alone is never provenance.

## Independence rules

- never repair implementation and approve that same repair;
- re-read current base/head after every new commit or base movement;
- do not trust Builder summaries, `completed`, PR prose, or stale artifacts as correctness evidence;
- trusted identity does not prove Reviewer independence;
- final merge remains human-gated.
