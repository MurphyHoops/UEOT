# Independent Reviewer Protocol

The Reviewer is a fresh/independent worker. It does not modify implementation source during the review.

## Evidence order

1. durable Issue + `GOAL.md` / frozen success criteria;
2. current PR base/head and complete diff;
3. **base-anchored** trust policy and protected CI evidence;
4. changed source plus affected callers/tests/specification;
5. prior Builder state only as navigation, never as proof.

## Trust root

Before using a structured review or CI result for authorization, fetch `.ai/TRUST_POLICY.json` from the PR **base SHA**, never candidate HEAD.

- The actual GitHub author of a structured review artifact must be listed in the base-policy reviewer allowlist.
- Candidate changes to the trust policy do not apply to the PR that proposes them; they become effective only after merge.
- Mandatory CI is derived from base-policy path rules and actual changed files. Candidate `STATE.required_checks` cannot reduce that set.
- Protected gate identity is workflow path + job name under the base policy, with the protected workflow and declared runner inputs required to match base blobs.

If the base has no trust policy, this is the initial bootstrap. The Reviewer may still provide an independent technical conclusion, but any PASS is **advisory only**; it cannot authorize merge. Bootstrap merge is human-only.

## Output

Publish one top-level structured PR comment.

### PASS

```text
[UEOT-AI-REVIEW]
event_key: review:<sha>:pass
reviewed_sha: <sha>
reviewed_by: <actual-github-login>
trust_policy_sha: <base-sha-or-bootstrap>
trust_mode: base-policy|bootstrap-advisory
result: PASS
findings: none
```

For `trust_mode: base-policy`, PASS requires current-head protected CI green, success criteria met, coherent diff, no material unresolved finding, trusted GitHub-author provenance, and Reviewer independence.

For `trust_mode: bootstrap-advisory`, PASS is evidence for the human bootstrap decision only and must not be treated as an authoritative merge token.

### CHANGES_REQUESTED

```text
[UEOT-AI-REVIEW]
event_key: review:<sha>:changes-requested
reviewed_sha: <sha>
reviewed_by: <actual-github-login>
trust_policy_sha: <base-sha-or-bootstrap>
trust_mode: base-policy|bootstrap-advisory
result: CHANGES_REQUESTED
```

Follow with concrete findings naming file/symbol/evidence and expected property. A fresh `/ueot-resume` routes current-head findings to Builder. During bootstrap, material findings remain blocking for the human even though authorization is human-only.

## Independence rules

- never repair implementation source and then approve that same repair;
- re-read current head after every new commit;
- do not trust Builder summaries, `completed` arrays or PR prose as correctness evidence;
- trusted identity does not prove Reviewer independence;
- final merge remains human-gated.
