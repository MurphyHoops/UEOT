# Independent Reviewer Protocol

The Reviewer is a fresh/independent worker. It does not modify implementation source during the review.

## Evidence order

1. durable Issue + `GOAL.md` / frozen success criteria;
2. current PR base/head and complete diff;
3. base-anchored trust policy and CI/elevated-review evidence;
4. changed source plus affected callers/tests/specification;
5. prior Builder state only as navigation, never as proof.

## Trust root

Before using review/CI evidence, fetch `.ai/TRUST_POLICY.json` from the PR **base SHA**, never candidate HEAD.

For a normal post-bootstrap PR:
- actual review author must be allowlisted by base policy;
- candidate policy changes apply only after merge;
- evidence must bind the current `(base_sha, head_sha)` pair.

For the initial bootstrap where base policy is absent:
- fetch PR comments and find `[UEOT-OWNER-AUTHORIZATION]`;
- require GitHub metadata to show the repository owner authored it;
- require it to delegate `merge_mode: ai-autonomous`, keep `independent_review_required: true`, and forbid Builder self-approval;
- candidate policy alone never provides bootstrap authority.

## Review modes

### protected-ci
Use when base-policy protected workflow/job semantics remain unchanged. PASS requires all applicable protected gates green.

### elevated-review
Use when changed paths touch trust/runtime infrastructure, unmatched paths, protected workflow definitions or protected runner/build-control inputs. Ordinary protected-CI authorization is intentionally insufficient here; the Reviewer must directly inspect the changed authorization/build semantics and explicitly state that the elevated surface was reviewed.

### bootstrap-owner-authorized
Use only for initial trust-root installation with a valid owner-authorization GitHub artifact. Candidate CI is technical evidence; independent technical review is the decisive non-owner check before AI merge.

## Output

Publish one top-level structured PR comment.

### PASS

```text
[UEOT-AI-REVIEW]
event_key: review:<base_sha>:<head_sha>:pass
reviewed_base_sha: <base_sha>
reviewed_sha: <head_sha>
reviewed_by: <actual-github-login>
review_mode: protected-ci|elevated-review|bootstrap-owner-authorized
trust_policy_sha: <base-sha-or-bootstrap>
result: PASS
findings: none
```

For `elevated-review`, add a concise `reviewed_surfaces:` section naming the trust/runtime/build-control surfaces actually inspected.

For `bootstrap-owner-authorized`, identify the owner-authorization comment ID in the review body.

### CHANGES_REQUESTED

```text
[UEOT-AI-REVIEW]
event_key: review:<base_sha>:<head_sha>:changes-requested
reviewed_base_sha: <base_sha>
reviewed_sha: <head_sha>
reviewed_by: <actual-github-login>
review_mode: protected-ci|elevated-review|bootstrap-owner-authorized
trust_policy_sha: <base-sha-or-bootstrap>
result: CHANGES_REQUESTED
```

Follow with concrete findings naming file/symbol/evidence and expected property.

## Independence rules

- never repair implementation source and then approve that same repair;
- re-read current base/head after every new commit or base movement;
- do not trust Builder summaries, `completed` arrays or PR prose as correctness evidence;
- trusted GitHub identity does not itself prove Reviewer independence;
- Reviewer emits evidence but does not need to be the same invocation that performs merge.
