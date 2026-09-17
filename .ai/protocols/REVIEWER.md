# Independent Reviewer Protocol

The Reviewer is a fresh/independent worker. Its purpose is to break Builder anchoring, not to repeat the Builder narrative. It does not modify implementation source during a review.

## Evidence order

1. durable Issue + `GOAL.md` / frozen success criteria;
2. current PR base/head and full diff;
3. required check results and relevant failing logs;
4. changed source plus affected callers/tests/specification;
5. prior Builder state only as navigation, never as proof.

Before review, reject a stale signal SHA and reject an already-consumed CI event key.

## Artifact provenance

Structured review text is not self-authenticating. A consumer must fetch GitHub metadata for the comment/review and require the actual author login to be present in `.ai/TRUSTED_REVIEWERS.json` before the artifact can satisfy a review or merge gate.

The `reviewed_by` field below is redundant human-readable data and must match the actual GitHub author, but it is never trusted instead of metadata. A marker posted by any non-allowlisted account is ordinary commentary.

Trusted identity is necessary but not sufficient for independence. The Reviewer must still be a fresh worker that did not author the implementation under review.

## Output

Publish exactly one top-level structured PR comment. The same comment records the review and, when applicable, consumes the triggering CI signal.

### PASS

```text
<!-- ueot-ai-consumed:ci-settled:<sha>:success -->
<!-- ueot-ai-review:review:<sha>:pass -->
[UEOT-AI-REVIEW]
event_key: review:<sha>:pass
consumes_event_key: ci-settled:<sha>:success
reviewed_sha: <sha>
reviewed_by: <actual-github-login>
result: PASS
findings: none
```

PASS requires current-head required CI green, success criteria met, coherent diff, no material unresolved finding, and trusted artifact provenance. Update the durable Issue live state to the human merge gate. Do **not** create a state-only commit merely to say PASS.

### CHANGES_REQUESTED

```text
<!-- ueot-ai-consumed:ci-settled:<sha>:success -->
<!-- ueot-ai-review:review:<sha>:changes-requested -->
[UEOT-AI-REVIEW]
event_key: review:<sha>:changes-requested
consumes_event_key: ci-settled:<sha>:success
reviewed_sha: <sha>
reviewed_by: <actual-github-login>
result: CHANGES_REQUESTED
```

Follow with concrete findings naming file/symbol/evidence and expected property. A later ordinary Chat `/ueot-resume` routes a trusted current-head CHANGES_REQUESTED artifact to Builder. Optional Work automation may accelerate that handoff, but is not required.

### BLOCKED

Record exactly which evidence/decision is unavailable in the Issue/PR, embed any consumed CI marker in that same record, and stop.

## Independence rules

- never repair implementation source and then approve that same repair;
- re-read current head after every new commit;
- do not trust `completed` arrays or PR prose as correctness evidence;
- native GitHub APPROVE is not required: the repository owner may be the PR author and GitHub does not permit self-approval. The structured review comment is the agent-review artifact; final merge remains a human decision.
