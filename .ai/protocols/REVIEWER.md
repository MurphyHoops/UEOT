# Independent Reviewer Protocol

The Reviewer is a fresh/independent worker. Its purpose is to break Builder anchoring, not to repeat the Builder narrative. It does not modify implementation source during a review.

## Evidence order

1. durable Issue + `GOAL.md` / frozen success criteria;
2. current PR base/head and full diff;
3. required check results and relevant failing logs;
4. changed source plus affected callers/tests/specification;
5. prior Builder state only as navigation, never as proof.

Before review, reject a stale signal SHA and reject an already-consumed CI event key.

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
result: PASS
findings: none
```

PASS requires current-head required CI green, success criteria met, coherent diff, and no material unresolved finding. Update the durable Issue live state to the human merge gate. Do **not** create a state-only commit merely to say PASS.

### CHANGES_REQUESTED

```text
<!-- ueot-ai-consumed:ci-settled:<sha>:success -->
<!-- ueot-ai-review:review:<sha>:changes-requested -->
[UEOT-AI-REVIEW]
event_key: review:<sha>:changes-requested
consumes_event_key: ci-settled:<sha>:success
reviewed_sha: <sha>
result: CHANGES_REQUESTED
```

Follow with concrete findings naming file/symbol/evidence and expected property. A later ordinary Chat `/ueot-resume` routes this state to Builder. Optional Work automation may accelerate that handoff, but is not required.

### BLOCKED

Record exactly which evidence/decision is unavailable in the Issue/PR, embed any consumed CI marker in that same record, and stop.

## Independence rules

- never repair implementation source and then approve that same repair;
- re-read current head after every new commit;
- do not trust `completed` arrays or PR prose as correctness evidence;
- native GitHub APPROVE is not required: the repository owner may be the PR author and GitHub does not permit self-approval. The structured review comment is the agent-review artifact; final merge remains a human decision.
