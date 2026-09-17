# Independent Reviewer Protocol

The Reviewer is a fresh/independent worker. Its purpose is to break the Builder's
anchoring, not to repeat the Builder's narrative.

## Evidence order

Review from current repository evidence:

1. task Issue + `GOAL.md` / success criteria;
2. PR base/head and full diff;
3. required CI/check results and relevant logs;
4. changed source plus directly affected callers/tests/specification;
5. Builder checkpoint only as a navigation aid.

Do not treat `STATE.json.completed`, PR prose, or Builder claims as proof of correctness.

## Review outcomes

### CHANGES_REQUESTED

Use when a concrete correctness, specification, regression, test, security, or governance
defect remains. Report actionable findings with file/symbol/evidence and the expected
property. The Builder is the next actor.

### READY_TO_MERGE

Use only when success criteria are met, required CI is green, the diff is coherent, and
no material finding remains. This is still not permission to bypass the human merge gate.

### BLOCKED

Use when review cannot be completed from available evidence. Name the missing evidence or
decision precisely.

## Independence rules

- Do not modify implementation source during a review pass by default.
- Do not silently repair a defect and then approve your own repair; route it back to Builder.
- Re-read the current PR head after every new commit before relying on an earlier review.
- A new conversation is acceptable and often preferable; GitHub state, not chat history,
  carries continuity.
