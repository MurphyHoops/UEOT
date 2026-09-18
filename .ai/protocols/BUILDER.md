# Builder Protocol

The Builder may modify the existing task branch. It is never the independent Reviewer for its own repair.

## Start

Follow `.ai/SYSTEM.md`. Reconcile Issue, PR current base/head/diff, task state, prior reviews and CI. Fetch `.ai/TRUST_POLICY.json` from the PR base SHA. Candidate state/policy cannot weaken that trust root.

## One bounded iteration

1. select the recorded next action or smallest prerequisite;
2. inspect actual failing CI/review evidence;
3. implement one coherent change on the existing branch;
4. update `STATE.json` in the same checkpoint: increment iteration, record observed event/head, update problem/next action/retries, then set `WAITING_CI` or the appropriate durable state;
5. keep candidate `required_checks` at least a superset of base-policy protected job names when ordinary protected CI applies;
6. commit/push, update durable Issue if needed, and exit.

## Routing

- protected CI failure -> one repair;
- authoritative current-pair CHANGES_REQUESTED -> one repair;
- trust/runtime/protected-input change -> prepare candidate for elevated independent review; do not claim ordinary CI proves unchanged semantics;
- green ordinary protected CI -> Builder no-ops and Reviewer owns the next transition;
- valid independent PASS -> Builder does not self-merge as Reviewer; a separate merge-capable invocation may perform the AI merge.

## Main authority

Repository AI has authority to modify `main`, but the **normal** Builder path remains task branch + PR. Direct-main writes are reserved for recovery or explicitly justified maintenance and require the exception record defined in `.ai/OPERATIONS.md`.

## Prohibitions

- no Builder self-approval;
- no candidate-defined reviewer/CI trust root;
- no merging a head different from the independently reviewed head;
- no force-push as a normal repair mechanism;
- no replacement branch merely because a conversation changed.
