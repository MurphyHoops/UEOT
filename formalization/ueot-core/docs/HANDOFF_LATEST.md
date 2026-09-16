# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current authoritative checkpoint

- frozen source P-IDs: **106**;
- counted FULL-GREEN: **83/106**;
- remaining not-yet-counted: **23**;
- authoritative main: `995c99683e0ae225f8df46108fd1442038c3963a`;
- 83/106 ledger PR: **#94**;
- ledger branch CI: `35107803914` — success;
- ledger PR CI: `35108606468` — success;
- ledger resulting-main CI: `35109381744` — success;
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
- official root target: `lake build UEOT`;
- active uncounted theorem proof lanes: **0**.

P-CTL-01 is therefore **CLOSED / COUNTED**. Do not reopen it absent an explicit
frozen-source mismatch or a regression on main.

## P-CTL-01 — completed lifecycle

Frozen Core 3 P-CTL-01 is represented at source strength for finite discounted
control: finite state space, state-dependent finite nonempty action sets,
bounded rewards, stochastic transitions and `0 < beta < 1`.

The counted proof establishes:

1. Bellman contraction in the finite-state sup metric;
2. existence and uniqueness of the Bellman fixed point `V*`;
3. value-iteration convergence from every initial value function;
4. the Bellman-residual stopping/error certificate;
5. arbitrary causal policies with arbitrary time-indexed memory and randomized action laws, hence full history dependence;
6. finite-horizon domination by `V*` plus an explicit geometric terminal tail;
7. existence of every causal policy's infinite discounted value;
8. domination of every causal history-dependent randomized policy by `V*`;
9. stationary deterministic Bellman-greedy attainment of `V*` at every state.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality`.

Supporting source-facing facts:
- `UEOT.V3.FiniteDiscountedControl.Model.fixedPoint_unique`;
- `UEOT.V3.FiniteDiscountedControl.Model.valueIteration_tendsto`;
- `UEOT.V3.FiniteDiscountedControl.Model.valueError_le_residual`;
- `UEOT.V3.FiniteDiscountedControl.CausalPolicy.infiniteValue_le_optimal`;
- `UEOT.V3.FiniteDiscountedControl.greedy_infiniteValue_eq_optimal`.

Promotion evidence:
- feature head `47218ef06c63ed81ab3974d107f0d3d46cc49ecb`, root CI `35098260086` success;
- clean integration head `45440746a7086b74bc65ba741611f98a8da92f27`, root CI `35099296408` success;
- proof PR #93 CI `35102272835` success;
- proof main `3efe7ebc74d8f2a6705c12a5218a7880f5a3688c`, resulting-main CI `35104140440` success;
- ledger branch final staged head `df4b04b8ce6fe0214f0c9cc4143ad9787004115b`, branch CI `35107803914` success;
- ledger PR #94 CI `35108606468` success;
- ledger main `995c99683e0ae225f8df46108fd1442038c3963a`, resulting-main CI `35109381744` success;
- prohibited-proof audit clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`).

## Repository branch governance — current gate

At the 83/106 checkpoint the remote repository has **18 branches** and **0 open
PRs**. Repository hard cap is 12 and normal target is 8. Therefore branch hygiene
precedes any new theorem branch.

The reviewed `.github/workflows/core3-branch-hygiene.yml` is intentionally scoped
to audited Core-3 legacy namespaces. It:

- never deletes `main`;
- preserves its explicit keep-set, any `hold/*`, and all open-PR heads;
- treats unknown/non-Core namespaces as out of scope;
- records exact pre-delete branch SHAs to Issue #56 before mutation;
- performs bounded-batch deletion only after audit;
- records the post-cleanup branch list;
- fails if apply-mode cleanup still leaves more than 12 branches.

The already-completed branch `formal/ledger-81-pcomp01` is reused solely as the
governance PR surface so no new branch is created. It is reset from the latest
full-green main before the governance changes. Once that PR merges, the hygiene
workflow may retire this branch together with the other completed `formal/*`
legacy branches.

## Next theorem lane after branch hygiene — P-QUO-01

P-QUO-01 is the next high-leverage source-facing target. The existing
`UEOT.V3.StructuredQuotient` module is P-INT-02 response-kernel infrastructure
and **must not** be substituted for the frozen control quotient.

Frozen P-QUO-01 obligations:

1. same admissible action type/set on each fibre of a surjective macro map `f`;
2. exact reward closure through `f`;
3. for every admissible action, exact pushed-forward transition closure through `f`;
4. Bellman intertwining for pulled-back macro value functions;
5. unique fixed-point pullback `V* = Vbar* ∘ f`;
6. actionwise optimal-Q agreement;
7. lifting of any macro stationary argmax selector to a micro stationary policy with the same optimal value, including tie cases.

Reusable main infrastructure:

- `FiniteDiscountedControl.Model.expect`;
- `FiniteDiscountedControl.Model.qValue`;
- `FiniteDiscountedControl.Model.bellman`;
- `FiniteDiscountedControl.Model.fixedPoint_unique`;
- the full causal-policy infinite-value layer completed for P-CTL-01;
- pinned Mathlib fibre regrouping (`Fintype.sum_fiberwise` / `Finset.sum_fiberwise*`).

Expected audit class: **B — explicit bridge on an existing control foundation**.
Planned source-facing module: `UEOT/V3/FiniteDiscountedExactQuotient.lean`.
A generic stationary-selector policy-evaluation lemma should be factored from the
existing greedy-policy proof so that macro argmax ties are handled correctly;
do not require equality with a particular canonical tie-breaking selector.

P-QUO-02 and P-QUO-04 remain separate source propositions. P-QUO-04 explicitly
requires its resolvent/Neumann identity and may not be replaced by only a
finite-horizon or telescoping occupancy surrogate. P-TEL-01 is already counted
and must not be reopened or double-counted.

## Larger pending foundations

P-PER-02; P-ALI-01; P-DDH-02/03/04/05; P-KL-04/05; P-EVO-03/04;
P-QSD-01/04 remain source-strength lanes unless a fresh main audit finds an exact
bridge. P-EVO-03 still requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; an assumed-convergence surrogate is forbidden.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green or proof-main green never increments source-level coverage;
- no `sorry`, `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; no finite/toy/assumed-conclusion replacement of a stronger source theorem;
- source-object identity must be explicit; generalization alone does not count without a bridge back to the frozen object;
- historical rejected surrogate routes remain part of the recovery audit;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level;
- P-EVO-03 requires the full primitive nonnegative-matrix Perron-Frobenius asymptotic package.

## Exact continuation order

1. complete the audited branch-hygiene PR lifecycle;
2. verify post-cleanup remote branch count `<= 12` and preferably `<= 8`;
3. verify latest main root CI remains green;
4. only then open/reuse one P-QUO-01 proof lane from latest full-green main;
5. implement source object → fibre sum/expect bridge → qValue/Bellman intertwining → fixed-point pullback → generic optimal-selector lift → source-facing theorem;
6. run official root CI and the full promotion lifecycle before incrementing coverage.

## Recovery order

1. `NEW_CHAT_BOOTSTRAP.md`;
2. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`;
3. `UEOT_CORE3_LEAN_OPERATIONS.md`;
4. Issue #56 when available;
5. `PID_STATUS.yaml`;
6. `FORMALIZATION_STATE.md`;
7. `V3_COVERAGE_STATUS.md`;
8. this `HANDOFF_LATEST.md` fallback snapshot;
9. live main/branches/PR/CI reconciliation.
