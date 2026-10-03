# GCR1 — Absorbed Normalized Discounted Repair Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Parent planning: #242
Governance base: `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Counted-core impact: **NONE**

## Scope

GCR1 introduces the exact absorbed normalized discounted model used by the
selected Route A. It remains a discounted control stage; no undiscounted
reachability or general-causal completeness claim is made here.

## New semantic interfaces

- `absorbedRepairPMF P K`
  - if `x ∈ K`, every action produces `PMF.pure x`;
  - if `x ∉ K`, the transition is exactly `P x a`.
- `pmfControlledKernel_absorbedRepair_of_not_mem`
  - kernel-level equality with the original controlled model at every pre-hit
    state.
- `controlledNext_absorbedRepair_of_current_not_mem`
  - the exact complete-history physical next-state kernel is unchanged for
    every action whenever the current history state has not hit `K`.
- `pmfControlledKernel_absorbedRepair_of_mem`
  - target states are action-independent Dirac self-loops.

These local identities are now lifted in
`AbsorbedRepairHittingSemantics.lean` to the exact complete-history and physical
Ionescu--Tulcea laws.  In particular:

- `historyKernel_absorbed_of_current_not_mem` proves equality of the entire
  one-step complete-history transition measure at every pre-hit history;
- `causalRepairPathLaw_absorbed_survival_eq` proves equality of every finite
  survival-event probability under the original and absorbed exact physical
  causal path laws;
- `causalRepairPathLaw_absorbed_eventually_hits_iff` proves that target
  absorption preserves almost-sure eventual hitting in both directions.

Thus GCR1 now satisfies the frozen contract that absorption does not change
first-hitting semantics.  GCR2 starts from this established invariant and is
responsible only for the exact discounted hitting-transform / normalized
occupation identity.

## Normalized discounted model

The reward is

`(1 - beta) * 1_K`

for `0 < beta < 1`. Two aligned models are constructed:

1. `finiteNormalizedRepairModel` — finite PMF Bellman model used to synthesize
   the deterministic greedy selector;
2. `causalNormalizedRepairModel` — kernel-valued complete-history model used by
   `CompactCausalOptimalityCore`.

`integral_absorbedRepair_eq_sum` is the exact PMF-integral bridge between them.

`normalizedRepairGreedyCertificate` then packages the finite Bellman optimum as
an exact `CompactCausalOptimalityCore.Model.GreedyCertificate` without adding
compactness or Feller assumptions.

Finally,
`allCausal_normalizedDiscountedRepair_le_greedy` proves that for each fixed
`0 < beta < 1`, every randomized complete-history causal policy is dominated by
the deterministic stationary greedy certificate in the absorbed normalized
model.

This theorem is deliberately labelled and documented as **discounted only**.
It is not `GeneralCausalToStationaryCompleteness`.

## Assumption audit

The stage uses:

- finite `X` and finite `A`;
- nonempty `A` only where a greedy action must be selected;
- finite measurable-singleton structures already used by AR6;
- `0 < beta < 1` for the Bellman / infinite-value layer.

It does **not** assume compact/Feller continuity, irreducibility, recurrence,
finite expected hitting time, almost-sure hitting, or any stationary-completeness
property.

## Boundary discipline

GCR1 does not:

- identify discounted value with a hitting transform yet;
- take `beta -> 1`;
- infer almost-sure hitting from a policy that did not already have it (it
  proves only original/absorbed invariance of that property);
- infer finite expected hitting;
- mutate Track S/H, counted ledger, coverage, or the four-generator core;
- enter RH/RLSR/EC/OC/AP;
- claim a fifth generator or complete autopoiesis.

## Local validation

- focused Lean compile of `AbsorbedDiscountedRepair.lean`: **PASS**
- focused Lean compile of `AbsorbedRepairHittingSemantics.lean`: **PASS**
- `lake build UEOT.V3.Compression.Objecthood`: **PASS**
- `lake build UEOT.V3.Compression`: **PASS**
- proof-escape scan (`sorry|admit|axiom|opaque|unsafe`): **CLEAR**
- representative `#print axioms`:
  - `controlledNext_absorbedRepair_of_current_not_mem`: `propext`, `Classical.choice`, `Quot.sound`
  - `normalizedRepairGreedyCertificate`: `propext`, `Classical.choice`, `Quot.sound`
  - `allCausal_normalizedDiscountedRepair_le_greedy`: `propext`, `Classical.choice`, `Quot.sound`
  - `causalRepairPathLaw_absorbed_survival_eq`: `propext`, `Classical.choice`, `Quot.sound`
  - `causalRepairPathLaw_absorbed_eventually_hits_iff`: `propext`, `Classical.choice`, `Quot.sound`
- no nonstandard/project-local proof axiom introduced.

Governance regression, exact-candidate validation, and final `git diff --check` all pass on the exact staged candidate used for the atomic local commit.
