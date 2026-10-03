# GCR2 — Exact Path-Law Discounted Hitting Transform Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Parent planning: #242
Governance base: `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Prior local stages: GCR0 `4c87558`, GCR1 `83d28d6`
Counted-core impact: **NONE**

## Scope

GCR2 closes the main Route-A semantic bridge between the existing
complete-history discounted-control layer and the exact physical
Ionescu--Tulcea path law.

The stage proves that, for the GCR1 absorbed model with normalized reward
`(1-beta) * 1_K` and `0 < beta < 1`, the nested causal discounted value from a
deterministic initial state is exactly the normalized discounted target
occupation of the absorbed physical path law.

This is the equivalent hitting-transform representation explicitly permitted by
#243.  GCR2 does not take `beta -> 1` and does not assert an undiscounted
reachability theorem.

## Semantic route

The proof is deliberately layered rather than identifying the nested Bellman
value with a path expression by fiat:

1. `integral_fixedPolicyAugmented`
   - converts one complete-history transition expectation into the exact
     action-then-state nested integral used by `Model.truncatedValue`.
2. `carrierRepairTruncatedValue`
   - gives the ordinary homogeneous Markov recursion on the time-tagged complete
     history carrier.
3. `truncatedValue_eq_carrierRepairTruncatedValue`
   - proves the nested causal value equals that carrier recursion at every
     finite horizon.
4. `carrierTargetProbability`
   - defines exact `n`-step target probability under the homogeneous history
     kernel.
5. `carrierTargetProbability_succ`
   - proves its Chapman--Kolmogorov recursion.
6. `carrierNormalizedOccupationPartial_succ`
   - proves the finite normalized occupation satisfies the same Bellman
     recursion.
7. `truncatedValue_eq_carrierNormalizedOccupationPartial`
   - identifies the two finite recursions exactly.
8. General Ionescu--Tulcea marginal bridges
   - `homHistoryKernel_comp_eq_last_marginal_general` and
     `homTrajMeasure_time_succ_general` remove accidental finite-state wrapper
     assumptions and work on the infinite time-tagged `Carrier` without adding
     `Fintype Carrier` or `MeasurableSingletonClass Carrier`.
9. `causalRepairPathLaw_targetProbability_eq_carrier`
   - identifies each carrier `n`-step target probability with the corresponding
     target-coordinate probability of the exact absorbed physical causal path
     law.
10. `causalNormalizedOccupationPartial_eq_integral`
    - proves the finite coordinate-probability sum is literally the Bochner
      expectation of the pathwise finite normalized target occupation under the
      exact physical Ionescu--Tulcea law.
11. `truncatedValue_eq_causalNormalizedOccupationPartial`
    - is the finite exact path-law bridge.
12. `admissibleCausalNormalizedInfiniteValue_eq_occupation`
    - identifies the existing discounted `infiniteValue` with the `limUnder`
      of those exact path-law occupations.
13. `causalNormalizedOccupationPartial_tendsto`
    - proves that limit is genuine, inherited from the already machine-checked
      Cauchy convergence of `truncatedValue`; it is not an arbitrary `limUnder`
      choice.

## Relation to first-hitting semantics

GCR1 now separately proves that target absorption preserves all finite survival
probabilities and almost-sure eventual hitting under the original exact causal
path law.  GCR2 therefore works entirely with the absorbed law without changing
first-hitting semantics.

For an absorbed process, normalized discounted target occupation is the Route-A
hitting-transform representation: once the target has been hit, all subsequent
coordinates remain in the target.  #243 explicitly allows this normalized
occupation representation as equivalent to `E[beta^tau_K; tau_K < infinity]`.
GCR3 will use this exact path-law surrogate for the `beta -> 1` direction; GCR2
does not perform that limit.

## Assumption audit

The public GCR2 theorems use only the finite controlled-PMF setting already
frozen by GCR:

- finite `X` and `A`;
- measurable-singleton structures on physical state/action spaces;
- an `AdmissibleCausalRepairPolicy`, which carries exactly the per-time Markov
  kernel witnesses required by AR6;
- `0 < beta < 1` where discounted infinite value is used.

No compactness, Feller continuity, irreducibility, recurrence, stationary-policy
assumption, almost-sure-hitting assumption, finite-expected-hitting assumption,
or new generator assumption is introduced.

Crucially, the infinite complete-history carrier itself is **not** assumed
finite or measurable-singleton.

## Boundary discipline

GCR2 does not:

- infer almost-sure reachability from discounted optimality;
- take the Abelian `beta -> 1` limit;
- extract a stationary witness;
- prove finite expected hitting time;
- assert `GeneralCausalToStationaryCompleteness`;
- mutate Track S/H, the counted ledger/coverage, or the four-generator core;
- enter RH/RLSR/EC/OC/AP;
- claim a fifth generator or full autopoiesis.

## Local validation

- focused Lean compile of `ExactPathLawDiscountedHittingTransform.lean`: **PASS**
- `lake build UEOT.V3.Compression.Objecthood`: **PASS**
- `lake build UEOT.V3.Compression`: **PASS**
- proof-escape scan (`sorry|admit|axiom|opaque|unsafe`): **CLEAR**
- representative `#print axioms`:
  - `truncatedValue_eq_causalNormalizedOccupationPartial`: `propext`, `Classical.choice`, `Quot.sound`
  - `causalNormalizedOccupationPartial_eq_integral`: `propext`, `Classical.choice`, `Quot.sound`
  - `admissibleCausalNormalizedInfiniteValue_eq_occupation`: `propext`, `Classical.choice`, `Quot.sound`
  - `causalNormalizedOccupationPartial_tendsto`: `propext`, `Classical.choice`, `Quot.sound`
- governance regression / exact-candidate validation / final `git diff --check`: executed on the exact candidate immediately before the atomic local commit
