# GCR3 — Arbitrary-Causal Discounted Direction / Abelian Reachability Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Planning parent: #242
Governance base: `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Prior local stages: GCR0 `4c87558`, GCR1 `83d28d6`, GCR2 `611706c`
Counted-core impact: **NONE**

## Scope

GCR3 proves exactly the two implications frozen by #243 and no more:

1. for each fixed `0 < beta < 1`, every admissible randomized complete-history
   causal repair policy is dominated by the deterministic stationary greedy
   certificate of the GCR1 normalized absorbed Bellman model, now stated in the
   exact GCR2 physical path-law occupation semantics;
2. if the original exact causal path law hits `K` almost surely, then along
   **any** sequence `beta_m in (0,1)` with `beta_m -> 1`, its exact normalized
   absorbed occupation tends to `1`.

GCR3 does not extract one stationary policy. That finite-policy pigeonhole step
belongs to GCR4.

## Probability bridge

The new file `GeneralCausalDiscountedDirection.lean` first proves the missing
absorbed probability identities on the complete-history Markovization.

- The physical current-state marginal of an absorbed transition started inside
  `K` is a Dirac self-loop.
- Therefore `historyRepairTarget K` is an absorbing set for the absorbed
  `historyKernel`.
- A generic absorbing-kernel induction proves, in `ENNReal`, that at every time
  `n`:

  `targetMass_n + survivalProb_n = 1`.

- `absorbed_targetProb_add_survivalReal_eq_one` transports that identity back to
  the exact absorbed physical Ionescu--Tulcea law used by GCR2.
- Using the GCR1 `neverHitSet = iInter survivalSet` characterization and
  continuity from above,
  `absorbed_survivalReal_tendsto_zero_of_ae_eventually_hits` proves:

  original causal a.s. eventual hit
  -> absorbed causal a.s. eventual hit
  -> finite survival probabilities tend to zero.

No finite-expectation assumption or stationary-policy assumption is used.

## Abelian bridge

`geometricAbelAverage s beta` is defined as

`sum_n beta^n * (1-beta) * s_n`.

For `0 <= s_n <= 1`, the file proves:

- weighted summability for every `0 <= beta < 1`;
- normalized geometric total mass is exactly `1`;
- nonnegativity / unit upper bound;
- the quantitative head-tail estimate

  `Abel_beta(s) <= N*(1-beta) + delta`

  whenever `s_n <= delta` for all `n >= N`.

From this, `geometricAbelAverage_tendsto_zero` proves the sequential Abel
statement needed by GCR4: for **arbitrary** `beta_m -> 1` with
`0 <= beta_m < 1`, if `s_n -> 0`, then `Abel_{beta_m}(s) -> 0`.

This is a direct epsilon head/tail proof. No Tannery/dominated-convergence
hypothesis is smuggled in; in particular no nonexistent beta-uniform summable
majorant is assumed.

## Exact GCR2 occupation rewrite

For each genuine discount:

- `causalNormalizedOccupation_eq_tsum_target` identifies the GCR2 `limUnder`
  occupation with its actual convergent target-coordinate series;
- `causalNormalizedOccupation_eq_one_sub_survivalAbel` proves

  `occupation = 1 - Abel_beta(survival)`.

Consequently the Abelian limit is a theorem about the exact physical causal
path law, not a Bellman-only surrogate.

## Public GCR3 conclusions

### `causalNormalizedOccupation_le_greedyValue`

For every admissible randomized complete-history causal policy and fixed
`0 < beta < 1`:

`exact causal normalized occupation <= deterministic stationary greedy value`.

This is obtained by composing the existing all-causal discounted verifier from
GCR1 with the exact path-law identity from GCR2.

### `causalNormalizedOccupation_tendsto_one_of_ae_eventually_hits`

For every sequence `beta_m` with

- `0 < beta_m < 1`, and
- `beta_m -> 1`,

if the original exact causal path law hits `K` almost surely, then

`causalNormalizedOccupation(..., beta_m) -> 1`.

This theorem is intentionally sequence-parametric so GCR4 can choose a concrete
Lean-friendly sequence and then perform finite-policy pigeonhole extraction.

## Assumption audit

Public GCR3 results use only the authorized finite controlled-PMF setting:

- finite physical state and action spaces;
- measurable-singleton physical/action structures;
- nonempty action space only where a greedy selector is needed;
- `AdmissibleCausalRepairPolicy` carrying the exact AR6 per-time Markov kernel
  witnesses;
- genuine discount factors in `(0,1)`.

No compactness, Feller continuity, irreducibility, recurrence, finite expected
hitting, stationary completeness, spectral assumption, or new generator
assumption is introduced.

## Boundary discipline

GCR3 does **not**:

- select a repeated deterministic stationary policy;
- claim a deterministic stationary policy hits `K` almost surely;
- prove finite expected hitting time;
- assert `GeneralCausalToStationaryCompleteness`;
- mutate Track S/H or counted Core/ledger/coverage;
- enter RH, RLSR, EC, OC, or AP;
- claim a fifth generator or full autopoiesis.

## Local validation

- focused compile of `GeneralCausalDiscountedDirection.lean`: **PASS**
- `lake build UEOT.V3.Compression.Objecthood`: **PASS** (`8842` jobs)
- `lake build UEOT.V3.Compression`: **PASS** (`9107` jobs)
- proof-escape scan (`sorry|admit|axiom|opaque|unsafe`): **CLEAR**
- representative `#print axioms`:
  - `absorbed_targetProb_add_survivalReal_eq_one`: `propext`, `Classical.choice`, `Quot.sound`
  - `geometricAbelAverage_tendsto_zero`: `propext`, `Classical.choice`, `Quot.sound`
  - `causalNormalizedOccupation_le_greedyValue`: `propext`, `Classical.choice`, `Quot.sound`
  - `causalNormalizedOccupation_tendsto_one_of_ae_eventually_hits`: `propext`, `Classical.choice`, `Quot.sound`
- no nonstandard/project-local proof axiom introduced.

Research-governance regression, exact-candidate validation, and final `git diff --check` all pass on the exact staged candidate used for the atomic local commit.
