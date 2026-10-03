# GCR4 — Finite-Policy Abelian Stationary Witness Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Planning parent: #242
Governance base: `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Prior local stages: GCR0 `4c87558`, GCR1 `83d28d6`, GCR2 `611706c`, GCR3 `9c75f5c`
Counted-core impact: **NONE**

## Scope

GCR4 performs exactly the finite-policy Abelian witness extraction frozen by
#243.  Starting from an arbitrary admissible randomized complete-history causal
policy whose exact physical path law reaches `K` almost surely, it extracts one
**fixed deterministic stationary policy** whose canonical stationary physical
path law also reaches `K` almost surely.

This stage deliberately stops at almost-sure hitting.  It does **not** prove
finite expected hitting time; that is the separate GCR5 obligation.

## Canonical discount schedule

`gcrBeta n = 1 - (1/2)^(n+1)`.

Machine-checked properties:

- `gcrBeta_pos`: `0 < gcrBeta n`;
- `gcrBeta_lt_one`: `gcrBeta n < 1`;
- `gcrBeta_tendsto_one`: `gcrBeta -> 1` along `atTop`.

This gives a concrete Lean-friendly sequence of genuine discounts while
remaining independent of any policy choice.

## Greedy value / exact path-law bridge

`gcrGreedyPolicy P K n` is the selector of the exact GCR1 normalized absorbed
`GreedyCertificate` at discount `gcrBeta n`.

`greedyValue_eq_stationaryOccupation` proves that the Bellman value of a greedy
certificate is exactly the GCR2 exact-path-law normalized occupation of the
stationary admissible embedding of its selector.  The proof uses the existing
`GreedyCertificate.stationary_infiniteValue_eq_value` theorem plus the GCR2
`admissibleCausalNormalizedInfiniteValue_eq_occupation` identity; it does not
identify Bellman and path-law semantics informally.

## Finite-policy pigeonhole extraction

Because `X` and `A` are finite, the deterministic stationary policy type
`X -> A` is finite.  `exists_repeated_gcrGreedyPolicy` applies Mathlib's strong
infinite pigeonhole principle to the sequence `gcrGreedyPolicy P K` and obtains:

- one fixed policy `g : X -> A`;
- an injective index subsequence `sigma : Nat -> Nat`;
- `sigma -> infinity` via `Function.Injective.nat_tendsto_atTop`;
- `gcrGreedyPolicy P K (sigma n) = g` for every `n`.

No compact-policy-space or choice-of-convergent-subsequence assumption is used;
this is literal finiteness of `X -> A`.

## Stationary occupation squeeze

For an arbitrary admissible causal policy `pi` that hits `K` almost surely,
GCR3 gives

`causalNormalizedOccupation(pi, gcrBeta n) -> 1`.

At each selected index `sigma n`:

1. GCR3 discounted domination gives
   `occupation(pi) <= greedy value`;
2. `greedyValue_eq_stationaryOccupation` and the repeated-selector equality
   rewrite that value as the exact occupation of the one fixed `g`;
3. exact normalized occupation is at most `1`.

The squeeze theorem therefore yields

`causalNormalizedOccupation(stationaryAdmissible g, gcrBeta (sigma n)) -> 1`.

## Occupation-to-almost-sure-hitting converse used in GCR4

For a fixed absorbed path law `mu`, let

`q = mu.real (neverHitSet K)`.

Since `neverHitSet K` is contained in every finite `survivalSet K n`, each
survival probability is at least `q`.  Consequently

`q <= geometricAbelAverage(survival, beta)`

for every genuine discount.  GCR3's exact identity

`occupation = 1 - geometricAbelAverage(survival, beta)`

then shows that occupation tending to `1` along the selected discounts forces
`q = 0`.  Hence the absorbed exact path law reaches `K` almost surely.

This argument is intentionally weaker than GCR5: it proves zero never-hit mass,
not summability of the survival tail and not finite expected hitting time.

## Public GCR4 conclusion

`exists_stationaryPolicy_ae_eventually_hits` proves:

- input: an `AdmissibleCausalRepairPolicy` whose original exact
  `causalRepairPathLaw` reaches `K` almost surely;
- output: a deterministic stationary `g : X -> A` such that
  `stationaryTrajMeasure P g (PMF.pure x)` reaches `K` almost surely.

The final semantic conversion is exact:

- GCR1 transfers absorbed a.s.-hitting back to the original dynamics;
- GCR0 rewrites the stationary causal embedding's physical path law to the
  canonical `stationaryTrajMeasure`.

Thus GCR4 establishes the memoryless-determinacy **almost-sure witness** required
before GCR5.

## Assumption audit

The public result uses only the authorized finite controlled-PMF setting:

- finite `X` and finite `A`;
- `Nonempty A` for greedy selection;
- measurable-singleton state/action structures;
- the existing AR6 `AdmissibleCausalRepairPolicy` witness;
- no compactness/Feller, irreducibility, recurrence, spectral gap, finite
  expectation, or new generator assumption.

## Boundary discipline

GCR4 does **not**:

- prove `E[tau_K] < infinity` for the stationary witness;
- assert `GeneralCausalToStationaryCompleteness` yet;
- prove the set-level equivalence reserved for GCR6;
- identify the maximal AR certificate basin with the general-causal set;
- mutate Track S/H, counted Core, ledger, coverage, or the four-generator core;
- enter RH/RLSR/EC/OC/AP;
- claim a fifth generator or full autopoiesis.

## Local validation

The exact local candidate passed the complete GCR stage gate:

- focused Lean compile of `FinitePolicyAbelianStationaryWitness.lean`: **PASS**;
- `lake build UEOT.V3.Compression.Objecthood`: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS** (`9108/9108` jobs);
- proof-escape scan (`sorry|admit|axiom|opaque|unsafe`): **CLEAR**;
- representative `#print axioms` for `gcrBeta_tendsto_one`,
  `greedyValue_eq_stationaryOccupation`,
  `exists_stationaryOccupation_subsequence_tendsto_one`, and
  `exists_stationaryPolicy_ae_eventually_hits`: only `propext`,
  `Classical.choice`, `Quot.sound`;
- research-governance regression suite: **PASS**;
- exact-candidate Track-O validation: **PASS — 3 changed paths**;
- final `git diff --check`: **PASS**;
- atomic local commit: created only after these checks.

No research branch is pushed during this stage.  The first research push remains
for the cumulative GCR0--GCR8 local closure only.
