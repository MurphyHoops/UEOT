# GCR6 — General-Causal / Stationary Completeness Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Planning parent: #242
Governance base: `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Prior local stages: GCR0 `4c87558`, GCR1 `83d28d6`, GCR2 `611706c`, GCR3 `9c75f5c`, GCR4 `2aec086`, GCR5 `a1cb1ec`
Counted-core impact: **NONE**

## Scope

GCR6 closes the exact AR6 G3 boundary named by
`GeneralCausalToStationaryCompleteness`.  For finite controlled PMF dynamics,
an arbitrary randomized complete-history causal policy whose exact physical
Ionescu--Tulcea law reaches `K` almost surely now implies existence of a
deterministic stationary policy with finite canonical expected hitting time.

## Forward direction

`generalCausalToStationaryCompleteness` is a direct composition of the proved
GCR stages:

1. unpack `GeneralCausalAlmostSureRepairable` to obtain the exact admissible
   causal witness;
2. GCR4 `exists_stationaryPolicy_ae_eventually_hits` extracts one deterministic
   stationary `g` whose canonical `stationaryTrajMeasure` hits `K` almost surely;
3. GCR5 `stationary_expectedHittingTime_ne_top_of_ae_eventually_hits` upgrades
   that stationary a.s.-hitting witness to
   `expectedHittingTime (stationaryKernel P g) x K != infinity`;
4. this is exactly membership in `StationaryRepairBasin`, hence
   `DeterministicStationaryFiniteExpectedRepairable`.

No discounted theorem is used directly as an undiscounted conclusion here;
GCR2--GCR5 supply the required bridges.

## Reverse direction

`deterministicStationaryFiniteExpectedRepairable_to_generalCausal` proves the
easy reverse implication without an informal policy-class inclusion:

1. finite expected hitting gives a.s. eventual hitting under the genuine
   homogeneous Markov law via the existing
   `eventually_hits_ae_of_expectedHittingTime_ne_top`;
2. the deterministic stationary policy is embedded as `stationaryAdmissible`;
3. GCR0 `stationaryCausal_pathLaw_eq_stationaryTrajMeasure` identifies its exact
   AR6 causal physical path law with the canonical stationary trajectory law.

This satisfies the explicit #243 requirement that stationary -> general-causal
must use GCR0.

## Set-level closure

GCR6 proves both:

- `generalCausalAlmostSureRepairable_iff_deterministicStationary`;
- `generalCausalRepairableSet_eq_deterministicStationaryRepairableSet`.

Thus the arbitrary-causal almost-sure repairable set and the deterministic-
stationary finite-expected-hitting repairable set are exactly equal in the
finite PMF semantics covered by GCR.

## Boundary discipline

GCR6 does **not** yet:

- identify this set with the AR3 maximal certificate basin — reserved for GCR7;
- resynthesize the broad Objecthood repair theorem — reserved for GCR7;
- perform the architecture/deletion/G3 classification audit — reserved for GCR8;
- mutate Track S/H, counted Core, ledger, coverage, or the four-generator core;
- enter RH/RLSR/EC/OC/AP;
- claim a fifth generator or full autopoiesis.

## Local validation

The exact local candidate passed the complete stage gate:

- focused Lean compile of `GeneralCausalStationaryCompleteness.lean`: **PASS**;
- Objecthood build: **PASS**;
- Compression build: **PASS** (`9110/9110` jobs);
- proof-escape scan: **CLEAR**;
- representative `#print axioms` on the completeness theorem, reverse
  direction, pointwise iff, and set equality: only `propext`,
  `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- exact-candidate Track-O validation: **PASS — 3 changed paths**;
- final `git diff --check`: **PASS**.

The research branch remains local through GCR8.
