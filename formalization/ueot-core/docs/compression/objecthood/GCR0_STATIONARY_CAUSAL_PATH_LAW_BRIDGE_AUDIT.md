# GCR0 — Stationary / General-Causal Path-Law Bridge Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Parent planning: #242
Governance authorization: PR #244, merged to `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Counted-core impact: **NONE**

## Scope

GCR0 closes only the semantic embedding direction required by the later
`GeneralCausalToStationaryCompleteness` proof.  It does not prove any new
reachability, expected-hitting-time, or discounted-to-undiscounted theorem.

The stage adds `StationaryCausalPathLawBridge.lean` and proves that a
finite-state deterministic stationary policy can be represented as the exact
AR6 complete-history kernel-valued `CausalPolicy`, and that the resulting
physical Ionescu--Tulcea path law is exactly the repository's existing
stationary trajectory law.

## New public interfaces

1. `stationaryCausalPolicy pi`
   - embeds `pi : X -> A` as a deterministic complete-history policy;
   - the action at time `n` reads only `currentFiber n h`.

2. `stationaryAdmissible pi`
   - packages the embedding as `AdmissibleCausalRepairPolicy`;
   - each policy kernel is Markov by deterministic-kernel construction.

3. `fixedPolicyAugmented_current_marginal`
   - proves the one-step physical marginal of the history-augmented transition
     is exactly `stationaryKernel P pi`.

4. `historyKernel_stationary_strongLumpability`
   - upgrades the one-step identity to `StrongLumpability` of the complete
     history kernel through `Carrier.current`.

5. `stationaryCausal_pathLaw_eq_stationaryTrajMeasure`
   - applies the already proved `homTrajMeasure_path_naturality` theorem;
   - identifies the AR6 causal physical path law of the stationary embedding
     with `stationaryTrajMeasure P pi (PMF.pure x)` exactly.

## Assumption audit

The bridge uses the same finite-state / finite-action measurable-singleton
setting already used by AR6 and AR stationary repair.  It does not add compact,
Feller, continuity, irreducibility, recurrence, positivity, finite-hitting, or
almost-sure-hitting assumptions.

No target-set hypothesis is needed: GCR0 is purely a policy/path-law semantic
bridge.  In particular it does not smuggle the later GCR reachability result
into the embedding theorem.

## Proof route

The proof deliberately avoids hand-building a second infinite-path
Ionescu--Tulcea induction:

`deterministic stationary policy`
→ `stationaryCausalPolicy`
→ one-step physical marginal equality
→ `StrongLumpability(historyKernel, stationaryKernel, Carrier.current)`
→ existing `homTrajMeasure_path_naturality`
→ exact whole-path law equality.

This reuses the canonical projective-limit uniqueness machinery already in
`DynamicsKernel.lean` rather than duplicating it inside Track O.

## Boundary discipline

GCR0 does **not**:

- use discounted P-CTL as an undiscounted reachability theorem;
- claim the arbitrary-causal direction;
- claim deterministic-stationary completeness;
- mutate Track S/H;
- mutate the frozen counted four-generator core or 106-theorem ledger;
- enter RH, RLSR, EC, OC, or autopoiesis.

## Local validation

- focused Lean compile of `StationaryCausalPathLawBridge.lean`: **PASS**
- `lake build UEOT.V3.Compression.Objecthood`: **PASS**
- `lake build UEOT.V3.Compression`: **PASS**
- proof-escape scan (`sorry|admit|axiom|opaque|unsafe`) on new Lean source: **CLEAR**
- representative `#print axioms`:
  - `fixedPolicyAugmented_current_marginal`: `propext`, `Classical.choice`, `Quot.sound`
  - `historyKernel_stationary_strongLumpability`: `propext`, `Classical.choice`, `Quot.sound`
  - `stationaryCausal_pathLaw_eq_stationaryTrajMeasure`: `propext`, `Classical.choice`, `Quot.sound`
- no nonstandard/project-local proof axiom is introduced.

Research-governance regression, exact-candidate validation, and final `git diff --check` all pass on the exact GCR0 candidate used for the atomic local commit.
