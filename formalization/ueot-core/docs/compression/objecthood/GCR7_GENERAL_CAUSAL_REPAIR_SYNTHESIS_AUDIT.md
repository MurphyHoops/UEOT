# GCR7 — General-Causal Repair Synthesis Audit

Status: **FINAL LOCAL PASS**
Tracker: #243
Planning parent: #242
Governance base: `main@a2fd6f431e6ef891bc5b233d87a4cc884bcf9129`
Prior local stages: GCR0 `4c87558`, GCR1 `83d28d6`, GCR2 `611706c`,
GCR3 `9c75f5c`, GCR4 `2aec086`, GCR5 `a1cb1ec`, GCR6 `6be0695`
Counted-core impact: **NONE**

## Scope

GCR7 feeds the GCR6 general-causal/stationary equivalence back into the
existing AR7 Objecthood repair architecture.  It does not construct a new
repair controller, certificate, deletion primitive, or generator.

The unchanged AR3 maximal deterministic stationary certificate is shown to
already have the full general-causal semantics now proved by GCR6.

## Basin identification

`maximalStationaryRepairCertificate_basin_eq_generalCausalRepairableSet`
proves

`(maximalStationaryRepairCertificate P K).basin =
  {x | GeneralCausalAlmostSureRepairable P K x}`.

The proof is an exact composition of:

1. AR7
   `maximalStationaryRepairCertificate_basin_eq`, identifying the same basin
   with the deterministic-stationary finite-expected-hitting repairable set;
2. GCR6
   `generalCausalRepairableSet_eq_deterministicStationaryRepairableSet`.

No new maximality argument is introduced.

`mem_maximalStationaryRepairCertificate_basin_iff_generalCausal` exposes the
same result pointwise for downstream synthesis.

## Broad Objecthood repair synthesis

`stochasticObjecthood_generalCausalRepair_synthesis` upgrades the AR7
structural package so that its maximal basin is stated directly as the exact
general-causal repairable set while retaining:

- target inclusion;
- one-step support closure outside the target;
- inclusion of every `StrongRepairable` state;
- the constructive repair-rank upper bound on the optimal stationary hitting
  value.

Thus GCR6 changes the proven *semantics of the basin*, not the architecture that
realizes it.

## Deletion/autonomous-repair resynthesis

`generalCausalRepairable_failure_restores_legitimate` accepts a damaged state
that is repairable by an arbitrary admissible causal policy almost surely and
then reuses the unchanged AR7 deletion/autonomous-repair theorem after the
machine-checked GCR6 conversion to the stationary finite-expectation class.

`generalCausalRepairable_eventually_always_legitimate` similarly upgrades the
ER0 conclusion:

general-causal repairability of the physical coordinate implies that the
unchanged maximal AR certificate drives the constitutive process into the
legitimate domain and keeps it there eventually forever.

These are theorem-level resyntheses only; no second repair dynamics or new
Objecthood primitive is created.

## Assumption audit

GCR7 uses the same finite controlled-PMF setting closed by GCR6:

- finite state and action spaces;
- nonempty action space;
- measurable-singleton state/action structures;
- existing AR7 constitutive-state measurability assumptions for the autonomous
  repair wrappers.

It adds no compactness/Feller, irreducibility, recurrence, spectral, energetic,
resource, ontogenetic, or self-reconstruction assumption.

## Boundary discipline

GCR7 does **not**:

- enter RH recurrent homeostasis;
- enter RLSR repair-law self-reconstruction;
- enter EC/OC/AP;
- reopen Track S/H;
- mutate the frozen counted ledger/coverage or four-generator core;
- claim a fifth generator;
- claim complete autopoiesis.

Architecture/deletion classification and residual-boundary review remain the
separate GCR8 obligation.

## Local validation

The exact local candidate passed:

- focused Lean compile of `GeneralCausalRepairSynthesis.lean`: **PASS**;
- Objecthood build: **PASS**;
- Compression build: **PASS** (`9111/9111` jobs);
- proof-escape scan (`sorry|admit|axiom|opaque|unsafe`): **CLEAR**;
- representative `#print axioms` on
  `maximalStationaryRepairCertificate_basin_eq_generalCausalRepairableSet`,
  `stochasticObjecthood_generalCausalRepair_synthesis`,
  `generalCausalRepairable_failure_restores_legitimate`, and
  `generalCausalRepairable_eventually_always_legitimate`: only
  `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression suite: **PASS**;
- exact-candidate Track-O validation: run against the final staged tree before
  the atomic local commit;
- final `git diff --check`: **PASS**.

No research branch is pushed during GCR7.  First push remains after cumulative
GCR0--GCR8 local closure and second-pass audit.
