# Track O / ER3 — Endogenous Physical Repair Certificate Audit

Status: **LOCAL ER3 CLEAR — stage gate passed before commit**

Tracker: #234. Counted-core impact: **NONE**.

## Construction

Define the ENNReal repair potential as the least repair rank on `StrongRepairable` states and `infinity` outside. Under the ER2 descending selector, the next-state support lies one layer lower, yielding unit expected Lyapunov drift.

ER3 constructs `endogenousPhysicalRepairCertificate P K : PhysicalRepairCertificate P K`, proves its finite-potential basin is exactly `{x | StrongRepairable P K x}`, and reuses the existing O4/P-REC interface to derive `expectedHittingTime <= repairRank` and almost-sure eventual hitting.

## Scientific advance

On the strong finite repair basin, O4/O5 no longer need a user-supplied physical repair certificate: repair policy, basin, rank potential and unit-drift certificate are generated from `P` and `K`.

## Boundaries

ER3 does not claim the strong basin is the maximal stochastic repair basin; it does not use discounted P-CTL as a repair theorem; and it does not address recurrent faults, semantic-recovery dynamics, repair-law self-reconstruction, autopoiesis, or a fifth counted generator.

## Stage gate

ER3 receives its own commit only after focused compile, Objecthood/Compression/full UEOT builds, proof-escape scan, selected axiom audit, governance regression, exact-candidate validation and diff-check are CLEAR.

## Exact validation result

- focused EndogenousRepairCertificate compile: **PASS**;
- Objecthood root build: **PASS**;
- Compression build: **PASS**;
- full `lake build UEOT`: **PASS — 9113 jobs**;
- Objecthood proof-escape scan: **CLEAR**;
- selected axiom audit (`endogenousRepair_drift`, `endogenousPhysicalRepair_basin_eq`, `endogenous_expectedHittingTime_le_rank`, `endogenous_eventually_hits_ae`): only standard `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- exact-candidate governance: **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

ER3 disposition: **CLEAR / eligible for its own local commit**.
