# Track O / AR5 — Repair Rank / Canonical Hitting-Time Relation Audit

Status: **LOCAL AR5 CLEAR — stage gate passed before commit**

Tracker: #238. Counted-core impact: **NONE**.

## Result

AR5 connects the earlier strong-repair rank semantics to the new canonical
stationary hitting-time semantics without duplicating the ER proof. For every
`StrongRepairable` state:

- the AR0 canonical certificate potential under `descendingRepairAction` is at
  most the finite `repairRank`;
- the state lies in the descending policy's `StationaryRepairBasin`;
- the AR3 pointwise optimal stationary repair value is also at most
  `repairRank`;
- consequently the state lies in the maximal deterministic-stationary repair
  basin.

## Second-pass review / reflection

- the quantitative inequality is inherited from the already machine-checked
  endogenous certificate theorem rather than reproved with a weaker surrogate;
- the rank is an upper bound on canonical expected hitting time, not asserted
  to be equal to it;
- AR3 minimization can only improve that bound, hence the transitive inequality
  for `stationaryRepairValue` is directionally correct;
- the result preserves AR4's strict separation: stochastic geometric retry may
  have finite expected hitting time even when no finite strong rank exists;
- no statement about general randomized/history-dependent policy completeness
  is introduced before AR6.

Disposition: **CLEAR**.

## Validation

- focused compile and module build: **PASS**;
- Objecthood / Compression / full UEOT builds: **PASS**;
- proof-escape scan: **CLEAR**;
- selected axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression and 3-path governance simulation: **PASS**;
- `git diff --check`: **PASS**.

AR5 disposition: **CLEAR / eligible for its own local commit**.
