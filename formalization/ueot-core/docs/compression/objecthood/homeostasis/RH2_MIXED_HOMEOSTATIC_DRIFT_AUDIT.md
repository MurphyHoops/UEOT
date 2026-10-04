# RH2 — Mixed Homeostatic Drift Audit

Status: **FINAL LOCAL PASS**
Tracker: #248
Prior local stages: RH0 `faebae1`, RH1 `f23fbce`
Counted-core impact: **NONE**

## Scope

RH2 proves the one-step recurrent-fault drift budget required by #248.  It
combines the explicit RH0 repair/fault mixture with an RH1
`FaultBurdenCertificate`.  It does not yet telescope over time or state any
long-run homeostatic occupation claim.

## Exact mixed expectation

`recurrentFaultMix_lintegral` proves, for the finite PMF mixture,

`E_H W = (1-epsilon) E_Q W + epsilon E_F W`.

The equality is proved directly in ENNReal by finite PMF expansion; no
subtraction, invariant law, or mixing assumption is used.

## Generic one-step drift

`RecurrentHomeostasisSystem.damagePenalty` is zero on legitimate states and
uses the declared repair drift on damaged states.

`mixedHomeostaticDrift` proves

`E_H W + (1-epsilon) * damagePenalty <= W + epsilon * b`

from only:

- the repair-side one-step drift budget;
- the RH1 fault-burden inequality;
- the RH0 explicit convex mixture.

This is the exact local budget frozen by #248/RH2.

## Objecthood specialization

`autonomousRepairDamagePenalty` and
`autonomousRepair_global_drift_budget` show that the existing autonomous
repair dynamics satisfies the required repair-side inequality globally:
outside legitimacy this is the O5/AR drift inequality, while on legitimate
states the repair process stays legitimate and the existing repair potential is
zero.

`objecthood_mixedHomeostaticDrift` therefore specializes the generic RH2
budget to the GCR-complete Objecthood carrier with

- Q = existing autonomous repair;
- F = explicit RH fault kernel;
- epsilon = explicit hazard;
- W/c = unchanged maximal repair certificate data;
- b = RH1 fault burden.

## Boundary discipline

RH2 does **not** infer:

- any finite-horizon or asymptotic damaged occupation bound;
- existence/uniqueness of an invariant law;
- pathwise recurrent legitimacy;
- semantic homeostasis;
- a necessary or sharp threshold;
- repair-law self-reconstruction.

## Local validation

- focused Lean compile: **PASS**;
- Objecthood build: **PASS**;
- Compression build: **PASS** (`9114/9114` jobs);
- proof-escape: **CLEAR**;
- representative `#print axioms`: only
  `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- exact-candidate Track-O validation: **PASS**;
- `git diff --check`: **PASS**.

No RH research branch is pushed in RH2.
