# RH1 — FaultBurdenCertificate Audit

Status: **FINAL LOCAL PASS**
Tracker: #248
Prior local stage: RH0 `faebae1`
Counted-core impact: **NONE**

## Scope

RH1 adds only the finite fault-side burden certificate required by #248.
It does not mix repair/fault dynamics and makes no long-run occupation claim.

`FaultBurdenCertificate S` stores a finite `burden = b` and proves, for every
carrier state,

`E_F[W(next) | z] <= W(z) + b`.

## Finite-carrier existence

`exists_finite_uniform_gcrHomeostaticPotential_bound` uses the RH0
GCR-complete finite carrier and the already-proved pointwise non-top autonomous
repair potential to construct one finite uniform carrier bound.

`faultBurdenCertificateOfUniformBound` converts any such uniform finite bound
into a fault-burden certificate when the RH0 fault support remains inside the
carrier.

`nonempty_objecthoodFaultBurdenCertificate` specializes this to the exact
Objecthood RH0 system, so every RH0-admissible recurrent fault kernel has at
least one finite RH1 burden certificate.

This is a sufficient finite-carrier construction, not a claim that arbitrary
faults admit finite burden.

## Boundary discipline

RH1 does **not** prove:

- the mixed kernel drift inequality;
- finite-horizon or asymptotic homeostatic occupation;
- a necessary/sharp load threshold;
- pathwise recurrent legitimacy;
- semantic homeostasis;
- repair-law self-reconstruction.

No historical O/ER/AR/GCR theorem, audit, S/H/X source, counted ledger, coverage
or theorem index is modified.

## Local validation

- focused Lean compile of `FaultBurden.lean`: **PASS**;
- Objecthood build: **PASS**;
- Compression build: **PASS** (`9113/9113` jobs);
- proof-escape scan: **CLEAR**;
- representative `#print axioms`: only
  `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- exact-candidate Track-O validation: **PASS**;
- `git diff --check`: **PASS**.

No RH research branch is pushed in RH1.
