# RH0 — Recurrent-Fault System and GCR Repairable Carrier Audit

Status: **FINAL LOCAL PASS**
Tracker: #248
Planning parent: #246
Authorization base: `main@c6bb5a82f51dfaf18a354ee4a11687bff40a315f`
Counted-core impact: **NONE**

## Scope

RH0 introduces only the finite recurrent-fault system and the GCR-complete
repairable carrier required by #248.  It does not introduce fault burden,
mixed drift, long-run occupation, recurrent-legitimacy, semantic homeostasis,
or any RLSR mechanism.

## Typed recurrent-fault system

`RecurrentHomeostasisSystem Z` keeps the following data separate:

- legitimate set `L`;
- retained carrier `B`;
- repair kernel `Q`;
- fault kernel `F`;
- hazard `epsilon : NNReal` with `epsilon <= 1`;
- repair potential `W`;
- positive/non-top repair drift `c`;
- support closure of both Q and F inside B.

`recurrentFaultMix` is an explicit finite `PMF.ofFintype` convex mixture.
`recurrentFaultMix_apply` machine-checks the exact pointwise formula

`H(z) = (1-epsilon) Q(z) + epsilon F(z)`.

`RecurrentHomeostasisSystem.mixed_stays_carrier` proves that the mixed row
preserves B whenever both component rows preserve B.

## GCR-complete Objecthood carrier

`gcrHomeostaticCarrier P K` is the constitutive lift of the full
GCR-complete repairable set:

`{z | GeneralCausalAlmostSureRepairable P K z.1}`.

This is not a new repairability class.  It reuses the GCR6 equivalence and the
unchanged AR maximal certificate.

Machine-checked bridges:

- `legitimate_subset_gcrHomeostaticCarrier`;
- `autonomousRepairLift_staysIn_gcrHomeostaticCarrier`;
- `autonomousRepairPotential_ne_top_on_gcrHomeostaticCarrier`.

Thus the existing autonomous repair dynamics preserves the full GCR carrier
and its existing repair potential is finite on that carrier.

## Objecthood specialization

`objecthoodRecurrentHomeostasisSystem` fixes:

- Q = existing `autonomousRepairLift`;
- L = existing `legitimateConstitutiveDomain`;
- W = existing `autonomousRepairPotential`;
- c = drift of the unchanged `maximalStationaryRepairCertificate`;
- B = `gcrHomeostaticCarrier`;
- F and epsilon remain explicit RH inputs.

The only new admissibility condition on F is support closure inside B.
Faults that exit B remain outside the positive RH theorem, exactly as required
by #248/P5.

## Boundary discipline

RH0 does **not** claim:

- a finite fault burden;
- the mixed drift inequality;
- finite-horizon or asymptotic occupation control;
- pathwise recurrent legitimacy;
- semantic homeostasis;
- repair-law self-reconstruction;
- a necessary/sharp phase transition;
- a fifth generator or counted-core change.

S/H/X sources, ledger, coverage, theorem index and prior O/ER/AR/GCR evidence
are unchanged.

## Local validation

- focused Lean compile of `RecurrentFaultSystem.lean`: **PASS**;
- `lake build UEOT.V3.Compression.Objecthood`: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS** (`9112/9112` jobs);
- proof-escape scan: **CLEAR**;
- representative `#print axioms` for carrier/mixed-kernel bridges:
  only `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- final exact-candidate Track-O validation: **PASS**;
- final `git diff --check`: **PASS**.

No RH research branch is pushed in RH0.
