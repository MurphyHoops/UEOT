# RH5 — Certified Homeostatic Margin and No-Go Audit

Status: **FINAL LOCAL PASS**
Tracker: #248
Planning parent: #246
Authorization base: main@c6bb5a82f51dfaf18a354ee4a11687bff40a315f
Prior local stages: RH0 faebae1, RH1 f23fbce, RH2 a3156e5, RH3 4961e3f, RH4 24307a6
Counted-core impact: **NONE**

## Scope

RH5 names the certified scalar load condition and records explicit failure
witnesses for assumptions that are genuinely needed by the RH positive
theorems. The margin is sufficient only; no necessity or sharp phase
transition is claimed.

## Certified scalars

repairCapacityReal epsilon c = (1-epsilon)c.
faultLoadReal epsilon b = epsilon b.

homeostaticMarginReal is capacity minus load, and
homeostaticLoadRatioReal is load divided by capacity.

The machine-checked implications are:
- epsilon<1 and finite positive c imply positive repair capacity;
- positive margin iff load < capacity;
- positive margin implies load ratio < 1.

## No-go witnesses

1. hazard one: certified repair capacity is zero, hence no positive margin;
2. zero repair drift: certified repair capacity is zero, hence no positive
   margin;
3. catastrophicFaultBool: an explicit one-step fault exits a chosen safe
   carrier, showing carrier support closure is a real assumption;
4. infiniteFaultBurdenSystem: the fault row stays in the finite carrier but
   jumps to an infinite-potential state, and no finite FaultBurdenCertificate
   can exist.

These are boundary witnesses, not claims of a universal converse to the RH
sufficient condition.

## Boundary discipline

RH5 does **not** claim:
- a necessary or sharp fault threshold;
- a thermodynamic phase transition;
- pathwise recurrent legitimacy from mean occupation;
- semantic homeostasis;
- repair-law self-reconstruction;
- counted-core or generator changes.

## Local validation

- focused Lean compile of CertifiedHomeostaticMargin.lean: **PASS**;
- lake build UEOT.V3.Compression.Objecthood: **PASS**;
- lake build UEOT.V3.Compression: **PASS** (9117/9117 jobs);
- proof-escape scan: **CLEAR**;
- representative #print axioms: only propext, Classical.choice, Quot.sound;
- research-governance regression: **PASS**;
- exact-candidate Track-O validation: **PASS**;
- final git diff --check: **PASS**.

No RH research branch is pushed in RH5.
