# QT0 — Canonical Fault Excess / Direct-Finiteness Audit

Status: **FINAL LOCAL PASS**

Tracker: #253
Authorization base: main@d082ec1cfbde93a22bec0cab19eea539437db9d5
Stage: QT0
Counted-core impact: **NONE**

## Scope

QT0 introduces only the canonical fault-burden core authorized by #253. It does
not yet prove leastness against arbitrary certificates (QT1), downstream
quantitative tightening (QT2), Objecthood specializations (QT3), or any new RH
semantics.

## Construction

For a finite recurrent-homeostasis system S and state z,

faultExcess S z = E_F[W(next) | z] - W(z)

using ENNReal truncated subtraction.

canonicalFaultBurden S is the finite-state maximum of faultExcess over the
declared carrier, with zero off-carrier.

The carrier-support contract from RH0 and pointwise finiteness of W on the
carrier imply:

- every fault-row potential expectation is finite;
- every carrier fault excess is finite;
- the finite maximum canonicalFaultBurden is finite.

The exact additive identity property of truncated subtraction yields

E_F[W(next) | z] <= W(z) + canonicalFaultBurden S

for every carrier state. Hence canonicalFaultBurdenCertificate constructs a
valid RH1 FaultBurdenCertificate directly from the existing carrier and
potential-finiteness assumptions.

No auxiliary seed certificate or arbitrary uniform bound is required.

## Boundary discipline

QT0 does **not** claim:

- that canonicalFaultBurden is least among all certificates (QT1);
- strict improvement over the RH1 generic constructor (QT1);
- improved RH load ratio or occupation bounds (QT2);
- new Objecthood / same-parent consequences (QT3);
- pathwise recurrent legitimacy;
- a sharp/necessary phase transition;
- RLSR, EC, OC, AP, counted-core mutation, or a fifth generator.

## Integration issue found and fixed

The first aggregate Objecthood build exposed an internal declaration collision
from an anonymous local DecidableEq instance. The instance is now explicitly
named canonicalFaultBurdenDecidableEq. This changes no theorem statement and
removes the aggregate-import collision.

## Local validation

- focused Lean compile of CanonicalFaultBurden.lean: **PASS**;
- lake build UEOT.V3.Compression.Objecthood: **PASS**;
- lake build UEOT.V3.Compression: **PASS** (9121/9121 jobs);
- proof-escape scan: **CLEAR**;
- representative #print axioms: only propext, Classical.choice, Quot.sound;
- research-governance regression: **PASS**;
- final exact-candidate Track-O validation: **PASS**;
- final git diff --check: **PASS**.

No QT research branch is pushed in QT0.
