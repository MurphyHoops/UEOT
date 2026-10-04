# QT1 — Least Fault Burden / Strict Separation Audit

Status: **FINAL LOCAL PASS**
Tracker: #253
Authorization base: main@d082ec1cfbde93a22bec0cab19eea539437db9d5
Prior local stage: QT0 ae53e34
Counted-core impact: **NONE**

## Scope

QT1 proves that the QT0 canonical burden is least among all admissible
FaultBurdenCertificate burdens for the same recurrent-homeostasis system and
exhibits a finite strict-separation witness against the prior generic RH1
uniform-bound constructor.

QT1 does not yet propagate this improvement into the downstream load ratio,
homeostatic margin, mean occupation, invariant Cesaro, or same-parent
specializations.

## Least-burden theorem

For any recurrent-homeostasis system S and any
C : FaultBurdenCertificate S,

canonicalFaultBurden S <= C.burden.

The proof is pointwise: every admissible burden C.burden must dominate the
positive single-step fault excess at every retained carrier state; therefore it
must dominate their finite maximum.

Consequently, whenever QT0's direct-finiteness assumption is available,

(canonicalFaultBurdenCertificate S hW).burden <= C.burden.

Thus QT0's certificate is least in the existing RH1 burden interface.

## Strict finite separation

canonicalBurdenStrictWitnessSystem is a finite Bool system whose fault kernel is
the identity and whose potential is 1 on true and 0 on false.

Its true single-step fault excess is identically zero, so

canonicalFaultBurden = 0.

The prior generic RH1 uniform-bound constructor remains valid with the coarse
uniform carrier bound 1, hence it returns burden 1 on the same system.

Therefore QT1 proves a genuine strict improvement witness:

canonical burden 0 < generic automatic burden 1.

This shows the QT refinement is not merely a renaming of the RH1 interface.

## Boundary discipline

QT1 does **not** claim:

- that every previously chosen burden is strictly larger;
- any improvement when an existing certificate is already least;
- a new homeostatic threshold or phase transition;
- pathwise recurrent legitimacy;
- RLSR or autopoiesis;
- counted-core or generator changes.

## Local validation

- focused Lean compile of LeastFaultBurden.lean: **PASS**;
- lake build UEOT.V3.Compression.Objecthood: **PASS**;
- lake build UEOT.V3.Compression: **PASS** (9122/9122 jobs);
- proof-escape scan: **CLEAR**;
- representative #print axioms: only propext, Classical.choice, Quot.sound;
- research-governance regression: **PASS**;
- final exact-candidate Track-O validation: **PASS**;
- final git diff --check: **PASS**.

No QT research branch is pushed in QT1.
