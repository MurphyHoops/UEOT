# RH6 — Mean Homeostasis vs Pathwise Recurrent Legitimacy Audit

Status: **FINAL LOCAL PASS**
Tracker: #248
Planning parent: #246
Authorization base: main@c6bb5a82f51dfaf18a354ee4a11687bff40a315f
Prior local stages: RH0 faebae1, RH1 f23fbce, RH2 a3156e5, RH3 4961e3f, RH4 24307a6, RH5 67a1fbb
Counted-core impact: **NONE**

## Scope

RH6 fixes the semantic distinction between long-run mean occupation control and
pathwise recurrent legitimacy. It does not strengthen the RH3/RH4 mean theorem
into a pathwise statement.

## Semantics

MeanHomeostasis is an asymptotic Cesaro upper certificate for a sequence of
damaged probabilities.

PathwiseRecurrentLegitimacy requires almost every path to visit the legitimate
set arbitrarily late.

EventuallyAlwaysLegitimate is stronger still and implies
PathwiseRecurrentLegitimacy by a direct pathwise theorem.

RecurrentHomeostasisSystem.meanHomeostasis proves that the RH3 asymptotic
occupation theorem is exactly a MeanHomeostasis certificate.

## Separation witness

twoClassPathMeasure is a normalized path probability law with:
- probability 1/2 on a path that is damaged forever;
- probability 1/2 on a path that is legitimate forever.

For this law:
- damaged probability is exactly 1/2 at every time;
- MeanHomeostasis holds with rho=1/2;
- PathwiseRecurrentLegitimacy fails because the forever-damaged class has
  positive probability.

meanHomeostasis_does_not_imply_pathwiseRecurrent packages this separation.

## Consequence

The RH mean/capacity results cannot be renamed pathwise recurrent repair.
Any later pathwise recurrent-legitimacy theorem must add or derive genuine
path-level structure beyond the mean occupation certificate.

## Boundary discipline

RH6 does **not** claim:
- mean occupation implies infinitely-often repair;
- a unique invariant law or ergodic theorem;
- semantic homeostasis;
- repair-law self-reconstruction;
- a sharp phase transition;
- counted-core or generator changes.

## Local validation

- focused Lean compile of HomeostasisSemantics.lean: **PASS**;
- lake build UEOT.V3.Compression.Objecthood: **PASS**;
- lake build UEOT.V3.Compression: **PASS** (9118/9118 jobs);
- proof-escape scan: **CLEAR**;
- representative #print axioms: only propext, Classical.choice, Quot.sound;
- research-governance regression: **PASS**;
- exact-candidate Track-O validation: **PASS**;
- final git diff --check: **PASS**.

No RH research branch is pushed in RH6.
