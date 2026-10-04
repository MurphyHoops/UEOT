# RH3 — Finite-Horizon and Mean Damaged-Occupation Audit

Status: **FINAL LOCAL PASS**
Tracker: #248
Planning parent: #246
Authorization base: main@c6bb5a82f51dfaf18a354ee4a11687bff40a315f
Prior local stages: RH0 faebae1, RH1 f23fbce, RH2 a3156e5
Counted-core impact: NONE

## Scope

RH3 converts the RH2 local drift budget into finite-horizon and asymptotic mean
damaged-occupation control. It does not use or claim invariant-law uniqueness,
irreducibility, mixing, pathwise recurrent legitimacy, or semantic homeostasis.

## Carrier-aware marginal dynamics

homeostaticMarginal is the exact repository stationaryStateLaw for the RH0
mixed kernel. homeostaticMarginal_staysIn proves that an initial PMF supported
inside the retained carrier remains supported there at every finite time.

pmf_oneStep_drift_on_carrier integrates a pointwise drift inequality only on
the current PMF support. This is essential: RH1 burden and RH2 mixed drift are
not silently strengthened outside the authorized GCR carrier.

## Finite-horizon occupation telescope

damagedIndicatorENNReal is the exact 0/1 damaged-state observable.

finiteHorizonDamagedOccupation_on_carrier combines:
- exact PMF bind expectation;
- support propagation inside the RH0 carrier;
- the RH2 pointwise drift budget;
- a no-subtraction ENNReal telescope.

RecurrentHomeostasisSystem.finiteHorizonDamagedOccupation yields

kappa * sum_{t<N} P(Z_t outside L)
<= E[W_0] + N * lambda,

with kappa = (1-epsilon)c and lambda = epsilon b.

objecthood_finiteHorizonDamagedOccupation specializes the result to the full
GCR-complete Objecthood carrier and the unchanged autonomous repair dynamics.

## Asymptotic mean bound

real_average_bound_of_ennreal_homeostatic_budget and
mean_homeostasis_of_ennreal_budget convert the finite ENNReal telescope into a
real finite-average and eventual mean bound under exact finiteness and positive
capacity assumptions.

RecurrentHomeostasisSystem.eventually_realDamageAverage_le requires:
- potential finite on the retained carrier;
- epsilon < 1, so certified repair capacity is nonzero.

objecthood_eventually_realDamageAverage_le discharges carrier-potential
finiteness from RH0 and uses only epsilon < 1 as the extra scalar condition.

This is a sufficient long-run mean-occupation certificate, not a sharp or
necessary phase transition.

## Boundary discipline

RH3 does not claim:
- invariant or Cesaro limit semantics;
- pathwise infinitely-often legitimacy;
- semantic identity during damaged periods;
- repair-law self-reconstruction;
- a fifth generator or counted-core change.

## Local validation

- focused Lean compile of FiniteHorizonHomeostasis.lean: **PASS**;
- lake build UEOT.V3.Compression.Objecthood: **PASS**;
- lake build UEOT.V3.Compression: **PASS** (9115/9115 jobs);
- proof-escape scan: **CLEAR**;
- representative #print axioms: only propext, Classical.choice, Quot.sound;
- research-governance regression: **PASS**;
- final exact-candidate Track-O validation: **PASS**;
- final git diff --check: **PASS**.

No RH research branch is pushed in RH3.
