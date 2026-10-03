# Track O / ER1 — Strong Controlled Repair Attractor Audit

Status: **LOCAL ER1 CLEAR — stage gate passed before commit**

Tracker: #234. Counted-core impact: **NONE**.

## Construction

`R_0 = K` and `R_(n+1) = R_n union {x | exists a, StaysIn (P x a) R_n}`.

ER1 proves monotone outward growth, finite stabilization on a finite state space, permanence after the first adjacent fixed layer, and equality between the stabilized layer and `StrongRepairable`.

## Boundary

This is a support-wise / sure finite repair basin. It is not claimed to equal the maximal stochastic almost-sure repair basin. A chain with positive self-loop probability can be almost-surely repairable while failing strict support descent.

ER1 imports only the finite viability-kernel interface; it does not assume O4/P-REC repair certificates.

## Stage gate

ER1 receives its own commit only after focused compile, Objecthood/Compression/full UEOT builds, proof-escape scan, selected axiom audit, governance regression, exact-candidate validation and diff-check are CLEAR.

## Exact validation result

- focused StrongRepairAttractor compile: **PASS**;
- Objecthood root build: **PASS**;
- Compression build: **PASS**;
- full `lake build UEOT`: **PASS — 9111 jobs**;
- Objecthood proof-escape scan: **CLEAR**;
- selected axiom audit (`exists_repairIter_fixed`, `repairIter_add_eq_of_fixed`, `exists_strongRepairBasin_fixed`): only standard `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- exact-candidate governance: **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

ER1 disposition: **CLEAR / eligible for its own local commit**.
