# Track O / ER2 — Repair Rank and Descending Selector Audit

Status: **LOCAL ER2 CLEAR — stage gate passed before commit**

Tracker: #234. Counted-core impact: **NONE**.

## Construction

For a `StrongRepairable` state, `repairRank` is the least repair layer. Outside `K`, minimality forces current membership to arise from the action side of `repairStep`, producing a stationary `descendingRepairAction`.

ER2 proves every support successor has strictly lower repair rank and any path following these support transitions reaches `K` in at most the initial repair rank.

## Boundary

This is a generated stationary support-decreasing selector on the strong basin. No stochastic-shortest-path optimality, discounted-control shortcut, or maximal stochastic repair-basin claim is made.

## Stage gate

ER2 receives its own commit only after focused compile, Objecthood/Compression/full UEOT builds, proof-escape scan, selected axiom audit, governance regression, exact-candidate validation and diff-check are CLEAR.

## Exact validation result

- focused EndogenousRepairRank compile: **PASS**;
- Objecthood root build: **PASS**;
- Compression build: **PASS**;
- full `lake build UEOT`: **PASS — 9112 jobs**;
- Objecthood proof-escape scan: **CLEAR**;
- selected axiom audit (`descendingRepairAction_staysIn_previous`, `repairRank_lt_of_mem_support`, `support_path_hits_by_rank`): only standard `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- exact-candidate governance: **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

ER2 disposition: **CLEAR / eligible for its own local commit**.
