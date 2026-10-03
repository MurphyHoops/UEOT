# Track O / AR7 — Stochastic Objecthood Synthesis + Architecture/Deletion Audit

Status: **LOCAL AR7 CLEAR — AR0--AR7 scientific cycle closed locally**

Tracker: #238. Counted-core impact: **NONE**.

## 1. End-to-end synthesis

AR7 composes the AR0--AR6 theorem surface with the pre-existing O5/O6
Objecthood recovery/deletion architecture. The terminal stationary synthesis
proves, for the single AR3 maximal deterministic-stationary policy:

1. the target is contained in its finite-expected-hitting basin;
2. that basin is support-closed outside the target under the selected policy;
3. the basin is exactly the union of all deterministic-stationary
   finite-expected-hitting repair basins;
4. every prior `StrongRepairable` state belongs to the maximal basin;
5. on the strong basin, the pointwise optimal stationary expected hitting value
   is bounded above by the constructive `repairRank`.

The strict AR4 geometric-retry witness is also retained, so this synthesis is a
genuine stochastic enlargement of the prior strong support-decreasing basin.

## 2. Deletion-to-autonomous-repair bridge

`stationaryRepairable_failure_restores_legitimate` is the terminal operational
bridge. If a failing deletion realizes a physical state that is repairable by
some deterministic stationary policy with finite canonical expected hitting
time, then AR3's single maximal certificate supplies the O5/O6 repair
certificate required by the existing autonomous constitutive dynamics.

The resulting theorem simultaneously returns:

- a P-OMG minimal destructive deletion witness contained in the observed
  failing deletion; and
- almost-sure eventual return of the damaged constitutive state to the existing
  legitimate constitutive domain.

No new failure primitive, target, controller lift, parent selector, or repair
transition architecture is introduced.

## 2A. ER0 eventual-always closure

The cumulative second-pass review found that the first AR7 implementation only
reconnected the stochastic basin to O5/O6 eventual legitimacy. That was weaker
than the #238 AR7 contract, which explicitly requires reconnection to ER0
eventual-always legitimacy.

The final AR7 source therefore adds
`stationaryRepairable_eventually_always_legitimate`: every damaged constitutive
state that is finite-expected repairable under some deterministic stationary
policy enters the legitimate constitutive domain under the single AR3 maximal
certificate and, almost surely, stays there from some finite time onward.

This theorem is derived by converting deterministic-stationary repairability to
membership in the AR3 maximal certificate basin and then invoking the existing
ER0 theorem `autonomousRepair_eventually_always_legitimate_ae`. No recurrent
fault assumption or new homeostatic dynamics is introduced.

## 2B. Same formed parent and semantic restoration

The same second-pass review also identified that a generic P/K deletion theorem
was not by itself enough to satisfy #238's explicit O7 reconnection requirement.
The final source now provides:

- `canonicalSelfRepairingOperationalParent`, which takes an already formed
  `OperationalFormedPersistentParent` and fills its O7 physical-repair field
  with the AR3 maximal stationary certificate for that exact parent's stored
  dynamics and persistence kernel;
- `stationaryRepairable_failingDeletion_eventually_always_same_parent`, which
  combines the P-OMG minimal deletion witness with ER0 eventual-always return to
  the legitimate constitutive domain of that exact selected formed parent;
- `canonical_semantic_bound_and_eventually_always_same_parent_repair`, which
  retains the existing Track-X robust long-run semantic bound for the same
  parent completion while the canonical maximal repair dynamics return the
  damaged constitutive state to that parent's legitimate domain eventually
  forever.

These additions close the literal #238 target chain without changing the parent
selector, semantic kernel, persistence target, or autonomous repair lift.

## 3. AR0--AR7 architecture classification

The classification remains theorem-granular and uncounted:

| Stage | Principal role | Architecture classification |
| --- | --- | --- |
| AR0 | canonical expected hitting time -> fixed-policy physical repair certificate | G1/G2 retained-interface synthesis |
| AR1 | target inclusion + positive-support closure of finite-hitting basin | G1 structural bridge |
| AR2 | statewise two-policy patching with basin-union certificate | G2 conditional synthesis |
| AR3 | one policy realizing the union of all deterministic-stationary finite-hitting basins | G2 synthesis |
| AR4 | strong-basin inclusion + geometric-retry strict separation | G1 bridge + G3 boundary evidence |
| AR5 | constructive repair rank -> canonical hitting-time upper bound | G1 quantitative bridge |
| AR6 | exact arbitrary-causal path-law comparison class; general-to-stationary implication left explicit | G3 boundary |
| AR7 | maximal stochastic repair + deletion/autonomous-repair resynthesis | G2 end-to-end synthesis |

Nothing in AR0--AR7 supplies the independent multi-family generativity or
nonredundancy evidence required to promote a fifth counted G0 generator.

## 4. Deletion / nonredundancy audit

The AR cycle changes the *repairability semantics*, not the frozen generator
architecture.

- The prior P-REC hitting-time machinery remains indispensable. AR0 and AR3 use
  its exact first-step identity rather than replacing it.
- The P-PER persistence target remains indispensable to the existing O5/O6
  legitimate constitutive-domain construction used by AR7.
- P-OMG remains diagnostic rather than generative: AR7 consumes the existing
  minimal-failure theorem but repairability still arrives independently from
  the stochastic repair basin.
- The existing autonomous repair lift remains indispensable. AR7 injects a
  stronger canonical certificate into that architecture rather than creating a
  second autonomous dynamics.
- `StrongRepairable`, `repairRank`, and the endogenous descending certificate
  are not obsolete: AR4 proves the strong class is a strict sufficient
  subdomain, while AR5 preserves its constructive finite-step/rank guarantee.
- AR2 is not a new primitive and is not logically required to state AR3's final
  maximality theorem; it remains a useful constructive two-policy patching
  theorem/API. This is adapter-level redundancy, not evidence for deleting a
  counted source family.
- AR6's general-causal comparison semantics cannot be deleted if the G3
  boundary is to remain exact. Conversely, no unproved
  `GeneralCausalToStationaryCompleteness` bridge is inserted into the synthesis.

Therefore no existing counted theorem, source family, or frozen O/ER result is
made redundant by AR0--AR7, and no deletion of frozen architecture is justified
by this cycle.

## 5. Explicit boundary after AR7

AR7 closes exactly the authorized deterministic-stationary stochastic-repair
program. It does **not** claim that arbitrary complete-history randomized
almost-sure repairability coincides with finite-expected deterministic-
stationary repairability. `GeneralCausalToStationaryCompleteness` remains the
precise G3 theorem boundary recorded by AR6.

Likewise, AR7 does not enter recurrent homeostasis or repair-law
self-reconstruction. The repair-producing transition law/interpreter remains
intact external dynamics, exactly as required by the #238 authorization.

## 6. Counted-core / path audit

AR0--AR7 add only Objecthood Lean modules, Objecthood audit documents, and
imports in the public `Objecthood.lean` root. They do not alter the frozen
counted four-generator ledger, compression coverage, mission contract,
governance configuration, Track S/H source modules, workflows, or any frozen
106-theorem source theorem.

The correct architectural verdict therefore remains:

> **uncounted G2 stochastic self-repair synthesis with retained G1 bridges and
> an explicit G3 general-causal completeness boundary; no fifth G0 generator.**

## 7. AR7 stage-gate result

- focused `StochasticRepairSynthesis.lean` compile/module build: **PASS**;
- Objecthood root build: **PASS**;
- Compression build: **PASS**;
- full `lake build UEOT`: **PASS**;
- AR7 proof-escape scan: **CLEAR**;
- representative AR7 axiom audit of the terminal stationary synthesis,
  maximal-certificate basin theorem, deletion/autonomous-repair theorem,
  ER0 eventual-always closure, same-parent semantic-restoration theorem, and
  strict-separation theorem: only `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- three-path stage governance simulation: **PASS**;
- `git diff --check`: **PASS**.

## 8. Local-cycle disposition

AR0--AR7 are now scientifically and formally closed at the local stage level.
The required cumulative second-pass audit also passed on the eight-stage local
head:

- eight atomic AR commits are present in order, one for each AR0--AR7 stage;
- public Objecthood, Compression, and full `UEOT` builds: **PASS**;
- proof-escape scan across all eight new AR Lean modules: **CLEAR**;
- representative axiom audit spanning AR0--AR7: only `propext`,
  `Classical.choice`, `Quot.sound`;
- exact-HEAD research-governance validation: **PASS — 17 changed paths**;
- research-governance regression suite: **PASS**;
- cumulative `git diff --check`: **PASS**;
- counted ledger, coverage, research tracker, post-FINAL governance, mission,
  hierarchy/cross-track source roots, and workflows: **UNCHANGED**;
- AR source contains no RH/RLSR implementation or fifth-G0 claim;
- roadmap reconciliation: the second pass detected and repaired the initial AR7
  omission of the explicit ER0 eventual-always and O7 same-parent semantic
  restoration surfaces before final promotion;
- authorization PR #239 resulting-main Core Lean `37103661699` and Compression
  Guard `37103661702` on merge commit
  `85846436f56804fd28a6ce33fc5c65dc4aa0b9bb`: **SUCCESS**.

The single research branch is therefore eligible for its **first** remote push
and exact-head CI/review. No research commit was published before this local
closure point.

AR7 disposition: **CLEAR**.
