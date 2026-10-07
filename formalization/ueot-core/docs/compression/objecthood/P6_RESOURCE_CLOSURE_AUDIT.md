# P6 Resource Closure and Starvation Boundaries — Local Closure Audit

Status: **LOCAL THEOREM PROGRAM COMPLETE; REMOTE INTEGRATION PENDING**

Track: `O / Theory Completion P6`

Tracker: `#283`

Canonical working base: `main@fe211cbccdf5a19fedccf185f54f46ff6345ff19`

P5 scientific merge ancestor: `2ebe203a684e21ede5b21d95ab3cd03edd461b9c`

Post-recompression scientific head before this audit record:
`9e95c4d1bd4c444d5fba38a3f3d0f25b1cd09c95`

P6 is L1 additive, uncounted Track-O research. It does not mutate frozen Core
v3, counted 106/106 coverage, counted compression evidence, completed P5/RH/RLSR
source, or the frozen minimal core
`{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

## 1. Scientific architecture

P6 adds a resource-accounting layer **after** P5 joint same-parent homeostasis.
It does not reinterpret P5's Lyapunov drift as a resource stock.

The final architecture has four distinct levels:

1. **generic accounting semantics** — explicit initial stock, replenishment,
   realized cost, cumulative balance and deterministic/pathwise viability;
2. **P5 state-cost adapter** — maintenance plus nonnegative repair and
   reconstruction surcharges, with actual expected state cost bounded by joint
   damaged occupation;
3. **mean / finite-horizon expected closure** — P5 homeostasis controls mean and
   cumulative schedules of expected accounting cost;
4. **realized pathwise closure** — obtained only from a separate pointwise
   affordability premise on the realized cost schedule.

These levels are intentionally not identified with one another.

Resource quantities remain abstract real-valued accounting units. No P6 theorem
identifies them with thermodynamic energy, work, free energy, ATP, money,
compute, or any other domain quantity without a later explicit adapter.

## 2. Stage results

| Stage | Checkpoint | Result | Claim class |
|---|---|---|---|
| P6.0 | `8023c8e` | abstract resource-cost model; cumulative balance; deterministic/pathwise `ResourceViable`; pointwise affordability sufficient criterion | DEFINITION / THEOREM |
| P6.1 | `1bddbc5` | state-level maintenance/repair/reconstruction cost envelope; program mismatch lies inside P5 damage; PMF expected-cost bound | THEOREM / ADAPTER_INTERFACE |
| P6.2 | `26bcaae` | P5 mean homeostasis → eventual mean actual accounting cost below supply under strict steady-load slack | CONDITIONAL_THEOREM |
| P6.3 | `ca1bbb0` | finite-horizon transient+steady resource envelope and expected-accounting viability under explicit reserve/supply inequalities | CONDITIONAL_THEOREM |
| P6.4 | `8023c8e` reused | stronger realized/pathwise criterion already canonical in P6.0; no duplicate theorem family created | THEOREM / REUSE |
| P6.5 | `52b73a6` | constant-deficit starvation; mean sustainability ≠ pathwise viability; explicit equal-prior PMF expected-accounting closure ≠ pathwise viability | NO_GO_BOUNDARY |
| P6.6 | `69f4109` | same-parent P5 semantic/constitutive homeostasis + P6 mean and finite expected-resource closure | CONDITIONAL_THEOREM |
| P6.7 | `918eb8e` | terminal same-parent theorem adds realized pathwise viability only under a separate pointwise realized-cost affordability assumption | CONDITIONAL_THEOREM |
| post-P6 recompression | `9e95c4d` | restore state-cost nonnegativity theorem, remove duplicate no-go surface, decouple generic accounting from P5 imports | ARCHITECTURE TIGHTENING |

## 3. Recompression and adversarial-audit decisions

### 3.1 P5 drift is not a resource stock

P5/RH `repairDrift`, fault burden and homeostatic potential are Lyapunov/control
quantities. P6 therefore introduces independent accounting coordinates:
`maintenance`, `repair`, `reconstruction`, replenishment and initial reserve.
They enter resource theorems only through explicit algebraic bridges.

### 3.2 Generic accounting is independent of P5

The first draft of `ResourceAccounting.lean` imported the whole P5
`JointHomeostasis` root although none of its definitions needed P5.
Post-P6 recompression removes that false dependency. The dependency now begins
only in `StateCostEnvelope.lean`, where P5 joint legitimacy and program mismatch
are genuinely consumed.

The dependency direction is therefore:

`generic accounting → P5 state adapter → mean/finite resource closure → same-parent synthesis`.

### 3.3 State cost nonnegativity is explicit

The mission required a nonnegative state cost. The initial P6.1 surface had the
nonnegative cost-model fields and envelope theorem but no public theorem stating
the instantiated state cost itself is nonnegative.

Post-P6 audit added:

- `realIndicator_nonneg`;
- `stateResourceCost_nonneg`.

This closes the basic accounting invariant without adding a physical-unit
interpretation.

### 3.4 Program reconstruction cost is not double-counted outside damage

The state-level envelope charges:

- maintenance always;
- repair surcharge outside joint legitimacy;
- reconstruction surcharge on explicit program-organization mismatch.

`jointProgramMismatch_not_jointLegitimate` proves the mismatch event lies
inside the broader P5 damaged event. Hence the combined surcharge is bounded by
one damaged-mass term without asserting that repair and reconstruction are the
same mechanism.

### 3.5 Mean resource sustainability remains only a Cesaro statement

P6.2 consumes P5 `MeanHomeostasis`. A strict steady-load inequality

`maintenance + variableCost * rho < supply`

makes the Cesaro mean of **actual expected state costs** eventually less than
constant supply. It says nothing by itself about cumulative stock on every
realized path.

The front-loaded spike witness machine-checks this separation: its long-run
mean cost tends to zero while zero initial reserve with unit replenishment
fails immediately.

### 3.6 Expected-accounting closure remains weaker than pathwise viability

P6.3 proves `ResourceViable` for the deterministic schedule of **expected** P5
state costs. That is a finite-horizon expected-accounting statement, not a
realized stochastic-path statement.

P6.5 strengthens the boundary with an explicit equal-prior `PMF Bool`: expected
cumulative balance is nonnegative at every horizon, while one realized path
still violates the cumulative constraint. The earlier arithmetic-average
terminal no-go was removed as redundant; only its computation lemma is retained
under the genuine PMF theorem.

### 3.7 P6.4 is reuse, not a missing stage

The stronger deterministic/pathwise resource criterion was already proved in
P6.0:

`resourceViable_of_pointwise_cost_le_replenish`.

Creating a second P6.4 theorem family would duplicate the same accounting
result. P6.7 instead reuses this canonical criterion only after adding an
explicit realized-cost premise.

### 3.8 Finite reserve cleanly separates transient debt and steady load

P6.3 derives the cumulative expected cost bound

- transient term: `variableCost * V0 / kappa`;
- steady term: `maintenance + variableCost * lambda / kappa`.

Initial reserve covers the transient term; replenishment covers the steady
term. This is a direct consequence of the existing P5/RH finite-horizon damaged
occupation budget, not a new homeostasis algebra.

### 3.9 Terminal pathwise closure requires new information

`p6_terminal_sameParent_resourceClosure` first consumes the P6.6 same-parent
mean/expected synthesis. It then adds a realized schedule only under the
separate premise

`∀ n, realizedCost n ≤ supply`.

Only this extra realized-cost premise licenses pathwise `ResourceViable`.
Therefore P6 terminal closure does not silently upgrade means or expectations
to almost-sure/pathwise stock guarantees.

## 4. What P6 now closes

For the finite same-parent benchmark inherited from P5, with an explicit P6
accounting model, P6 now provides:

- nonnegative maintenance/repair/reconstruction accounting costs;
- explicit cumulative stock/replenishment semantics;
- deterministic/pathwise resource viability criterion;
- P5 state-cost envelope controlled by joint damaged probability;
- asymptotic mean actual-resource closure under strict steady-load slack;
- finite-horizon transient+steady cost bounds;
- finite-horizon expected-accounting viability under reserve/supply bounds;
- constant-deficit starvation theorem;
- mean-vs-pathwise and expectation-vs-pathwise counterexamples;
- same-parent resource-maintenance synthesis preserving P5 constitutive and
  semantic interpretation;
- terminal pathwise closure only when realized costs are separately certified
  affordable.

## 5. Nonclaims

P6 does not prove:

- thermodynamic energy, work, free energy, ATP, money or compute semantics from
  abstract resource accounting;
- pathwise no-starvation from mean homeostasis alone;
- pathwise no-starvation from expected-accounting closure alone;
- unlimited or free resource replenishment;
- ontogenetic self-construction from seed/components — P7;
- arbitrary uncorrectable repair-program damage;
- reconstruction of the trusted execution/codec/dynamics/object specification;
- infinite/general-state resource closure;
- counted-core promotion.

P7 ontogenetic construction remains a logically separate capability. Resource
closure can support construction once a construction mechanism exists, but it
does not itself create such a mechanism.

## 6. Local validation evidence

At post-recompression scientific head
`9e95c4d1bd4c444d5fba38a3f3d0f25b1cd09c95`:

- complete P6 proof-escape scan: **CLEAR**;
- `git diff --check`: **PASS**;
- exact Track-O governance validator: **PASS**;
- complete governance regression suite: **PASS**;
- representative axiom audit on nine P6 endpoints: only standard
  `[propext, Classical.choice, Quot.sound]`;
- `lake build UEOT.V3.Compression`: **PASS, 9208 jobs**;
- `lake build UEOT`: **PASS, 9227 jobs**.

P6.5, P6.6 and P6.7 were additionally rebuilt from detached exact stage heads
using only the shared untracked Lake cache. Earlier P6 stages were committed as
independent local checkpoints before later stages were started.

## 7. Remote gate still pending

This audit does **not** mark P6 closed. Closure still requires the single final
branch push, one coherent PR, exact-head Base Policy/governance, exact-head Core
Lean and Compression Guard, one independent exact-head review, merge,
resulting-main Core Lean + Compression Guard, tracker closure and branch
retirement.

Only after those gates may Theory Completion advance from P6 to P7.
