# UEOT Core v3.0 — High-Throughput Parallel Lean Formalization Plan

This document is the execution plan for completing the machine-checked
formalization of all 106 source P-IDs in `UEOT_Core_Mathematics_v3.0_Complete.md`.

> **Live state is not maintained here.** Read `docs/FORMALIZATION_STATE.md`
> first for branch heads, Actions, PRs, and recovery state. Source-level truth
> remains in `docs/V3_COVERAGE_STATUS.md`.

## 1. Non-negotiable proof gate

The source manuscript remains authoritative. A P-ID is promoted to `proved`
only after all of the following hold:

1. exact source statement and hypotheses are identified;
2. Lean semantics match the source or are explicitly stronger;
3. the declaration is imported by the official `UEOT` target;
4. pinned Lean/Mathlib branch CI passes;
5. the branch is based on the latest green **Lean-affecting** main state; a later docs-only commit does not force proof replay;
6. the branch is merged into `main`;
7. post-merge `lake build UEOT` passes;
8. no `sorry`, `sorryAx`, UEOT-specific axiom, `native_decide`, or source weakening;
9. coverage is updated only after the previous eight checks.

A helper theorem or a green isolated file never promotes a source P-ID by itself.

## 2. Current verified checkpoint

Current source-level status on green `main`:

- proved: **30**
- partial: **0**
- pending: **76**
- total: **106**

Current repository main checkpoint before this roadmap edit: `8b1667036182c69bdcd44b2391cb03f237ddb569` (full-target CI #343 success). Latest Lean-affecting proved-theorem checkpoint: `a5d1cd06d16483cfcc6805089fe7bd1bb5a34177` (P-DYN-03, full-target CI #337 success).

The 30 proved P-IDs are:

- P-MET-01, P-MET-02
- P-PROC-01
- P-PRED-01, P-PRED-02, P-PRED-03
- P-INFO-05
- P-INT-02, P-INT-03
- P-DYN-01, P-DYN-03, P-DYN-04
- P-REC-01
- P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- P-STAT-03, P-STAT-04
- P-TEL-01
- P-QUO-03
- P-BRG-02
- P-REF-04, P-REF-05

## 3. Why the previous branch model is now inefficient

The repository currently contains many historical formal branches. Most are
already merged, heavily behind `main`, or contain superseded experiments.
Keeping all of them mentally active creates three costs:

- repeated rebases of already-integrated work;
- unnecessary `UEOT/V3.lean` conflicts;
- ambiguity about which branch is the source candidate.

From now on branches are classified:

- **HOT**: actively changing proof lane, expected to merge;
- **WARM**: clean branch reserved for the next proof packet;
- **ARCHIVE**: merged/superseded evidence; never reused as a development base.

Only HOT/WARM branches count toward the parallel lane budget.

## 4. Six-slot parallel execution model

The optimal steady state is **six proof lanes plus one serialized integration lane**.
More than six active proof branches increases context-switching and rebase cost
faster than it increases theorem throughput.

### Slot A — immediate closure / covariance

Branch: `formal/pfac01-covariance`

Target:
- P-FAC-01

Already available:
- kernel transport;
- readout transport;
- strong-lumpability invariance;
- full path-law covariance;
- predictive-factorization covariance.

Remaining closure:
- transported reward expectation;
- policy value equality;
- optimal value equality;
- source-facing wrapper and semantic audit.

### Slot B — completed / finite causal path error

Branch: `formal/pdyn03-path-error` (archive after merge)

Target:
- P-DYN-03 — **proved**

Integrated on main:
- sharp product error algebra and additive union bound;
- finite-PMF TV/overlap identity;
- causal PMF path-law recursion;
- source-facing finite causal path-error wrapper.

Merge:
- `a5d1cd06d16483cfcc6805089fe7bd1bb5a34177`;
- main full-target CI #337: success.

The freed HOT slot is reassigned to P-DYN-02 / QSD-02 closure work.

### Slot C — information chain factory

Branch: `formal/pinfo01-04-chain`

Targets, in dependency order:
1. P-INFO-01 deterministic-statistic MI chain identity;
2. P-INFO-02 conditional-MI -> expected-TV via conditional KL + Pinsker + Jensen;
3. P-INFO-03 zero-distortion predictive rate-distortion;
4. P-INFO-04 Fano identity lower bound.

Shared infrastructure:
- existing `UEOT.V3.InformationCore`;
- pinned Mathlib KL data processing / chain rules;
- finite/discrete entropy layer where the source is discrete.

Rule: reusable MI/CMI lemmas merge first if later lanes need them.

### Slot D — structural interface factory

Branch: `formal/pint01-02-structure`

Targets:
- P-INT-01 structured sufficiency iff;
- P-INT-02 finite minimal internal/environment factorization.

Dependencies:
- P-PRED-01 already proved;
- P-INFO-01/02 only where the literal source theorem invokes information residuals.

Design:
- keep the conditional-independence/factorization theorem separate from
  information-norm corollaries;
- finite response-kernel quotient construction goes in a dedicated module.

### Slot E — continuous/discrete dynamics factory

Branch: `formal/pdyn02-ctmc`

Primary target:
- P-DYN-02 finite CTMC generator quotient iff.

Follow-on packets after P-DYN-02:
- P-PER-01 deterministic invariant core;
- P-PER-02 stochastic occupation core;
- P-PER-03 finite viability kernel.

P-PER-04 is differential/tangent and remains a separate analytic packet.

### Slot F — persistence/recovery/QSD factory

Branch: `formal/persistence-qsd`

Targets staged internally:
1. P-REC-02 continuous stochastic Lyapunov recovery;
2. P-REC-03 recovery-time canonical potential;
3. P-REC-04 drift -> mean recovery time;
4. P-QSD-02 finite Perron representation;
5. P-QSD-03 persistence/forgetting time window;
6. P-QSD-01 conditional stabilization inverse statement;
7. P-QSD-04 reversible killed-diffusion spectral specialization.

Important: finite Perron/QSD results should not wait for the hardest diffusion
spectral theorem. Split modules and promote individually.

## 5. Second parallel pool after the first two merges

When at least two of Slots A-F merge, open the next pool without increasing
the total HOT lane count above six.

### Factory G — finite certification and inverse problems

Targets:
- P-STAT-01, P-STAT-02, P-STAT-05..09
- P-INV-01, P-INV-04, P-INV-05

Shared tools:
- finite concentration;
- union bounds;
- TV estimates;
- linear regression finite-sample algebra.

P-INV-02/03 Fisher gauge directions form a separate differential-geometric
subpacket and should not block the finite statistics lane.

### Factory H — composition / implementation

Targets:
- P-ID-01, P-ID-02
- P-OMG-01, P-OMG-02
- P-COMP-01..07

Split:
- finite set/hypergraph/Booleanization results;
- prediction-information parent emergence results.

Reuse the already proved CAR/RES/PRED/INFO modules instead of rebuilding their
definitions locally.

### Factory I — control / quotient / GOA

Targets:
- P-CTL-01 first;
- P-QUO-01, P-QUO-02, P-QUO-04, P-QUO-05;
- P-GOA-01, P-GOA-02, P-GOA-03;
- P-CTL-02 after finite Bellman semantics are stable;
- P-CTL-03 and P-GOA-04 stay in the analytic/spectral lane.

Dependency:
world/process -> predictive state -> dynamic quotient -> policy/value -> GOA.

No downstream theorem may redefine upstream process or predictive semantics.

### Factory J — KL / variational / dual-drive

Targets:
- P-KL-01..03 first;
- P-DDH-01..03;
- P-DDH-04..05;
- P-ALI-01..03;
- P-KL-04/05 when CTMC/Girsanov infrastructure is ready.

This factory should reuse `InformationCore` and never introduce a second KL definition.

### Factory K — evolution / reflexivity

Targets:
- P-EVO-01..04
- P-BRG-01
- P-REF-01..03

Expected infrastructure:
- positive matrices/operators;
- finite Perron layer from QSD where appropriate;
- martingale expectation identities;
- Bayesian state augmentation.

## 6. Final assembly lane

Only after prerequisites are source-proved:

- P-API-01
- P-ALG-01
- P-CORE-01

These are integration theorems, not a place to hide missing mathematics.

Final gate:
- 106 proved;
- 0 partial;
- 0 pending;
- `lake build UEOT` green;
- source/coverage consistency green;
- transitive axiom audit green.

## 7. File ownership rule

Parallel lanes should edit disjoint files.

Preferred pattern:
- one P-ID family -> one new module;
- source-facing wrapper stays in the same family module;
- a feature branch may edit `UEOT/V3.lean` only to add its own import line, so the official target compiles that module in branch CI;
- no feature branch performs unrelated/shared refactors in `UEOT/V3.lean`;
- only `main` promotion commits edit `docs/V3_COVERAGE_STATUS.md`.

If two lanes need the same reusable lemma:
1. extract it into a small infrastructure module;
2. merge that module first;
3. clean-rebase both lanes;
4. continue independently.

This is cheaper than cross-branch cherry-picking.

## 8. CI hierarchy

Use three verification levels.

### L1 — branch development
On `formal/**` pushes:
- compile the official `UEOT.V3` target (new modules must already be imported);
- no source promotion.

### L2 — PR merge gate
Before merge:
- full `lake build UEOT`;
- source-facing theorem present;
- no prohibited proof escape;
- branch includes the latest green Lean-affecting main changes;
- docs-only commits after that Lean base do not force a rebase, provided the PR is conflict-free and the proof environment is unchanged.

### L3 — main promotion gate
After merge:
- full `lake build UEOT`;
- verification scripts / axiom audit;
- only then update coverage.

CI runs in parallel across feature branches; merges remain serialized.

## 9. Merge train

Never wait for all lanes.

For each lane independently:

source audit
-> helper lemmas
-> source wrapper
-> official import
-> green branch CI
-> clean rebase
-> green PR CI
-> serialized squash merge
-> green main CI
-> coverage promotion.

While one lane is in CI, proof work continues on another lane.

## 10. Throughput metrics

Track these, not raw commit count:

- proved P-IDs / week;
- median proof-lane cycle from first source wrapper to main promotion;
- percentage of failed CI caused by mathematics vs scripting/elaboration;
- number of stale branches requiring rebase;
- number of shared-file conflicts;
- number of source promotions reverted after semantic audit (target: zero).

The target steady state is:
- 4-6 HOT proof lanes;
- 1-2 candidates in CI;
- 1 integration at a time;
- zero unverified coverage promotions.

## 11. Immediate execution order

1. close P-DYN-03 current compile errors;
2. close P-FAC-01 value covariance;
3. run Slots C-F in parallel from current green main;
4. merge whichever lane reaches source-level green first;
5. after every Lean-affecting merge, advance/rebase dependent HOT lanes in a batch;
   never replay proofs merely because a coverage/roadmap-only commit moved main;
6. open Factories G-K progressively while keeping at most six HOT proof lanes.

This converts the project from branch-by-branch proof work into a controlled
parallel proof pipeline while preserving the strict source-matching standard.
