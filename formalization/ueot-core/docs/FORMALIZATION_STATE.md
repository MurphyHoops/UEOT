# UEOT Core Lean — Live Formalization State

> **Recovery entry point.** Read this file first when resuming formalization work.
> It records the current integrated checkpoint, active proof lanes, CI state,
> semantic gates, and next integration order. The source-level truth ledger is
> `V3_COVERAGE_STATUS.md`; the execution plan is
> `PARALLEL_FORMALIZATION_ROADMAP.md`.

Last synchronized: **2026-09-10 (Asia/Taipei)**

## 1. Canonical source and proof environment

- Canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- Source P-IDs: **106**
- Canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Official target: `lake build UEOT`
- Integration branch: `main`

No P-ID is promoted merely because a helper theorem or feature branch builds.
Promotion requires exact source matching, official-target CI, merge to
`main`, post-merge CI, and ledger update.

## 2. Current integrated checkpoint

| status | count |
|---|---:|
| proved | **31** |
| partial | **0** |
| pending | **75** |
| total | **106** |

Current main checkpoint before this status synchronization:
- commit: `5fa4b6ce4eeef96349c9dd00b2b7ea4fd352bc9f`
- latest integrated proof ledger remains **31 / 0 / 75**.

The counts intentionally remain unchanged while feature branches are being
closed. Branch-green or even a source-facing theorem is not yet an integrated
`proved` promotion.

## 3. HOT proof lanes

### A. P-DYN-02 — CTMC semigroup/generator closure

- branch: `formal/pdyn02-ctmc`
- current head: `8eb663c502c2f581f2be94a7f841a42ec702e7bb`
- current push Action: **#482**, in progress at this synchronization.
- green foundation: finite block-sum criterion ↔ generator intertwining;
  macro construction/uniqueness under a surjective partition; power-series
  propagation; generator ⇒ matrix-exponential semigroup intertwining.
- source-facing nonnegative-time layer exists in
  `CTMCSemigroupNonnegative.lean`, including the right-derivative-at-zero route
  and construction of the macro CTMC generator under the source hypotheses.
- residual blocker classification: **F0 proof engineering**. Prior runs showed
  a hidden norm/topology instance identity problem in the all-real derivative
  helper: Lean printed both equality types identically while rejecting them as
  definitionally unequal. The current repair removes local CLM aliases so the
  derivative proof uses the project-local bundled multiplication maps directly.
- next: inspect #482. If hidden instances remain, switch the reverse direction
  to scalar matrix-coordinate derivatives, eliminating bundled matrix codomain
  identity from derivative uniqueness entirely.

### B. P-PER-03 — finite viability kernel and genuine pathwise persistence

- branch: `formal/pper03-viability`
- current head: `8703bbcbbb7cbf93f422daab34637159b1d895e6`
- PR: **#21 draft**
- push CI **#478: success**; PR CI **#479: success**.
- machine-checked chain now includes:
  finite decreasing viability recursion and finite stabilization; fixed-point
  controlled invariance; maximality among controlled-invariant subsets;
  deterministic stationary preserving policy; PMF-to-kernel bridge; genuine
  Ionescu--Tulcea infinite trajectory; exact coordinate marginal equality; and
  probability-one all-times nonexit from a fixed viability kernel.
- exact v3.0 source audit exposed one remaining semantic gate. The manuscript
  states that the stabilized `K∞` is **exactly** the set of initial states from
  which there exists a strategy keeping the system in `V` forever almost
  surely, and separately states existence of a stationary deterministic
  strategy preserving `K∞`. Current Lean proves the stationary/all-times
  direction and greatest controlled-invariant characterization, but has not yet
  explicitly represented an arbitrary history-dependent strategy and proved
  the reverse implication `sure-safe strategy -> survives every deletion
  round`.
- classification: **F0/F1 interface gap**, not a counterexample. Do not promote
  yet.
- next: formalize the general sure-safe strategy predicate on finite histories,
  prove its winning set is controlled invariant / survives every viability
  iteration, then package exact `K∞` equality and rerun PR CI.

### C. P-INFO-01 — information retention identity and entropy lower bound

- branch: `formal/pinfo01-04-chain`
- current head: `a62f5d44d0a1af4b592a750877a2580b1ee3be8b`
- previous verified chain already proves deterministic-statistic data
  processing, measurable reversible lift, standard-Borel disintegration,
  `I(H;Y) = I(M;Y) + I(H;Y|M)`, and the epsilon-retention consequence.
- exact source statement additionally requires, for discrete `M`,
  `H(M) >= I(H;Y) - ε`, using the standard inequality `I(M;Y) <= H(M)`;
  `Y` need not be discrete.
- new module `InformationEntropyBound.lean` reduces the entropy inequality to
  a standard KL data-processing step from a diagonal copied state versus two
  independent copies. It is imported by the official `UEOT/V3.lean` graph.
- integration-graph CI **#481** exposed a missing explicit
  `IsFiniteMeasure (copyJoint μ)` instance; this was a real coverage check that
  the earlier isolated branch build had not exercised.
- current repair adds the finite-measure bridge for the project-local
  `copyJoint` abbreviation; Action **#483** is in progress.
- remaining mathematical bridge after CI: for discrete `M`, machine-check
  `D_KL(P_(M,M) || P_M × P_M) = H(M)` with compatible `ENNReal`/`Real`
  codomains. No new UEOT information axiom is permitted.

### D. P-FAC-01 — representation covariance

- branch: `formal/pfac01-covariance`
- current head: `8c5e451c10f58fa032af73c66b1bd52f2fee7620`
- branch and PR CI at the current source-facing chain are green.
- transported primitive kernels → finite causal feedback path law → transported
  rewards → policy-by-policy values → optimal supremum is derived in the
  correct direction; the previous independent-final-path-law hypothesis has
  been removed.
- next: exact source audit and integration gate after the two active F0 CI
  repairs are resolved.

### E. P-PER-01 — omega-limit strong invariance audit

- branch: `formal/pper01-omega-limit`
- current head: `94ddd8d0bbf231982c772968a985c4347cd46901`
- semantic status: unresolved **F2** for a one-sided semiflow if exact image
  equality `φ_s '' ω(x) = ω(x)` is claimed without enough reverse-time
  structure. Forward invariance alone is insufficient.
- next: prove reverse inclusion from the literal v3.0 hypotheses or record a
  v3.1 wording correction; do not silently strengthen semiflow to flow.

### F. P-REC-02 — continuous stochastic recovery

- branch: `formal/prec02-continuous-recovery`
- current head: `fc4ad64059c2f84324fc7c66312198c0151f3381`
- source already contains the Dynkin/localization/integrability regularity
  needed for the intended a.e./AC argument.
- status: **F0**, not a source defect.
- next: instantiate the process-level certificate without strengthening the
  manuscript to pointwise differentiability.

## 3.1 Theory-maintenance feedback

Canonical v3.0 remains frozen during formal verification. Theory-facing
findings go under `core/v3-maintenance`, especially
`core/status/FORMALIZATION_FEEDBACK_2026-09-10.md`.

Current high-value findings:

1. CTMC time is one-sided; source exposition should explicitly use the right
   derivative at `t = 0`.
2. Marginal persistence and pathwise persistence are distinct and need the
   explicit path-law bridge now present on P-PER-03.
3. P-PER-03 source-level equality also requires the reverse arbitrary-strategy
   winning-set characterization, not only existence of a stationary policy on
   the fixed kernel.
4. Representation covariance should be derived from primitive transported
   dynamics, not assumed as final path/value equality.
5. One-sided semiflow forward invariance must not be silently strengthened to
   exact image equality.
6. Import-graph inclusion is part of the formalization test: a green commit for
   an unimported module is not evidence that `lake build UEOT` checked it.

No active lane has produced an F3 counterexample to the UEOT Core architecture.

## 4. Integrated / archive lanes

Do not resume proof development from stale heads whose target work is already
integrated on `main`, including P-INT-02, P-PRED-03, P-DYN-04, P-DYN-03,
P-PROC-01, P-QSD-02, P-INFO-05 and P-REC-01.

Older branches such as `formal/dyn01`, `formal/pred02`, `formal/tel01`,
`formal/parallel-ci`, and old wave branches are archive evidence unless a
specific result is deliberately recovered.

## 5. Mandatory recovery procedure

When chat/context is missing:

1. Read this file first.
2. Read `V3_COVERAGE_STATUS.md` for proved/partial/pending truth.
3. Fetch current `main` SHA and latest main Action.
4. If main moved past the SHA recorded here, inspect every intervening commit.
5. Compare every HOT branch to current `main` and inspect its latest Action.
6. Never overwrite a newer branch head with an older remembered version.
7. Green feature branch ≠ proved P-ID until semantic audit + merge + green
   post-merge CI.
8. A module must be reachable from the official `UEOT`/`UEOT.V3` import graph;
   otherwise a green official-target run may simply not have compiled it.
9. After every material branch-state change or promotion, update this file in
   the same work session.

## 6. Immediate parallel order

1. **P-DYN-02** — close hidden-instance derivative interface; scalarize if the
   direct bundled-map repair is not green.
2. **P-PER-03** — add arbitrary-strategy reverse characterization required by
   the exact source wording; only then integrate PR #21.
3. **P-INFO-01** — make the copied-law data-processing module official-target
   green, then prove discrete copy-KL = Shannon entropy.
4. **P-FAC-01** — exact source audit and integration gate.
5. **P-PER-01** — resolve the semiflow reverse-inclusion semantic question.
6. **P-REC-02** — instantiate the exact Dynkin/AC process certificate.

## 7. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, canonical source manuscript + merged Lean
declarations + green main CI + the proof-status gate take precedence. Repair
documentation drift before continuing proof work.
