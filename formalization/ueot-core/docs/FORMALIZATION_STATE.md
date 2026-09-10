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
| proved | **32** |
| partial | **0** |
| pending | **74** |
| total | **106** |

Latest completed proof promotion:
- **P-PER-03**
- source-facing branch head: `eb0d0305ab7acab73ea9f3ac06957273f50936be`
- branch push CI #492: success
- PR #21 CI #493: success
- squash merge: `cb665eb3716024e3f677b4ba651e9ef95ea95664`
- post-merge main CI #494 (`34482798255`): success
- ledger synchronization commit: `ea7b62cfebcc866d0dbe8b1a011aacaeec688375`

The authoritative ledger therefore records **32 / 0 / 74**. Branch-green or
even a source-facing theorem is not an integrated `proved` promotion until the
full gate above is complete.

## 3. HOT proof lanes

### A. P-DYN-02 — CTMC semigroup/generator closure

- branch: `formal/pdyn02-ctmc`
- current submitted head: `4f61bc19e054a7cd670b0acbf1283094e6922c4b`
- green foundation: finite block-sum criterion ↔ generator intertwining;
  macro construction/uniqueness under a surjective partition; power-series
  propagation; generator ⇒ matrix-exponential semigroup intertwining.
- source-facing nonnegative-time layer exists in
  `CTMCSemigroupNonnegative.lean`, including the right-derivative-at-zero route
  and construction of the macro CTMC generator under the source hypotheses.
- blocker classification remains **F0 proof engineering**. Runs through #495
  showed that even after scalarizing derivative uniqueness to individual real
  matrix entries, project-local `ContinuousLinearMap` definitions retained
  hidden domain norm-instance parameters. Lean consequently printed the actual
  and expected scalar equality types identically while rejecting them as
  definitionally unequal.
- latest repair removes the bundled readout from the resulting derivative
  equality itself: after uniqueness, unfold `rightMulEntryCLM` and
  `leftMulEntryCLM` in-place and change directly to the bare matrix-entry
  equality. This is intended to erase the hidden norm instance before the
  source-facing algebra is recovered.
- next: inspect the CI for `4f61bc19...`; if green, immediately audit the
  nonnegative-time source wrapper and enter the integration gate.

### B. P-INFO-01 — information retention identity and entropy lower bound

- branch: `formal/pinfo01-04-chain`
- current head: `a62f5d44d0a1af4b592a750877a2580b1ee3be8b`
- official-target CI #483: **success**.
- existing verified chain proves deterministic-statistic data processing,
  measurable reversible lift, standard-Borel disintegration,
  `I(H;Y) = I(M;Y) + I(H;Y|M)`, and the epsilon-retention consequence.
- exact v3.0 source additionally requires, for discrete `M`,
  `H(M) >= I(H;Y) - ε`, using `I(M;Y) <= H(M)`; the source does not require
  `Y` to be discrete.
- `InformationEntropyBound.lean` is now genuinely reachable from the official
  `UEOT/V3.lean` graph. It proves the KL data-processing half by comparing a
  copied/diagonal state with two independent copies and includes the explicit
  finite-measure instance needed for the project-local `copyJoint` definition.
- remaining mathematical bridge: machine-check
  `D_KL(P_(M,M) || P_M × P_M) = H(M)` for discrete `M`, reconciling Mathlib's
  `ENNReal` KL codomain with the existing real-valued `pmfShannonEntropy`.
- preferred route: express diagonal and independent-copy laws as composition
  products with equal first marginal, use Mathlib's KL chain rule, reduce to
  the discrete one-point identity `D_KL(δ_m || μ) = -log μ(m)`, then sum under
  `μ`. No new UEOT information axiom is permitted.

### C. P-FAC-01 — representation covariance

- branch: `formal/pfac01-covariance`
- last audited head: `8c5e451c10f58fa032af73c66b1bd52f2fee7620`
- branch and PR CI at the current source-facing chain are green.
- transported primitive kernels → finite causal feedback path law → transported
  rewards → policy-by-policy values → optimal supremum is derived in the
  correct direction; the previous independent-final-path-law hypothesis has
  been removed.
- exact source audit has found the expected four covariance layers:
  macro path law, predictive sufficiency, exact dynamic closure, and control
  value under a bimeasurable microscopic coordinate change with transported
  primitives.
- next: refresh branch-vs-main state after the P-PER-03 merge, complete the
  declaration-by-declaration source audit, then integrate only if the rebased
  official target remains green.

### D. P-PER-01 — omega-limit strong invariance audit

- branch: `formal/pper01-omega-limit`
- last observed head: `94ddd8d0bbf231982c772968a985c4347cd46901`
- semantic status: unresolved **F2** for a one-sided semiflow if exact image
  equality `φ_s '' ω(x) = ω(x)` is claimed without enough reverse-time
  structure. Forward invariance alone is insufficient.
- next: prove reverse inclusion from the literal v3.0 hypotheses or record a
  v3.1 wording correction; do not silently strengthen semiflow to flow.

### E. P-REC-02 — continuous stochastic recovery

- branch: `formal/prec02-continuous-recovery`
- last observed head: `fc4ad64059c2f84324fc7c66312198c0151f3381`
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
2. Marginal persistence and pathwise persistence are distinct; P-PER-03 now
   contains an explicit Ionescu--Tulcea path-law bridge.
3. P-PER-03 also requires the arbitrary-history-strategy winning-set equality;
   that reverse characterization is now machine-checked and integrated.
4. Representation covariance should be derived from primitive transported
   dynamics, not assumed as final path/value equality.
5. One-sided semiflow forward invariance must not be silently strengthened to
   exact image equality.
6. Import-graph inclusion is part of the formalization test: a green commit for
   an unimported module is not evidence that `lake build UEOT` checked it.
7. Lean can hide norm-instance mismatches under identical pretty-printed types;
   source-facing proofs should eliminate auxiliary bundled analytic structures
   before the final algebraic equality whenever possible.

No active lane has produced an F3 counterexample to the UEOT Core architecture.

## 4. Integrated / archive lanes

Do not resume proof development from stale heads whose target work is already
integrated on `main`, including P-PER-03, P-INT-02, P-PRED-03, P-DYN-04,
P-DYN-03, P-PROC-01, P-QSD-02, P-INFO-05 and P-REC-01.

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

1. **P-DYN-02** — inspect `4f61bc19...`; if the hidden-instance boundary is
   gone, source-audit and integrate immediately.
2. **P-INFO-01** — close discrete copy-KL = Shannon entropy and then the source
   entropy lower bound.
3. **P-FAC-01** — refresh against current main, exact source audit, integration
   gate.
4. **P-REC-02** — instantiate the exact Dynkin/AC process certificate.
5. **P-PER-01** — resolve the one-sided semiflow reverse-inclusion issue without
   silently strengthening the source.
6. Refill free lanes from the pending P-ID set only after these near-closure
   lanes are not left half-finished.

## 7. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, canonical source manuscript + merged Lean
declarations + green main CI + the proof-status gate take precedence. Repair
documentation drift before continuing proof work.
