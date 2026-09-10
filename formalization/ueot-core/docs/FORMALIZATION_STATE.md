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

Snapshot parent main:
- commit: `f8ad303ed9b5116425af44e674f6d2b3256ce5e2`
- latest observed main Action: **#378**, `completed/success`
- latest ledger promotion: **P-QSD-02**

The counts above intentionally remain unchanged while the current feature
branches are being closed. Branch-green or source-facing closure is not yet an
integrated `proved` promotion.

## 3. HOT proof lanes

### A. P-DYN-02 — CTMC semigroup/generator closure

- branch: `formal/pdyn02-ctmc`
- current head: `b1434bdd93d4c91b92bf3186e8b8e9b6390fe4e1`
- current push Action: **#469**, in progress at this snapshot.
- green foundation: finite block-sum criterion ↔ generator intertwining;
  macro construction/uniqueness under a surjective partition; power-series
  propagation; generator ⇒ matrix-exponential semigroup intertwining.
- source-facing layer already exists in `CTMCSemigroupNonnegative.lean`:
  nonnegative-time semigroup equality implies generator equality by the right
  derivative at zero, and common block sums generate a genuine macro CTMC
  generator under the source hypotheses.
- current residual blocker is proof-engineering only (**F0**): the all-real
  helper's derivative equality captured hidden norm/topology instances inside
  bundled continuous-linear multiplication maps. The latest repair unfolds
  those maps to the underlying matrix multiplication after zero-time
  normalization.
- next: inspect #469; if green, run exact source audit and PR/integration gate.

### B. P-PER-03 — viability to genuine pathwise persistence

- branch: `formal/pper03-viability`
- current head: `e41461ed07bb328a2b3920a4750e8ed4bcb772eb`
- PR: **#21 draft**
- prior head `e75cecebf676802a4f857ba70bd5a061457803e3` passed both push and PR CI.
- established bridge: the PMF stationary recursion is exactly the
  measure/kernel composition recursion induced by the stationary Markov
  kernel.
- latest submitted closure proves the stronger semantic bridge that the
  `n`-th coordinate marginal of the Ionescu--Tulcea path law equals
  `stationaryStateLaw n` exactly.
- current push/PR Actions: **#470/#471**, in progress at this snapshot.
- next: if the coordinate-marginal theorem is green, derive the all-times
  nonexit event directly from the viability recursion and remove the supplied
  coordinate-safety hypothesis from the source-facing wrapper.

### C. P-INFO-01 — predictive information lower bound

- branch: `formal/pinfo01-04-chain`
- current verified head: `74ebe33e2b7260f6081246b2b54df49b007957e5`
- official-target Action: **#385, success**.
- closed layer: deterministic statistic data processing, measurable reversible
  lift, standard-Borel disintegration, the exact identity
  `I(H;Y) = I(M;Y) + I(H;Y|M)`, and the epsilon-retention consequence.
- exact source audit confirms that the remaining discrete conclusion is the
  standard bound `I(M;Y) <= H(M)` when `M` is discrete; the source does not
  require `Y` itself to be discrete.
- implementation direction: use Mathlib's Markov-kernel KL data-processing
  theorem `klDiv_comp_right_le`, reducing the bound to the self-information of
  a copied discrete variable, then bridge that self-information to the existing
  Shannon entropy implementation. Do not add a UEOT information axiom.
- blocker: machine-check the discrete self-information/entropy bridge with
  compatible `ENNReal`/`Real` codomains.

### D. P-FAC-01 — representation covariance

- branch: `formal/pfac01-covariance`
- current head: `8c5e451c10f58fa032af73c66b1bd52f2fee7620`
- branch and PR CI at the current source-facing chain are green.
- source-facing dependency is now derived in the correct direction:
  transported primitive kernels → finite causal feedback path law → transported
  rewards → policy-by-policy values → optimal supremum.
- previous blocker is closed: final path-law equality is no longer an
  independent source hypothesis.
- next: exact source audit, then merge/integration gate; do not promote before
  green post-merge main CI.

### E. P-PER-01 — omega-limit strong invariance audit

- branch: `formal/pper01-omega-limit`
- current head: `94ddd8d0bbf231982c772968a985c4347cd46901`
- the branch now explicitly isolates exact omega-limit equality when inverse
  times are available.
- semantic status: unresolved **F2** for the one-sided semiflow source theorem.
  Forward invariance does not by itself imply `φ_s '' ω(x) = ω(x)`; no hidden
  upgrade to a two-sided flow is permitted.
- next: either prove the reverse inclusion from the exact v3 semiflow
  hypotheses or record a v3.1 wording correction if it is genuinely missing.

### F. P-REC-02 — continuous stochastic recovery

- branch: `formal/prec02-continuous-recovery`
- current head: `fc4ad64059c2f84324fc7c66312198c0151f3381`
- source audit cleared the earlier possible regularity concern: v3.0 already
  states the generator-domain/Dynkin/localization/integrability conditions
  needed for local absolute continuity and the a.e. drift inequality.
- current architecture separates the process-level Dynkin certificate, a.e.
  scalar inequality, AC/a.e. Grönwall step, and energy-to-distance conversion.
- status: **F0**, not a source defect.
- next: instantiate the process-level certificate for the exact source process
  class without strengthening the final theorem to pointwise differentiability.

## 3.1 Theory-maintenance feedback

Canonical v3.0 is frozen during formal verification. Theory-facing findings are
recorded separately under `core/v3-maintenance`, especially
`core/status/FORMALIZATION_FEEDBACK_2026-09-10.md`.

Current high-value feedback:

1. CTMC time is one-sided; source exposition should say explicitly “right
   derivative at `t = 0`”.
2. Marginal persistence and pathwise persistence are distinct propositions and
   should be connected by an explicit measure-theoretic bridge.
3. Representation covariance should flow from primitive transported dynamics,
   not from a supplied final value/path-law equality.
4. One-sided semiflow forward invariance must not be silently strengthened to
   exact image equality.

No active lane has produced an F3 counterexample to the UEOT Core architecture.

## 4. Integrated / archive lanes

Do not resume proof development from these stale heads; their target work is
already integrated on `main`:

- `formal/pint01-02-structure` — P-INT-02 proved
- `formal/ppred03-recursion` — P-PRED-03 proved
- `formal/pdyn04-cross-scale` — P-DYN-04 proved
- `formal/pdyn03-path-error` — P-DYN-03 proved
- `formal/pproc01-history` — P-PROC-01 proved

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
8. After every material branch-state change or promotion, update this file in
   the same work session.

## 6. Immediate parallel order

1. **P-DYN-02** — finish the remaining F0 CTMC reverse-derivative interface.
2. **P-PER-03** — close exact coordinate marginal → all-times nonexit.
3. **P-INFO-01** — prove discrete `I(M;Y) <= H(M)` without new axioms.
4. **P-FAC-01** — source audit and integration gate for the now-green causal
   feedback covariance chain.
5. **P-PER-01** — resolve the semiflow reverse-inclusion semantic question.
6. **P-REC-02** — instantiate the exact Dynkin/AC process certificate.
7. Refill free lanes only after these near-closure branches are not left
   half-finished.

## 7. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, source manuscript + merged Lean declarations +
green main CI + the proof-status gate take precedence. Repair documentation
drift before continuing proof work.
