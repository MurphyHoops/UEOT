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
- commit: `35abc35c9eb9b209a3fb75699f79c893cdb3165c`
- latest observed main Action: #350
  `completed/success`
- latest ledger promotion: **P-QSD-02**
- theorem-bearing green checkpoint: `a5d1cd06d16483cfcc6805089fe7bd1bb5a34177`
  (P-DYN-03; main CI #337 success)

The complete proved list is maintained in `V3_COVERAGE_STATUS.md`.

## 3. HOT proof lanes

### A. P-DYN-02 — active repair

- branch: `formal/pdyn02-ctmc`
- head: `8de6126dd03f5b87b565bac16a16820d996409a4`
- latest Action: #351
  `completed/failure`
- modules: `CTMCLumpability.lean`, `CTMCSemigroup.lean`
- green foundation: block-sum ↔ generator intertwining; macro construction
  and uniqueness on a surjective partition; power propagation; generator ⇒
  matrix-exponential semigroup intertwining.
- blocker: pinned-Mathlib proof of the reverse zero-time derivative
  `semigroup ⇒ generator`. Use the rectangular multiplication
  `ContinuousLinearMap`s; do not use same-algebra `.mul_const/.const_mul`.
- target: source-exact finite CTMC generator criterion iff semigroup quotient.

### B. P-INFO-01 — active closure

- branch: `formal/pinfo01-04-chain`
- head: `0feab7b610891d25181358577062424ff33b588b`
- latest Action: #355
  `completed/failure`
- module: `InformationStatistic.lean`
- green core: deterministic statistic joint/marginal transport and
  `I(f(H);Y) ≤ I(H;Y)`.
- blocker: exact chain identity
  `I(H;Y)=I(M;Y)+I(H;Y|M)` with `M=f(H)`; the latest reversible-KL lift
  attempt is not green.
- no promotion from data processing alone.

### C. P-FAC-01 — infrastructure green, source theorem pending

- branch: `formal/pfac01-covariance`
- head: `9df57aed56d76f89240b09e97aefd8634c8d891f`
- PR: **#14 draft**
- latest observed branch Action: #n/a
  `unknown/unknown`
- green: kernel/readout transport, strong-lumpability covariance,
  homogeneous path-law covariance, predictive factorization covariance,
  expected reward/policy/optimal value under transported policy laws.
- blocker: full feedback-policy path-law transport.
- status remains **pending**.

### D. P-PER-01 — new omega-limit lane

- branch: `formal/pper01-omega-limit`
- source target: continuous semiflow + closed persistence domain + precompact
  orbit imply a nonempty compact omega-limit set contained in the domain and
  strongly invariant under the semiflow.
- Mathlib foundation: `Mathlib.Dynamics.OmegaLimit`.
- semantic gate: Mathlib's generic monoid `IsInvariant` only gives forward
  inclusion; the source equality `phi_s(omega)=omega` still requires the
  reverse inclusion from precompactness.
- state: active foundation.

### E. P-REC-02 — new continuous-recovery lane

- branch: `formal/prec02-continuous-recovery`
- source target: Dynkin/local-AC assumptions plus
  `L W <= -a W + b` imply the exact exponential mean bound and the
  mean-square distance bound from `W >= c d^2`.
- Mathlib foundation: `Mathlib.Analysis.ODE.Gronwall` plus
  absolutely-continuous/integral APIs.
- state: active analytic foundation.

## 4. Integrated / archive lanes

Do not resume proof development from these stale heads; their target work is
already integrated on `main`:

- `formal/pint01-02-structure` — P-INT-02 proved
- `formal/ppred03-recursion` — P-PRED-03 proved
- `formal/pdyn04-cross-scale` — P-DYN-04 proved
- `formal/pdyn03-path-error` — P-DYN-03 proved
- `formal/pproc01-history` — P-PROC-01 proved

Older branches such as `formal/dyn01`, `formal/pred02`,
`formal/tel01`, `formal/parallel-ci`, and old wave branches are archive
evidence unless a specific result is deliberately recovered.

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

## 6. Immediate order

1. **P-DYN-02** — repair reverse semigroup/generator bridge.
2. **P-INFO-01** — complete exact information chain.
3. **P-FAC-01** — finish feedback-policy path-law covariance.
4. **P-PER-01** — omega-limit compact invariant core.
5. **P-REC-02** — continuous Lyapunov recovery.
6. Keep 5–8 independent HOT lanes active and refill only from pending P-IDs.

## 7. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, source manuscript + merged Lean declarations +
green main CI + the proof-status gate take precedence. Repair documentation
drift before continuing proof work.
