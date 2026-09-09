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
- commit: `bfb711a54eb38f5df5c1a025153c118e833daa8e`
- latest observed main Action: #362
  `completed/success`
- latest ledger promotion: **P-QSD-02**
- theorem-bearing green checkpoint: `a5d1cd06d16483cfcc6805089fe7bd1bb5a34177`
  (P-DYN-03; main CI #337 success)

The complete proved list is maintained in `V3_COVERAGE_STATUS.md`.

## 3. HOT proof lanes

### A. P-DYN-02 — active reverse-derivative closure

- branch: `formal/pdyn02-ctmc`
- head: `268a5585953dfb262f7460bae862044783b283e3`
- latest submitted proof repair evaluates the derivative CLM composition at
  scalar direction `1` using explicit `ContinuousLinearMap.comp_apply` and
  `toSpanSingleton_apply`.
- latest observed Action: #372 on `268a5585`, **in progress** at snapshot.
- green foundation: finite CTMC block-sum criterion ↔ generator intertwining;
  macro construction/uniqueness under surjective partition; power propagation;
  generator ⇒ matrix-exponential semigroup intertwining.
- blocker: verify reverse semigroup ⇒ generator under pinned Mathlib, then
  package the exact source iff theorem.
- next: inspect #372; if green, source-audit + PR/merge train; if red, repair
  only the residual final simplification.

### B. P-INFO-01 — exact conditional-KL chain active

- branch: `formal/pinfo01-04-chain`
- head: `6a5db0dc519c07a1f93c43fcf482f94db03c343a`
- latest submitted theorem: `mutualInfo_eq_statistic_add_conditional`.
- latest repair opens the scoped probability/ENNReal notation required by
  pinned Mathlib and uses `ENNReal` explicitly where parser ambiguity arose.
- latest observed Action: #373 on `6a5db0dc`, **in progress** at snapshot.
- green foundation: deterministic statistic joint/marginal transport;
  data processing; reversible measurable lift preserving KL (#359 success).
- semantic design: conditional information is represented by standard-Borel
  disintegration and conditional KL after the reversible lift; it is not
  defined as a subtraction residual.
- blocker: pinned-Mathlib verification of the exact chain identity, then the
  ε-retention and discrete-entropy consequences.
- next: inspect #373 and repair only genuine disintegration/typeclass issues.

### C. P-FAC-01 — feedback-policy covariance pending

- branch: `formal/pfac01-covariance`
- head: `9df57aed56d76f89240b09e97aefd8634c8d891f`
- PR: **#14 draft**
- latest verified branch/PR CI: #321/#322, success.
- green foundation: representation transport for kernels/readouts,
  strong-lumpability covariance, homogeneous path-law covariance, predictive
  factorization covariance, and reward/policy/optimal-value transport.
- blocker: full feedback-policy finite path-law covariance must be derived,
  not assumed as an external policy-law equality.
- reuse target: main's `PathError.causalLaw` finite causal-record machinery.
- next: define transported history policy and prove law pushforward by horizon induction.

### D. P-PER-01 — omega-limit strong invariance active

- branch: `formal/pper01-omega-limit`
- head: `03079c3fdcdecfd1321afce973e3f204dd6b4e3f`
- PR: **#17 draft**
- latest full-target branch CI: #365, **success**.
- green theorem layer: nonempty compact omega-limit; containment in a closed
  persistence domain; forward invariance under the continuous semiflow.
- semantic blocker: the source requires `φ_s '' ω(x) = ω(x)`; Mathlib's
  generic monoid invariant theorem gives only forward inclusion.
- next: formalize the precompact-subsequence reverse inclusion while keeping
  genuine semiflow semantics.

### E. P-REC-02 — continuous recovery active

- branch: `formal/prec02-continuous-recovery`
- head: `45eb9a1bd35c98a245ca55c885bd45d800a8c5e7`
- PR: **#18 draft**
- module-only CI #366: success.
- official-target CI #370 on `45eb9a1b`: **success**.
- green theorem layer: exact source-shaped exponential scalar recovery bound
  under pointwise right-derivative hypotheses, plus energy-to-square-distance
  conversion.
- semantic blocker: bridge the source's local absolute continuity + a.e.
  Dynkin drift inequality to the scalar bound without strengthening the final
  P-ID statement.
- next: formalize an AC/a.e. Grönwall bridge, then instantiate it with
  `m(t)=E[W(X_t)]`.

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
