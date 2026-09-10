# UEOT Core Lean — Live Formalization State

> **Recovery entry point.** Read this file first when resuming formalization
> work. Source-level truth is `V3_COVERAGE_STATUS.md`; execution order is
> `PARALLEL_FORMALIZATION_ROADMAP.md`.

Last synchronized: **2026-09-11 (Asia/Taipei)**

## 1. Canonical source and environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

Promotion requires exact source matching, official-target branch/PR CI, merge
to `main`, green post-merge CI, and ledger synchronization.

## 2. Current integrated checkpoint

| status | count |
|---|---:|
| proved | **35** |
| partial | **0** |
| pending | **71** |
| total | **106** |

Latest completed proof promotion: **P-REC-02**.

- clean proof head: `4cfe8aad3f19070942e167fea9749595f1f196ee`
- clean branch CI #515 (`34500846267`): success
- clean PR #24 CI #517 (`34501636481`): success
- squash merge: `189fa6b476b0199b321c8d8c2b521f744c0b64ef`
- post-merge main CI #519 (`34502013388`): success
- ledger synchronization commit: `56aba1b5b008688036f3a2daf222262b1264536b`

P-REC-02 now starts from the source's pointwise generator and Lyapunov
inequalities, derives the expectation inequalities by integration, and applies
an explicit Dynkin/localization certificate plus AC/a.e. Grönwall. No
process-specific Dynkin theorem is hidden inside Core.

## 3. HOT proof lanes

### A. P-INFO-01 — information retention identity and entropy lower bound

- branch: `formal/pinfo01-04-chain`
- existing general chain: deterministic-statistic data processing, measurable
  reversible lift, standard-Borel disintegration, exact
  `I(H;Y)=I(M;Y)+I(H;Y|M)`, and epsilon retention
- arbitrary output `Y` is retained; only `M` is made finite/discrete for the
  Shannon bridge, matching the frozen source
- `InformationEntropyBound.lean` already proves the channel/data-processing
  reduction to the copied-state KL divergence
- `InformationDiscreteEntropy.lean` now proves the explicit diagonal density,
  absolute continuity, and the RN derivative formula
- latest RN-density head: `91d08bd12d896e62209a4fc830d2a8a8f18de0c7`
- official-target CI #518 (`34501748368`): **success**

Immediate target:

`(klDiv (copyJoint μ) (μ.prod μ)).toReal = pmfShannonEntropy μ.toPMF`.

After this equality, combine with `channel_kl_le_copy_kl` to obtain the source
`I(M;Y) <= H(M)` and then close the P-INFO-01 entropy lower bound. No new UEOT
information axiom is permitted.

### B. P-PER-01 — omega-limit strong invariance

- branch: `formal/pper01-omega-limit`
- classification corrected from the earlier F2 diagnosis to **F0 proof
  engineering** after literal source re-audit
- already proved on the branch: compactness, nonemptiness, closed-domain
  containment, and forward invariance of the omega-limit
- the old auxiliary right-inverse/group-time workaround is not source-facing
  evidence and must not be used for promotion
- frozen source explicitly proves the reverse inclusion for a one-sided
  semiflow: if `phi_(t_n)(x) -> y` with `t_n > s`, precompactness supplies a
  convergent subsequence of `phi_(t_n-s)(x)`; its limit `z` lies in the
  omega-limit and continuity gives `phi_s(z)=y`
- next: machine-check that compact/subsequence reverse-inclusion argument
  without adding negative-time structure

## 4. Newly integrated / archive lanes

### P-REC-02 — integrated

The clean integration contains:

- `RecoveryContinuous.le_initial_of_ac_ae_deriv_nonpos`
- `RecoveryContinuous.exponential_recovery_bound_ac_ae`
- `RecoveryDynkin.DynkinExpectationCertificate`
- `RecoveryDynkin.expected_generator_drift_of_pointwise`
- `RecoveryDynkin.expected_distance_domination_of_pointwise`
- `RecoveryDynkin.p_rec_02`

Old PR #18 was closed as divergent; clean PR #24 is the integration evidence.

### P-FAC-01 — integrated

- squash merge: `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0`
- post-merge main CI #502: success

### P-DYN-02 — integrated

- clean proof head: `8c0212f4bfbd0e7bf9ed0c445e4662eb02cf04ef`
- branch CI #504: success
- PR #23 CI #505: success
- squash merge: `8ac668253c4d8bc62ab22f250701bc0a190b6049`
- post-merge main CI #506: success

Other already integrated lanes include P-PER-03, P-INT-02, P-PRED-03,
P-DYN-04, P-DYN-03, P-PROC-01, P-QSD-02, P-INFO-05, P-REC-01,
P-DYN-01, P-MET-01/02 and the earlier recovered proof set.

## 5. Theory-maintenance feedback

Canonical v3.0 remains frozen during verification.

Current high-value findings:

1. CTMC time is one-sided; the source-facing P-DYN-02 converse correctly uses
   the right derivative at `t=0`.
2. Marginal persistence and pathwise persistence are distinct; P-PER-03 has an
   explicit infinite-path-law bridge.
3. Representation covariance must be derived from transported primitive
   dynamics, not assumed at the final path/value layer.
4. **Correction:** P-PER-01 exact omega-limit image equality is compatible with
   a one-sided continuous semiflow under the source's orbit-precompactness
   hypothesis. The reverse inclusion uses shifted orbit subsequences; a
   two-sided flow is not required.
5. Import-graph inclusion is part of verification: an unimported green module
   is not proof evidence for the official target.
6. P-INFO-01 exposes a clean modular boundary between general measure-theoretic
   mutual information and finite/discrete Shannon entropy; keep discreteness
   confined to the final entropy bridge.

No active lane has produced an F3 counterexample to the UEOT Core architecture.

## 6. Mandatory recovery procedure

1. Read this file.
2. Read `V3_COVERAGE_STATUS.md`.
3. Fetch current `main` SHA and latest main Action.
4. Inspect every main commit newer than the checkpoint recorded here.
5. Compare every HOT branch to current `main` and inspect its latest CI.
6. Never overwrite a newer branch head with an older remembered version.
7. Feature-green is not `proved` until semantic audit + integration + green
   post-merge CI + ledger sync.
8. New modules must be reachable from `UEOT` / `UEOT.V3`.
9. After material branch-state changes or promotions, update this snapshot in
   the same work session.

## 7. Immediate parallel order

1. **P-INFO-01** — prove copy-KL = Shannon entropy and close the literal entropy
   lower bound.
2. **P-PER-01** — machine-check the shifted-subsequence reverse inclusion under
   one-sided semiflow + orbit precompactness.
3. Audit adjacent pending information/recovery/persistence P-IDs for direct
   reuse only after these near-closure lanes are not left half-finished.

## 8. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, the frozen source manuscript + merged Lean
statements + green main CI + promotion gate take precedence; repair
documentation drift before further integration.
