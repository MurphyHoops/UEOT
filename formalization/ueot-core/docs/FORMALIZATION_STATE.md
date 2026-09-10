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
| proved | **36** |
| partial | **0** |
| pending | **70** |
| total | **106** |

Latest completed proof promotion: **P-PER-01**.

- clean proof head: `16c7a614c03b9404737b1b524d1abfbec2e3cb57`
- clean branch CI #533 (`34507651005`): success
- PR #25 CI #536 (`34508338456`): success
- squash merge: `3d3ecb46416ea156e06fffd70684937f8d94caf3`
- post-merge main CI #540 (`34508718076`): success
- ledger synchronization commit: `1abdf6a35fbfb7995c80364784869d79c1627340`

P-PER-01 now contains the literal one-sided persistence theorem: a precompact
continuous nonnegative-time orbit eventually contained in a closed persistence
domain has a nonempty compact omega-limit inside that domain and every
nonnegative-time map sends the omega-limit exactly onto itself.  The reverse
inclusion uses the source shifted-subsequence argument; no negative-time flow or
right inverse is assumed.

## 3. HOT proof lanes

### A. P-INFO-01 — information retention identity and entropy lower bound

- clean branch: `formal/pinfo01-clean-main`
- latest verified head: `ba5cfb82437feca00f73ba77cadadbf56013ebad`
- official-target CI #538 (`34508656414`): **success**
- general deterministic-statistic layer already proves
  `I(H;Y)=I(M;Y)+I(H;Y|M)` and the epsilon-retention inequality
- `InformationEntropyBound.lean` now identifies the copied-pair channel outputs
  with the actual joint law `μ ⊗ₘ κ` and the product of its marginals, so data
  processing gives the genuine mutual-information upper bound by copy-KL
- `InformationDiscreteEntropy.lean` proves, for finite discrete `M`, the
  explicit diagonal density, RN derivative, and
  `(klDiv (copyJoint μ) (μ.prod μ)).toReal = pmfShannonEntropy μ.toPMF`

Immediate target:

close the **literal source clause “if M is discrete”**, not merely a `Fintype M`
special case.  The source does not assume finite Shannon entropy.  Therefore a
real-valued `tsum` cannot silently represent the `H(M)=+∞` case; either introduce
an extended nonnegative Shannon entropy and prove the countable-discrete
copy-KL identity, or derive an equivalent source-complete split into finite- and
infinite-entropy cases.  No new information axiom is permitted.

### B. P-ID-01 — TCIC transport-defect accumulation

- development branch: `formal/pid01-transport-defect`
- latest verified head: `2cb273937c58198e7da5dc97f94618cd9cc5a848`
- official-target CI #539 (`34508693482`): **success**
- the module distinguishes frozen endpoint kernels from one-step physical
  transition kernels
- reusable TV self-distance and triangle lemmas are machine-checked
- the pointwise induction uses measurable pushforward contraction + adjacent
  defect + coherent transport composition
- the source-facing wrapper proves the literal supremum bound
  `sup_m defect(0,n,m) <= sum_{t<n} epsilon_t`

Immediate target:

clean-port only `TransportDefect.lean` plus its import edge onto the latest
`main`, rerun full branch CI, then source audit -> PR CI -> merge -> post-main CI.
Do not merge the older-base branch directly.

## 4. Newly integrated / archive lanes

### P-PER-01 — integrated

The clean integration contains:

- compact-tail omega-limit compactness;
- eventual closed-domain containment;
- nonempty omega-limit under precompact absorption;
- one-sided `atTop` translation for nonnegative time;
- shifted-subsequence reverse inclusion;
- source-facing `p_per_01` exact invariance theorem.

Old PR #17 was closed as superseded; clean PR #25 is the integration evidence.

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
- clean branch CI #504: success
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
4. P-PER-01 confirms exact omega-limit invariance for the one-sided source
   semiflow under orbit precompactness; no two-sided extension is required.
5. Import-graph inclusion is part of verification: an unimported green module
   is not proof evidence for the official target.
6. P-INFO-01 exposes a clean boundary between general measure-theoretic mutual
   information and discrete Shannon entropy.  The remaining issue is genuinely
   countable/infinite-entropy semantics, not the MI chain or channel law.
7. P-ID-01 is structurally independent of physical transition dynamics: its
   `K_t` objects are frozen endpoint kernels and the accumulation is a pure
   transport/TV theorem.

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

1. **P-ID-01** — clean-port the green literal theorem onto current `main` and
   push through the full promotion pipeline.
2. **P-INFO-01** — extend the finite copy-KL/Shannon bridge to the literal
   countable-discrete/infinite-entropy semantics and close the final entropy
   lower bound.
3. **Refill one independent HOT lane** only after P-ID clean branch CI is
   running; prioritize a low-coupling theorem that reuses existing TV,
   persistence, recovery, or finite-state infrastructure.

## 8. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, the frozen source manuscript + merged Lean
statements + green main CI + promotion gate take precedence; repair
documentation drift before further integration.
