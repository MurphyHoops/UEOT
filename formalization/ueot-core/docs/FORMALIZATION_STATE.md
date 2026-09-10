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
| proved | **37** |
| partial | **0** |
| pending | **69** |
| total | **106** |

Latest completed proof promotion: **P-ID-01**.

- clean proof head: `ea6bb69d92f505f2662ad4eac64405470370246f`
- clean branch CI #544: success
- PR #26 CI #545 (`34509874478`): success
- squash merge: `72b0703270df84d5a92f90d5e01c034777ff37dc`
- post-merge main CI #547 (`34510479466`): success
- ledger synchronization commit: `f4df253da346e43d5469cd4b1c67e6dfc3dc4cfb`

P-ID-01 now exposes the literal Core 3 finite-horizon supremum TCIC bound.
`K_t` is represented as a frozen endpoint kernel, not a one-step physical
transition kernel. The proof uses TV triangle inequality, measurable-pushforward
contraction, adjacent defect bounds, coherent transport composition, and
induction.

## 3. HOT proof lanes

### A. P-INFO-01 — information retention identity and entropy lower bound

- development branch: `formal/pinfo01-clean-main`
- last fully green checkpoint before the countable extension:
  `ba5cfb82437feca00f73ba77cadadbf56013ebad`
- official-target CI #538 (`34508656414`): success
- general deterministic-statistic layer proves
  `I(H;Y)=I(M;Y)+I(H;Y|M)` and epsilon retention
- channel layer identifies the copied-pair outputs with the actual joint law
  and the product of marginals, yielding `I(M;Y) <= copy-KL`
- the frozen source explicitly says **“if M is discrete”**; it does not restrict
  `M` to a finite type and does not assume finite Shannon entropy
- therefore the source-facing bridge is being upgraded from `Fintype`/`toReal`
  to **countable discrete + extended-real entropy**, preserving `H(M)=∞`

Current countable-extension work:

- first head: `fbaeccc5d0aed0db2eec75b7e16dae5dcdc88bb3`
- CI #546 exposed only Lean proof-engineering errors: classical decidability for
  the integrability split and the argument order of `integral_map`
- repair head: `45b78a4463f0e889228eecf7a48c53b12252addf`
- CI #548 (`34510816057`) is running

Immediate target after the extended copy-KL/Shannon bridge is green:

1. disintegrate an arbitrary `(M,Y)` joint law using the source-licensed
   standard-Borel conditional kernel;
2. prove the source-wide discrete bound `I(M;Y) <= H(M)`;
3. compose with epsilon retention to obtain the literal approximate predictive
   memory theorem `H(M) >= I(H;Y)-epsilon` (and an additive ENNReal form where
   needed to avoid invalid infinity subtraction);
4. clean-port the completed files onto the newest `main` before promotion.

## 4. Newly integrated / archive lanes

### P-ID-01 — integrated

The clean integration contains:

- `TransportDefect.tvDist_self`;
- `TransportDefect.tvDist_triangle`;
- `FrozenTransportSystem` with coherent measurable transports;
- `p_id_01_pointwise`;
- literal supremum theorem `FrozenTransportSystem.p_id_01`;
- official `UEOT.V3` import reachability.

### P-PER-01 — integrated

- clean feature head: `16c7a614c03b9404737b1b524d1abfbec2e3cb57`
- branch CI #533: success
- PR #25 CI #536: success
- squash merge: `3d3ecb46416ea156e06fffd70684937f8d94caf3`
- post-merge main CI #540: success

The proof uses the one-sided shifted-subsequence argument and does not assume a
two-sided flow or right inverse.

### P-REC-02 — integrated

- clean proof head: `4cfe8aad3f19070942e167fea9749595f1f196ee`
- branch CI #515: success
- PR #24 CI #517: success
- squash merge: `189fa6b476b0199b321c8d8c2b521f744c0b64ef`
- post-merge main CI #519: success

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

1. CTMC time is one-sided; P-DYN-02 correctly uses the right derivative at
   `t=0`.
2. Marginal persistence and pathwise persistence are distinct; P-PER-03 has an
   explicit infinite-path-law bridge.
3. P-PER-01 shows exact omega-limit invariance does not require negative time
   under the source's precompactness hypothesis.
4. Representation covariance must be derived from primitive transported
   dynamics rather than postulated at the final path/value layer.
5. P-ID-01 is a pure transport/TV theorem about frozen endpoint kernels and must
   not be conflated with the physical one-step dynamics.
6. P-INFO-01 requires genuine countable-discrete entropy semantics: using
   `ENNReal.toReal` at `∞` would silently map infinite entropy to zero and would
   not match the frozen source.
7. Import-graph inclusion remains part of proof evidence; an unimported green
   module is not a source-level promotion.

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

1. **P-INFO-01** — finish countable-discrete extended entropy, then close the
   exact `I(M;Y) <= H(M)` and approximate memory lower bound.
2. **Refill independent lanes** from the 69 pending source P-IDs while P-INFO CI
   is running, prioritizing the lowest-dependency theorems that reuse existing
   TV, finite-state, recovery, persistence, or information infrastructure.
3. Every near-complete theorem must be clean-ported onto the newest main before
   promotion; no stale-base PRs.

## 8. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, the frozen source manuscript + merged Lean
statements + green main CI + promotion gate take precedence; repair
documentation drift before further integration.
