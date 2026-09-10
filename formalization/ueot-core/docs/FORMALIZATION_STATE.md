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

The repository manifest still records `content_sync: pending` for the canonical
v3.0 manuscript body. However, the exact canonical file has now been recovered
from the user's File Library and can be used for source audits. New theorem
wrappers must quote/check that recovered canonical source rather than memory.

## 2. Current integrated checkpoint

| status | count |
|---|---:|
| proved | **39** |
| partial | **0** |
| pending | **67** |
| total | **106** |

Latest completed proof promotion: **P-INFO-01**.

- final development head: `315a0aeafdc2807f65d68ada7b2be6c70c09eedf`
- development CI #562 (`34542278658`): success
- clean-port head: `cfddeca9a99dc6466b69807940720aaafc48a119`
- clean-port branch CI #570 (`34542970826`): success
- PR #28 CI #571 (`34543199236`): success
- squash merge: `0dd65bc8ae40fdd1afbfdf0cf61c155585a5a2ac`
- post-merge main CI #572 (`34543427529`): success
- ledger synchronization commit: `f73f8e6793c287380d05a7ca00b34bd4d87ce944`

P-INFO-01 now exposes the exact deterministic-statistic information chain and
the source's discrete predictive-memory lower bound. The discrete layer is
countable rather than artificially finite, and uses `ℝ≥0∞` Shannon entropy so
that `H(M)=∞` is not collapsed through `toReal`.

## 3. HOT proof lanes

### A. P-STAT-01 — finite-alphabet simultaneous TV concentration

The canonical source has been recovered and the exact theorem is grounded.
For `L` fixed conditional responses on a finite response alphabet of size `K`,
with `N` independent samples per response, the source states

`P(max_j D_TV(p_j,pHat_j) > eta) <= L * 2^(K+1) * exp(-2*N*eta^2)`.

It also gives the clipped confidence radius

`eta_NKL(alpha) = min 1 (sqrt (((K+1)*log 2 + log(L/alpha))/(2*N)))`.

Source proof structure:

1. for each response cell `j` and each alphabet subset `A`, empirical mass of
   `A` is a Bernoulli average;
2. two-sided Hoeffding contributes `2 * exp(-2*N*eta^2)`;
3. union over at most `2^K` subsets;
4. union over `L` response cells;
5. finite-space TV is the maximum event-mass difference;
6. if the analytic radius exceeds one, use deterministic `TV <= 1`.

Pinned Mathlib audit:

- `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` gives Hoeffding's lemma for
  bounded variables;
- `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` gives the independent-sum
  Hoeffding tail;
- `MeasureTheory.measure_iUnion_le` supplies the union bound.

Implementation rule: model only the independence actually required by the
source—within each response cell across its `N` samples. No independence across
cells is needed for the union bound. The source-facing theorem must feed the
single simultaneous response event directly into P-STAT-02; it must not add a
second union bound over carriers.

### B. Next independent source-audit lane

While P-STAT-01 compiles, audit the exact frozen statements immediately adjacent
to the now-completed statistics infrastructure, prioritizing P-STAT-05/06/07
only when their dependencies can remain disjoint from the P-STAT-01 file.
Do not claim a new source P-ID from a helper theorem alone.

## 4. Newly integrated / archive lanes

### P-INFO-01 — integrated

The integrated proof contains:

- deterministic statistic law `M=f(H)` and exact chain identity
  `I(H;Y)=I(M;Y)+I(H;Y|M)`;
- epsilon retention `I(H;Y) <= I(M;Y)+epsilon`;
- copied-pair/channel data processing giving `I(M;Y) <= copy-KL`;
- countable-discrete Radon--Nikodym density calculation;
- extended-real Shannon entropy preserving `H(M)=∞`;
- exact `copy-KL = H(M)`;
- standard-Borel disintegration yielding `I(M;Y) <= H(M)`;
- source-facing ordered-subtraction lower bound
  `I(H;Y)-epsilon <= H(M)`.

### P-STAT-02 — integrated

- feature head: `0275f7ad43f8505eefeefaefa0fb29052cf5b523`
- branch CI #560: success
- PR #27 CI #561: success
- squash merge: `5886c7baa4d9b4936e21dbd5639d7c893af22053`
- post-merge main CI #563: success

The integrated module provides TV symmetry, two-endpoint TV perturbation
stability, carrier response-diameter/defect definitions, supremum stability,
and the simultaneous-all-carriers source wrapper `p_stat_02`.

### P-ID-01 — integrated

- clean proof head: `ea6bb69d92f505f2662ad4eac64405470370246f`
- clean branch CI #544: success
- PR #26 CI #545: success
- squash merge: `72b0703270df84d5a92f90d5e01c034777ff37dc`
- post-merge main CI #547: success

The integration contains `TransportDefect.tvDist_self`, TV triangle inequality,
`FrozenTransportSystem` with coherent measurable transports,
`p_id_01_pointwise`, and the literal source supremum theorem.

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
7. P-STAT-02 confirms that once one simultaneous response-level event is
   available, all carrier defects are controlled deterministically by `2η`;
   carrier multiplicity belongs in P-STAT-01 only if the source puts it there.
8. P-STAT-01 source recovery confirms that its statistical complexity depends
   on response alphabet size `K` and number of response cells `L`, not the
   number of candidate carriers.
9. Import-graph inclusion remains part of proof evidence; an unimported green
   module is not a source-level promotion.
10. Repository source-body synchronization is still desirable even though the
    exact canonical file is now recoverable from File Library; the manifest
    should not be changed to `content_sync: complete` until the matching body is
    actually committed into the repository.

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
10. For unresolved theorem wording, use the recovered canonical v3.0 source;
    never reconstruct constants or hypotheses from memory.

## 7. Immediate parallel order

1. **P-STAT-01** — formalize the exact finite-alphabet simultaneous TV bound
   and the clipped confidence-radius corollary from the recovered source.
2. Connect its simultaneous event to the already integrated P-STAT-02
   deterministic carrier-defect bridge, without any extra carrier union bound.
3. While its CI runs, source-audit the next low-dependency statistics theorem
   packet, preferring P-STAT-05/06/07 when their dependencies are isolated.
4. Every near-complete theorem must be clean-ported onto the newest green main
   before promotion; no stale-base PRs.

## 8. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, the frozen source manuscript + merged Lean
statements + green main CI + promotion gate take precedence; repair
documentation drift before further integration.