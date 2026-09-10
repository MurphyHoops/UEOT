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

The repository manifest currently records `content_sync: pending` for the
canonical v3.0 manuscript body. The exact canonical filename, SHA-256, and 106
P-ID ledger are preserved. Do not reconstruct an unresolved source theorem
from memory when the exact frozen wording is unavailable.

## 2. Current integrated checkpoint

| status | count |
|---|---:|
| proved | **38** |
| partial | **0** |
| pending | **68** |
| total | **106** |

Latest completed proof promotion: **P-STAT-02**.

- feature head: `0275f7ad43f8505eefeefaefa0fb29052cf5b523`
- branch CI #560 (`34542020196`): success
- PR #27 CI #561 (`34542249026`): success
- squash merge: `5886c7baa4d9b4936e21dbd5639d7c893af22053`
- post-merge main CI #563 (`34542472419`): success
- ledger synchronization commit: `1a21f170da43c5fdc6f2dcbae569889464e07935`

P-STAT-02 now exposes the deterministic response-error -> carrier-defect error
bridge. On one simultaneous response-level TV event, every carrier satisfies
`|eHat(S)-e(S)| <= 2 * eta`; there is no additional union bound over carriers.
P-STAT-01 remains the distinct probabilistic layer that must supply that
simultaneous event.

## 3. HOT proof lanes

### A. P-INFO-01 — information retention identity and entropy lower bound

- development branch: `formal/pinfo01-clean-main`
- current development head: `315a0aeafdc2807f65d68ada7b2be6c70c09eedf`
- full-target CI #562 (`34542278658`): **success**
- branch is proof-complete but stale/diverged relative to current main and must
  be clean-ported before PR promotion

The complete green development proof contains:

1. deterministic statistic law `M=f(H)` and exact chain identity
   `I(H;Y)=I(M;Y)+I(H;Y|M)`;
2. epsilon retention `I(H;Y) <= I(M;Y)+epsilon`;
3. copied-pair/channel data processing giving `I(M;Y) <= copy-KL`;
4. a countable-discrete Radon--Nikodym density calculation;
5. extended-real Shannon entropy, preserving the source-allowed `H(M)=∞` case;
6. exact `copy-KL = H(M)` for countable discrete probability laws;
7. standard-Borel disintegration of arbitrary `(M,Y)` laws yielding
   `I(M;Y) <= H(M)`;
8. source-facing approximate memory lower bound
   `I(H;Y)-epsilon <= H(M)` in `ℝ≥0∞` ordered subtraction.

The finite-state specialization also recovers the existing real-valued PMF
Shannon sum used by P-INFO-05.

Immediate action: clean-port exactly the four information modules plus their
`UEOT.V3` imports onto the newest green main, rerun full branch CI, then proceed
through PR CI -> squash merge -> post-merge main CI -> ledger synchronization.

### B. P-STAT-01 — source audit only

P-STAT-02/03/04 are now integrated. P-STAT-01 is the natural remaining front of
the finite statistics chain, responsible for the concentration/union-bound
layer that produces the simultaneous response-error event consumed by
P-STAT-02.

Do **not** create its source-facing Lean theorem until the exact canonical v3.0
constants and hypotheses are grounded. The repository manifest currently says
`content_sync: pending`, so memory-level reconstruction is not acceptable for a
proof promotion.

## 4. Newly integrated / archive lanes

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
8. Import-graph inclusion remains part of proof evidence; an unimported green
   module is not a source-level promotion.
9. Canonical source body sync is a verification-infrastructure task: unresolved
   theorem wrappers must not be invented while `content_sync: pending`.

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

1. **P-INFO-01** — clean-port the green proof packet onto newest green main and
   drive it through promotion.
2. **Canonical source sync audit** — recover/verify the exact v3.0 manuscript
   body corresponding to the manifest hash before creating new unresolved
   source-facing wrappers such as P-STAT-01.
3. **Refill independent lanes** from the 68 pending source P-IDs only where the
   exact source statement is already grounded, prioritizing low-dependency
   theorems that reuse existing TV, finite-state, recovery, persistence, or
   information infrastructure.
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
