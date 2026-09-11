# UEOT Core Lean — Live Formalization State

> **Recovery entry point.** Read this file first when resuming formalization
> work. Source-level truth is `V3_COVERAGE_STATUS.md`; the broader execution
> model is `PARALLEL_FORMALIZATION_ROADMAP.md`.

Last synchronized: **2026-09-11**

## 1. Canonical source and environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

Promotion requires exact source matching, official-target branch/PR CI, merge
to `main`, green post-merge CI, and ledger synchronization. A helper theorem or
green feature branch alone is never counted as a source-level proof.

The repository manifest still records `content_sync: pending` for the canonical
v3.0 manuscript body. The exact canonical file is available through the user's
File Library for semantic audits; do not change the manifest to complete until
the matching body is actually committed to the repository.

## 2. Current integrated checkpoint

| status | count |
|---|---:|
| proved | **40** |
| partial | **0** |
| pending | **66** |
| total | **106** |

Latest completed proof promotion: **P-STAT-05**.

- final feature head: `259b69ece2be22ead8e22b04c02fcf0bd9170da8`
- branch CI #580 (`34544593542`): success
- PR #29 CI #583 (`34544873693`): success
- squash merge: `5e5071820a5e30554b23f8344b3315841b0e4b6a`
- post-merge main CI #584 (`34545279143`): success
- source-level ledger synchronization commit: `5214fe5cff18adca6b37ed4c30e72098592034f3`

P-STAT-05 now exposes exact finite-history predictive-class recovery under the
source gap condition. It proves same-class empirical distance is at most
`2*eta`, different-class empirical distance is at least `gamma-2*eta`, and the
`gamma/2` threshold exactly coincides with true predictive equivalence. It does
not infer class identity by uncontrolled transitive closure.

## 3. HOT proof lane A — P-STAT-01

Branch: `formal/pstat01-finite-tv`

Target: **P-STAT-01 — finite-alphabet simultaneous TV concentration**.

Frozen source statement for `L` fixed response cells, response alphabet size
`K`, and `N` independent samples per cell:

`P(max_j D_TV(p_j,pHat_j) > eta) <= L * 2^(K+1) * exp(-2*N*eta^2)`.

Clipped source radius:

`eta_NKL(alpha) = min 1 (sqrt (((K+1)*log 2 + log(L/alpha))/(2*N)))`.

Source proof structure is frozen:

1. each response-cell/subset empirical mass is a Bernoulli average;
2. two-sided Hoeffding contributes `2 * exp(-2*N*eta^2)`;
3. union over at most `2^K` alphabet subsets;
4. union over `L` response cells;
5. finite-space TV is the maximum event-mass discrepancy;
6. when the analytic radius exceeds one, use deterministic `TV <= 1`.

No independence across response cells is required; only the `N` samples inside
each cell need independence. No carrier-candidate union bound is permitted:
P-STAT-02 already propagates one simultaneous response event deterministically
to all carrier defects.

### Current implementation state

Two modules are active:

- `UEOT/V3/FiniteAlphabetConcentration.lean` — deterministic finite-event/union layer;
- `UEOT/V3/FiniteAlphabetSampling.lean` — empirical law and Hoeffding sampling layer.

The deterministic layer has already passed the official target on branch CI
#579 (`34544379413`), including the exact `2^K` subset factor and `L` response
factor.

Sampling development history:

- structural sampling head `7c8ac7e5ebf04138a6e75c9921995e4fff685eb7`;
- CI #585 (`34545387234`) failed only in the sampling module;
- #585 narrowed the remaining issues to indicator-constant normalization,
  finite empirical-count coercion syntax, and the exact pinned-Mathlib
  namespace for the independent-sum Hoeffding theorem;
- exact pinned Mathlib audit established the tail theorem as
  `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`;
- current repair head: `686786cf8f9c91234fd4f6d49528ea6e9bac450e`;
- current branch CI #586 (`34545870759`) is the next verification run.

The accepted part of #585 already includes measurable Bernoulli indicators,
i.i.d.-within-cell independence transport to centered variables, exact event
means, and the `[0,1]` Hoeffding sub-Gaussian certificate. No source theorem
constant has been changed.

### Promotion constraint after P-STAT-05

P-STAT-01 was opened before the P-STAT-05 Lean-affecting merge. Therefore even
if its current feature CI becomes green, it must be clean-ported/rebased onto
the newest green Lean-affecting `main` before PR promotion. Feature-green is not
source-level `proved`.

## 4. HOT proof lane B — next independent statistics audit

The next low-collision target is **P-STAT-07** after P-STAT-01 stabilizes.
The frozen source states exact MMD covariance under a bimeasurable bijection
`T` with synchronously transported kernel `k_T(Tx,Ty)=k(x,y)`:

`MMD_{k_T}(T#P,T#Q) = MMD_k(P,Q)`.

This should be developed as a separate MMD/kernel infrastructure packet. The
repository does not currently expose a dedicated MMD module, so do not fake the
theorem by renaming TV covariance. P-STAT-06 is heavier because it requires the
separable-RKHS/Bochner/McDiarmid concentration layer and should not block
P-STAT-07.

## 5. Recent integrated promotions

Recent source-level promotions after the archived 32-proof checkpoint:

- P-FAC-01 — main CI #502 success;
- P-DYN-02 — main CI #506 success;
- P-REC-02 — main CI #519 success;
- P-PER-01 — main CI #540 success;
- P-ID-01 — main CI #547 success;
- P-STAT-02 — main CI #563 success;
- P-INFO-01 — main CI #572 success;
- P-STAT-05 — main CI #584 success.

Detailed older narratives remain in the source-level coverage archive and Git
history. No already proved P-ID is downgraded by this state-file compaction.

## 6. Theory-maintenance findings

Canonical v3.0 remains frozen during verification.

Current high-value constraints:

1. CTMC time is one-sided; P-DYN-02 uses the right derivative at `t=0`.
2. Marginal persistence and pathwise persistence are distinct; P-PER-03 has an
   explicit infinite-path-law bridge.
3. P-PER-01 exact omega-limit invariance does not require negative time under
   the source precompactness hypothesis.
4. Representation covariance is derived from transported primitive dynamics,
   not postulated at final value/path level.
5. P-ID-01 is a frozen endpoint-kernel transport theorem and is not the physical
   one-step dynamics itself.
6. P-INFO-01 preserves genuine countable-discrete `ENNReal` entropy semantics,
   including `H(M)=infinity`.
7. P-STAT-02 proves that one simultaneous response event controls all carrier
   defects by `2*eta`; carrier multiplicity must not be reintroduced in P-STAT-01.
8. P-STAT-01 complexity depends on response alphabet size `K` and response-cell
   count `L`, not the number of candidate carriers.
9. Import-graph reachability is part of proof evidence.
10. No active lane has produced an F3 counterexample to the UEOT Core architecture.

## 7. Mandatory recovery procedure

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

## 8. Immediate execution order

1. Close P-STAT-01 sampling/Hoeffding compile errors on its feature branch.
2. Add the lower-tail/two-sided event theorem, then feed it through the already
   green subset and response-cell union layer.
3. Prove the exact source-facing P-STAT-01 probability bound and clipped radius.
4. Connect that single simultaneous response event directly to P-STAT-02.
5. Clean-port the completed packet onto newest green Lean-affecting `main`.
6. Run branch CI -> PR CI -> squash merge -> post-merge main CI -> ledger sync.
7. In a disjoint lane, begin P-STAT-07 MMD covariance infrastructure only after
   the P-STAT-01 sampling API is stable.

## 9. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, the frozen source manuscript + merged Lean
statements + green main CI + promotion gate take precedence; repair document
drift before further integration.
