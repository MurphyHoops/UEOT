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
| proved | **44** |
| partial | **0** |
| pending | **62** |
| total | **106** |

Latest completed proof promotion: **P-STAT-08**.

Recent promotion train:

- P-STAT-07 — squash merge `97533726d71e28b8f4aac1d956db7f65fe98ebda`; post-main CI #629 success.
- P-STAT-09 — squash merge `b21f91f233e7cb65c6f1d6ec928b4870ceee3db4`; post-main CI #641 success.
- P-STAT-08 — squash merge `f03ea2ae9996228d86c742d7f787b95a85ad5898`; post-main CI #648 success.

P-STAT-08 exposes the frozen finite-candidate bound with

`u = sqrt(log(2*m/alpha)/(2*N))`

and proves that an empirical-risk minimizer has true risk at most the finite
class optimum plus `2*u`, with failure probability at most `alpha` for `[0,1]`
losses and `N` independent validation observations. Candidatewise independence
is not assumed.

## 3. Active parallel proof lanes

Formal proof development is parallel; only promotion into `main` is serialized.

### Lane A — P-STAT-06: RKHS/MMD simultaneous embedding error

Branch: `formal/pstat06-mmd-concentration`

Frozen source target: for `L` fixed response laws, `N` independent samples per
law, separable RKHS, `k(y,y)<=1`, and Bochner-integrable feature map,

`max_j ||muHat_j-mu_j|| <= (1 + sqrt(2*log(L/alpha)))/sqrt(N)`

with probability at least `1-alpha`.

Machine-checked helper layers currently include:

- exact one-replacement sensitivity `2/N`;
- independent centered Hilbert off-diagonal inner expectation equals zero;
- deterministic double-inner-product expansion of the empirical-mean squared norm.

The branch is now testing the exact second-moment estimate
`E||mean Z_i||^2 <= 1/N`. The source P-ID remains pending until the
second-moment/Jensen/McDiarmid/finite-union chain is complete and promoted.

### Lane B — P-INV-01: equal-prior binary testing

Branch: `formal/pinv01-binary-testing`

Frozen source target:

`R* = (1/2) * (1 - D_TV(P0,P1))`.

The universal lower bound is already machine-checked. The branch now contains a
general-space Hahn-decomposition attainability proof, which is the
measure-theoretic equivalent of selecting the source density-comparison event
relative to `P0+P1`. It remains pending until the source-facing optimum theorem
is green and passes the promotion train.

## 4. Promotion protocol for parallel lanes

Each lane may compile, repair, and accumulate commits independently. Promotion
into `main` remains a single-writer train:

1. semantic source audit;
2. feature full-target CI;
3. clean-port/rebase onto newest green Lean-affecting `main`;
4. clean-port branch full-target CI;
5. PR full-target CI;
6. squash merge;
7. post-merge main full-target CI;
8. ledger synchronization.

A later lane must clean-port if another Lean-affecting lane reaches `main` first.
This is how proof work stays parallel without letting integration races corrupt
source-level accounting.

## 5. Recent integrated promotions

Recent source-level promotions after the archived 32-proof checkpoint:

- P-FAC-01 — main CI #502 success;
- P-DYN-02 — main CI #506 success;
- P-REC-02 — main CI #519 success;
- P-PER-01 — main CI #540 success;
- P-ID-01 — main CI #547 success;
- P-STAT-02 — main CI #563 success;
- P-INFO-01 — main CI #572 success;
- P-STAT-05 — main CI #584 success;
- P-STAT-01 — main CI #599 success;
- P-STAT-07 — main CI #629 success;
- P-STAT-09 — main CI #641 success;
- P-STAT-08 — main CI #648 success.

Detailed older narratives remain in the source-level coverage archive and Git
history. No already proved P-ID is downgraded by this state-file synchronization.

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
9. MMD-small does not imply TV-small in general; P-STAT-06/07 keep the RKHS
   error scale distinct from TV.
10. P-STAT-09 keeps the source Radon–Nikodym density-ratio assumption rather
    than replacing it with stronger measure domination.
11. Import-graph reachability is part of proof evidence.
12. No active lane has produced an F3 counterexample to the UEOT Core architecture.

## 7. Mandatory recovery procedure

1. Read this file.
2. Read `V3_COVERAGE_STATUS.md`.
3. Fetch current `main` SHA and latest main Action.
4. Inspect every main commit newer than the checkpoint recorded here.
5. Compare every active branch to current `main` and inspect its latest CI.
6. Never overwrite a newer branch head with an older remembered version.
7. Feature-green is not `proved` until semantic audit + integration + green
   post-merge CI + ledger sync.
8. New modules must be reachable from `UEOT` / `UEOT.V3`.
9. Keep proof development parallel but serialize main promotion.
10. For unresolved theorem wording, use the recovered canonical v3.0 source;
    never reconstruct constants or hypotheses from memory.

## 8. Immediate execution order

Parallel now:

- P-STAT-06: finish exact Hilbert second moment, Jensen, McDiarmid and finite union;
- P-INV-01: validate Hahn attainability and then clean-port onto current main;
- audit the next shallow-dependency pending P-ID so a new lane is ready before either current lane reaches promotion.

Promote whichever source-matched lane becomes green first, then clean-port the
remaining lanes onto the new `main` before their own PR gates.

## 9. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, the frozen source manuscript + merged Lean
statements + green main CI + promotion gate take precedence; repair document
drift before further integration.
