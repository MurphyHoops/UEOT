# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log when available.

Last synchronized: **2026-09-15**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- exact canonical bytes in public repo: pending synchronization

## Current staged checkpoint

| operational state | count |
|---|---:|
| integrated proved, staged by this checkpoint | **80** |
| active proof / feature-green uncounted | **0** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **26** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **79/106** at
`main@a7d1804ea8149230526b8e8473389997f2469ede`, with ledger resulting-main CI
`34886982624` success. P-REC-03 has completed all source, feature, clean-
integration, PR and proof-main gates, including resulting-main CI `34987526584`
success at `main@b337cb8a15e0996f6c285bd073773832fb21500e`.
This ledger branch stages **80/106**. Do not call 80/106 full-green until the
ledger branch passes branch CI, PR CI, lands on `main`, and the resulting-main
CI succeeds.

## Newly staged proof — P-REC-03

Frozen Core 3 P-REC-03 is represented at its declared homogeneous discrete-time
Markov hitting-potential scope:

1. `τ_A` is the first hitting time of the measurable set `A`;
2. `V_A(x)=E_x τ_A` is represented in `ENNReal` and vanishes on `A`;
3. for `x ∉ A`, a pathwise first-step hitting-time recursion is proved before using Markov restart;
4. the homogeneous one-step restart law is derived from the Ionescu–Tulcea path construction rather than postulated;
5. the initial-law mixture and one-step marginal bridge identify the kernel integral of `V_A`;
6. the canonical ENNReal identity is `V_A(x)=1+P V_A(x)` outside `A`;
7. the source finiteness hypothesis is then used only to pass to the real-valued endpoint;
8. the final source-facing equation is `P V_A(x)-V_A(x)=-1`;
9. no finite-state specialization or assumed Poisson/restart identity is introduced.

Canonical theorem surface:
- `UEOT.V3.RecoveryHittingPoisson.p_rec_03`.

Promotion evidence:
- feature branch `formal/prec03-first-step-v1`;
- final feature head `1e01c64824f2e3441b8492cc1f8731895eed467f`;
- feature official root CI `34985193231`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration branch `formal/prec03-main-integration-v1`;
- clean integration head `5142964d87fe53be7b0598d428c49991f50c837f`;
- clean integration CI `34985962098`: success;
- proof PR #87 PR-triggered CI `34986723827`: success;
- proof main `b337cb8a15e0996f6c285bd073773832fb21500e`;
- proof resulting-main CI `34987526584`: success.

## Previous full-green checkpoint — 79/106

P-REC-04 is closed and counted in the 79/106 baseline at
`main@a7d1804ea8149230526b8e8473389997f2469ede`. Its proof resulting-main CI
`34882613059` and ledger resulting-main CI `34886982624` succeeded.

With P-REC-03 staged, the Recovery source-facing set is now complete at the
proof level: P-REC-01, P-REC-02, P-REC-03 and P-REC-04. It becomes ledger-counted
as a complete four-item set only after this promotion lifecycle closes.

P-PER-04, P-QSD-03, P-BRG-01, P-REF-04 and P-REF-05 remain previously counted;
wrapper work must not be double-counted.

## Grounded non-quick fronts

- P-PER-02: Polish/Feller occupation-law theorem with tightness, Prokhorov and Portmanteau; sample-path empirical-frequency weakening is forbidden.
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/04: source-locked distinct non-A results.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; do not count an assumed-convergence
surrogate.

## Candidate next fronts after 80 full-green

- **P-COMP-01:** source requires arbitrary finite nontrivial partitions and the equivalence between conditional KL zero and the corresponding multi-block conditional product law; binary CMI wrappers alone are insufficient.
- **P-PER-02:** remains a larger analytic lane rather than a quick wrapper.

No second proof branch is opened while the P-REC-03 ledger gate is active.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available, `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green or proof-main green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent source/API audit without opening a conflicting proof branch.
