# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- source P-IDs: **106**;
- authoritative full-green baseline before this ledger checkpoint: **79/106**;
- full-green 79 baseline: `main@a7d1804ea8149230526b8e8473389997f2469ede`;
- P-REC-03 proof main: `b337cb8a15e0996f6c285bd073773832fb21500e`;
- P-REC-03 proof resulting-main CI: `34987526584` — success;
- ledger branch: `formal/ledger-80-prec03`;
- this branch stages **80/106**;
- remaining not-yet-counted P-IDs after staging: **26**;
- active uncounted proof lanes after this staging: **0**.

**Do not call 80/106 full-green until this ledger/recovery branch passes its own
branch CI, PR CI, lands on `main`, and the resulting main CI succeeds.**

## P-REC-03 — proof complete, ledger promotion running

Frozen Core 3 P-REC-03 is represented at source strength:

1. homogeneous discrete-time Markov kernel `P` and measurable target set `A`;
2. first hitting time `τ_A` and potential `V_A(x)=E_x τ_A`;
3. pathwise first-step recursion before any Markov argument;
4. one-step homogeneous path-law restart derived from the existing Ionescu–Tulcea construction;
5. initial-law mixture and one-step marginal transport identify `P V_A`;
6. an ENNReal first-step identity is proved without a finiteness shortcut;
7. finite `V_A(x)` is used only for the real-valued endpoint;
8. the final conclusion outside `A` is `P V_A(x)-V_A(x)=-1`;
9. no finite-state weakening or assumed restart/Poisson identity is introduced.

Canonical theorem:
- `UEOT.V3.RecoveryHittingPoisson.p_rec_03`.

Evidence:
- feature `formal/prec03-first-step-v1@1e01c64824f2e3441b8492cc1f8731895eed467f`;
- feature official root CI `34985193231` success;
- source semantic audit complete;
- prohibited-proof audit clean;
- clean integration `formal/prec03-main-integration-v1@5142964d87fe53be7b0598d428c49991f50c837f`;
- clean integration CI `34985962098` success;
- proof PR #87 PR CI `34986723827` success;
- proof main `b337cb8a15e0996f6c285bd073773832fb21500e`;
- proof resulting-main CI `34987526584` success.

Exact next action: complete the separate **80/106** ledger/recovery branch → PR →
main resulting-CI lifecycle.

## Previous full-green promotion — P-REC-04

P-REC-04 is already counted in the 79/106 baseline at
`main@a7d1804ea8149230526b8e8473389997f2469ede`; ledger resulting-main CI
`34886982624` succeeded.

Once this ledger lifecycle closes, Recovery is counted complete as
P-REC-01/P-REC-02/P-REC-03/P-REC-04.

## Branchless next-front audit

No second proof branch is open during the P-REC-03 ledger lifecycle.

- **P-COMP-01:** provisional next lane; frozen source requires arbitrary finite nontrivial partitions and a genuine conditional-product-law equivalence, not only binary conditional mutual information.
- **P-PER-02:** non-quick; requires Polish/Feller, tight time-averaged laws, Prokhorov subsequences, Feller invariance and Portmanteau support preservation.
- **P-ALI-01 / P-KL-04/05 / P-EVO-03/04:** remain larger source-strength foundations.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green or proof-main green never increments coverage;
- no `sorry`, `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; do not replace hard clauses by convenient finite/toy/assumed-conclusion surrogates;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level.

## Recovery order

1. `NEW_CHAT_BOOTSTRAP.md`;
2. `docs/REPOSITORY_BRANCH_GOVERNANCE.md`;
3. `UEOT_CORE3_LEAN_OPERATIONS.md`;
4. Issue #56 when available;
5. `PID_STATUS.yaml`;
6. `FORMALIZATION_STATE.md`;
7. `V3_COVERAGE_STATUS.md`;
8. this `HANDOFF_LATEST.md` fallback snapshot;
9. live main/branches/CI reconciliation.
