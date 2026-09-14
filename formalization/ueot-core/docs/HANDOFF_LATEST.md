# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- source P-IDs: **106**;
- authoritative full-green baseline before this ledger checkpoint: **78/106**;
- full-green 78 baseline: `main@22f536ea27eecf78de5005f47ecfea21edd001c6`;
- P-REC-04 proof main: `4946a4435d3c15efbf0ca13aed7b44e65defc79c`;
- P-REC-04 proof resulting-main CI: `34882613059` — success;
- ledger branch: `formal/ledger-79-prec04`;
- this branch stages **79/106**;
- remaining not-yet-counted P-IDs after staging: **27**;
- active uncounted proof lanes after this staging: **0**.

**Do not call 79/106 full-green until this ledger/recovery branch passes its own
branch CI, PR CI, lands on `main`, and the resulting main CI succeeds.**

## P-REC-04 — proof complete, ledger promotion running

Frozen Core 3 P-REC-04 is represented at source strength:

1. homogeneous discrete-time Markov kernel `P`;
2. measurable target set `A`;
3. measurable nonnegative Lyapunov potential `V`;
4. positive finite recovery drift `c`;
5. outside `A`, the source drift is encoded equivalently as `PV + c <= V`;
6. the path law is derived from `P` through the existing Ionescu–Tulcea infrastructure;
7. the nonnegative hitting time is built from survival-tail truncations in `ENNReal`;
8. one-step survival potential obeys the kernel drift recurrence;
9. finite horizons telescope and the full expectation follows by monotone convergence;
10. no finite-state weakening, assumed stopped bound, or global future-integrability premise is introduced.

Canonical theorem:
- `UEOT.V3.RecoveryHittingBound.p_rec_04_hitting_time_bound`.

Evidence:
- feature `formal/prec04-drift-hitting-time-v1@3ea9086976ac595eb034a125390d69264e12772e`;
- feature CI `34875538212` success;
- source semantic audit complete;
- prohibited-proof audit clean;
- clean integration `formal/prec04-main-integration-v1@50ac5834ff74fe4aa5229b60be87a256e762c778`;
- clean integration CI `34877803577` success;
- proof PR #85 PR CI `34880820942` success;
- proof main `4946a4435d3c15efbf0ca13aed7b44e65defc79c`;
- proof resulting-main CI `34882613059` success.

Exact next action: complete the separate **79/106** ledger/recovery branch → PR →
main resulting-CI lifecycle.

## Previous full-green promotion — P-PER-04

P-PER-04 is already counted in the 78/106 baseline at
`main@22f536ea27eecf78de5005f47ecfea21edd001c6`. Its proof resulting-main CI
`34863965181` and ledger resulting-main CI `34866495921` succeeded.

P-QSD-03 is also already counted and remains distinct from P-QSD-01/P-QSD-04.

## Branchless next-front audit

No second proof branch is open during the P-REC-04 ledger lifecycle.

- **P-REC-03:** natural next recovery lane; must derive the real Markov first-step identity `PV_A - V_A = -1` outside `A`.
- **P-PER-02:** non-quick; requires Polish/Feller, tight time-averaged laws, Prokhorov subsequences, Feller invariance and Portmanteau support preservation.
- **P-COMP-01:** binary CMI/KL infrastructure exists, but the frozen arbitrary finite-partition and multi-block product-law equivalence remains missing.

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
