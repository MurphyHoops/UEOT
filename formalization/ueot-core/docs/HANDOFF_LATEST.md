# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- source P-IDs: **106**;
- authoritative full-green baseline before this ledger checkpoint: **76/106**;
- full-green 76 baseline: `main@b461bdf8b37250fae9fca923ea243e1182f9e5cc`;
- P-QSD-03 proof main: `bab0b0718afaee90e858d71e41340066ba1774d8`;
- P-QSD-03 proof resulting-main CI: `34848676178` — success;
- ledger branch: `formal/ledger77-pqsd03`;
- this branch stages **77/106**;
- remaining not-yet-counted P-IDs after staging: **29**;
- active uncounted proof lanes after this staging: **0**.

**Do not call 77/106 full-green until this ledger/recovery branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.**

## P-QSD-03 — proof complete, ledger promotion running

Frozen Core 3 §10.3 is represented at full declared same-initial-law scope:

1. for `t ≥ t0`, conditional-stability error is bounded by `C exp(-γ t)`;
2. for the same initial law, survival probability is bounded below by `c exp(-λ t)`;
3. `C,c,γ,λ,ε,p > 0` and `p ≤ c`;
4. the usable closed window is
   `[max{t0,0,log(C/ε)/γ}, log(c/p)/λ]`;
5. every time in that nonempty window simultaneously has error at most `ε`
   and survival at least `p`;
6. endpoint equality is allowed.

Canonical theorem:
- `UEOT.V3.QSDDurationWindow.p_qsd_03`.

Evidence:
- feature `formal/pqsd03-duration-window-v1@11076f31eec199a4e80ba13e00e037c5e62a2de2`;
- feature CI `34831456183` success;
- source semantic audit complete;
- prohibited-proof audit clean;
- clean integration `formal/pqsd03-main-integration@8e85e687ea11a8dac89ebe7ebbab8240551d8f99`;
- clean integration CI `34847211649` success;
- PR #79 PR CI `34848043040` success;
- proof main `bab0b0718afaee90e858d71e41340066ba1774d8`;
- proof resulting-main CI `34848676178` success.

Exact next action: complete the separate 77/106 ledger/recovery PR lifecycle.

## Previous promotion — P-BRG-01

P-BRG-01 is already counted in the authoritative 76/106 baseline. Do not reopen
it absent a source mismatch or regression.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green never increments coverage;
- no `sorry`, `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; do not replace hard clauses by convenient finite/toy/Markov-only surrogates;
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
