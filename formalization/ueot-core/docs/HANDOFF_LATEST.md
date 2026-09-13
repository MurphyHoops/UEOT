# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state. This file is the
> fallback archival snapshot on `main` and is updated at meaningful lifecycle
> transitions.

## Current lifecycle snapshot

- counted coverage staged by this ledger: **67/106**;
- not yet counted: **39**;
- proof main before this docs commit:
  `412815d611fc3c20e867fdf245fc15fbf1f9266f`;
- newest counted promotion: **P-COMP-04**;
- integration CI `34758385777`: success;
- post-main CI `34758642764`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean;
- **67/106 becomes full-green only after this ledger commit's own main CI succeeds.**

## P-COMP-04 — counted pending ledger CI

- branch `formal/pcomp04-parent-info`;
- feature head `d7b3446dcac54f62f7d28a141dd8649793b2586c`;
- feature CI `34757571535`: success;
- theorem `UEOT.V3.CompositionParentInformation.p_comp_04`;
- source-facing side information contains child cores plus `U`, while the
  canonical map is restricted to `C_P = g(M_P,U)`;
- clean integration branch `formal/pcomp04-main-integration`;
- integration/main proof commit `412815d611fc3c20e867fdf245fc15fbf1f9266f`;
- exact integration diff: theorem file + one top-level import;
- integration CI `34758385777`: success;
- post-main CI `34758642764`: success.

## Active proof lane — P-KL-03

- branch `formal/pkl03-path-chain`;
- same-initial theorem `p_kl_03` green at
  `ad67c92db2e9bf6fce561e16dcd0c9680072731f`;
- CI `34758129042`: success;
- latest source-facing proof head before this snapshot:
  `6f3e3e3a458da9ef3324783ae0e9423d48a78814`;
- latest CI `34761786961`: in progress;
- `p_kl_03_general` adds the frozen-source distinct-initial-law term
  `D_KL(μ0 || ν0)`;
- theorem remains finite-horizon and genuinely history-dependent;
- homogeneous-only replacement is forbidden.

## Source-audit lane — P-EVO-02

Frozen target: finite label `T`, independent of `(F,F')`, copied without error,
with exact identity
`I((F,T);(F',T)) = I(F;F') + H(T)`.
Reuse existing product/KL-chain/deterministic-copy infrastructure; do not count a
weaker inequality or renamed assumption.

## Exact next actions

1. require this 67/106 ledger commit's own main CI to succeed;
2. refresh Issue #56 with the full-green 67 checkpoint once that gate is green;
3. collect P-KL-03 CI `34761786961`; if red, decode the exact job log and repair only that error;
4. if P-KL-03 becomes source-closed/feature-green, clean-integrate from the latest full-green main, then post-main and ledger gates;
5. use CI time to advance the exact P-EVO-02 shared-label proof audit;
6. feature green never increments coverage.

## Guards

- do not reopen counted P-IDs absent source mismatch/CI regression;
- no `sorry`, `admit`, `native_decide`, unsourced `axiom`;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes concentration/extinction/maximizer-ratio clauses.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. live main/branches/CI.
