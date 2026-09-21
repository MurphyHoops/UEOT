# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-21**

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
| integrated/proof-complete, staged by this checkpoint | **97** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **9** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **96/106**.
P-CORE-01 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@1a6d7d90d06988e0e0bda7a29061df955dfd0096`; proof resulting-main root CI
`35570915485` succeeded.

This ledger branch stages **97/106**. Do not call 97/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-CORE-01

Frozen Core 3 §31.1 assembles the finite operational certificate on one common
high-probability event. The source-facing Lean theorem keeps the true source
objects fixed across samples and combines exact predictive/carrier recovery,
quotient control, action-gap certification, same-policy finite path stability,
conditional mixing/recurrent GOA stability, P-ID history transport, and the
source-direction integrity margin.

The implementation uses one lifted greedy policy for the control/path/GOA ports,
derives the `D`/`2D` bounds from the approximation data, places optional
mixing/recurrent/history clauses inside the same `CorePointwiseCertificate`, and
uses `HEq` plus policy-kernel equalities to prevent recurrent-source substitution.
Shared failure keys are deduplicated through the common-event construction.

Canonical theorem:
- `UEOT.V3.CoreOperationalAssembly.p_core_01`.

Supporting module:
- `UEOT.V3.CoreOperationalAssembly`.

Promotion evidence:
- two independent final source/proof audits: GREEN;
- feature commit `bad381814a902047ece0f813d6b3385c71bc9db1`;
- feature tree `85ba74aaa1fbabb36a1b766ad8cd32f34e70f185`;
- feature root CI `35569184015`: success;
- full feature `lake build UEOT`: success (`8989` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pcore01-main-integration@a34423f7abd99a172605eb6a321e39c5c45921fb`
  from `main@5a18daa6a14edd0dc609fd0db72661e422991b17`;
- feature/integration tree hash identical;
- integration full local `lake build UEOT`: success (`8989` jobs);
- integration root CI `35569862884`: success;
- proof PR #125 exact-head root CI `35570425596`: success;
- proof main `1a6d7d90d06988e0e0bda7a29061df955dfd0096`;
- proof resulting-main root CI `35570915485`: success.

## Previous FULL-GREEN checkpoint — 96/106

P-EVO-04 and all earlier counted P-IDs remain closed. The 96/106 ledger landed
at `main@5a18daa6a14edd0dc609fd0db72661e422991b17` with resulting-main CI
`35562298378` success.

P-CORE-01 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 97 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful 97/106
promotion, the remaining P-IDs are exactly P-PER-02, P-QSD-01, P-QSD-04,
P-CTL-02, P-CTL-03, P-KL-04, P-KL-05, P-ALI-01, and P-EVO-03.

The next theorem lane must be selected dynamically from the exact 97/106
FULL-GREEN main after this ledger finishes, rather than being opened early from
this staged branch.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available,
   `V3_COVERAGE_STATUS.md`, this file, then the fallback handoff.
2. Reconcile live `main`, active branches, PRs and Actions before mutation.
3. Never reopen counted green P-IDs absent a substantive frozen-source mismatch
   or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green, integration green and proof-main green never increment
   coverage.
6. No `sorry`, Lean `admit`, `native_decide`, or unsourced `axiom`.
7. Use CI waiting time for source/API audit only; do not open a conflicting
   proof lane while a promotion lifecycle is active.
8. After a proof resulting-main succeeds, use a separate docs-only ledger
   lifecycle before incrementing source coverage.
