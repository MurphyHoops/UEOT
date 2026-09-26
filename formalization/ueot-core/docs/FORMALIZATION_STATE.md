# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-26**

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
| integrated/proof-complete, staged by this checkpoint | **104** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **2** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **103/106**.
P-KL-05 has completed frozen-source audit, feature validation, clean
integration, proof PR, proof-main and proof resulting-main gates. Its proof is
on `main@15005abdb80bcf059077e08a33b2b80965b12b4e`; proof resulting-main
root CI `36229427792` succeeded.

This ledger branch stages **104/106**. Do not call 104/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-KL-05

Frozen Core 3 §22.5 separates full-noise-space Girsanov entropy from the KL of
the observed state trajectory. The implementation keeps the source Girsanov
setup explicit: progressive control, a.e. clock-time energy integrability,
density change, exponential density, and terminal stochastic-integral shift.
The controlled stochastic integral is the terminal value of a zero-start
martingale, so its integrability and zero mean are proved rather than assumed.
The exact full-space KL equality is then derived through the RN derivative,
while the state-path law receives only the measurable data-processing bound.

Canonical theorem:
- `UEOT.V3.GirsanovPathKL.TerminalGirsanovData.p_kl_05`.

Promotion evidence:
- feature head `c8bb0e2cf05e17be6c720b3493354165de712bd0`;
- feature root CI `36228481080`: success;
- clean integration `9b5623ded2c67fe972ca8507b73f94b312446bd6`
  from `main@e4590074b7d292e5c24e8f19ce79d198f543c69f`;
- feature/integration tree identity
  `9ff34d07229c17912c9b96655fe767867bb23621`;
- integration root CI `36228493685`: success;
- proof PR #139 exact-head root CI `36228972886`: success;
- proof main `15005abdb80bcf059077e08a33b2b80965b12b4e`;
- proof resulting-main root CI `36229427792`: success;
- full local build: success (`9009/9009`);
- prohibited-proof audit clean; audited axioms only `propext`,
  `Classical.choice`, `Quot.sound`.

## Previous FULL-GREEN checkpoint — 103/106

P-KL-04 and all earlier counted P-IDs remain closed. The 103/106 ledger landed
at `main@e4590074b7d292e5c24e8f19ce79d198f543c69f` with resulting-main CI
`36225697848` success.

P-KL-05 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 104 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful
104/106 promotion, the remaining P-IDs are exactly P-QSD-04 and P-CTL-03.

The next theorem lane must be selected dynamically from the exact 104/106
FULL-GREEN main after this ledger finishes, rather than being opened early
from this staged branch.
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
