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
| integrated/proof-complete, staged by this checkpoint | **103** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **3** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **102/106**.
P-KL-04 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@7af0d8970a33063bb31a216bce97235a380571c0`; proof resulting-main root CI
`36224107001` succeeded.

This ledger branch stages **103/106**. Do not call 103/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-KL-04

Frozen Core 3 §22.4 is the finite continuous-time Markov-chain path KL identity.
The implementation constructs normalized full finite-jump path laws for the
controlled and baseline generators, proves support-driven absolute continuity
and the path-law likelihood relation, derives Campbell/renewal equalities from
path densities, proves integrability of the signed jump-log plus escape-rate
decomposition, and identifies the holding reward with the literal clock-time
source integral.

Canonical theorem:
- `UEOT.V3.FiniteCTMCPathKL.p_kl_04`.

Promotion evidence:
- final frozen-source/proof audit: CLEAR, zero blockers;
- feature commit `79bc6873d9b445627f70017ae37c43e498332158`;
- feature tree `79049834494228824abbe6a7de487f790f926edc`;
- feature root CI `36222018778`: success;
- focused/root/full local checks: success (`9008/9008`);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pkl04-main-integration@1117010ab9554ab073d47a6f7f16e7fc78ada214`
  from `main@91547a488ba9a1a86abbb4e5ead7ad5aa98b6bde`;
- feature/integration tree hash identical:
  `79049834494228824abbe6a7de487f790f926edc`;
- integration root CI `36222441619`: success;
- proof PR #137 exact-head root CI `36222997612`: success;
- proof main `7af0d8970a33063bb31a216bce97235a380571c0`;
- proof resulting-main root CI `36224107001`: success.

## Previous FULL-GREEN checkpoint — 102/106

P-CTL-02 and all earlier counted P-IDs remain closed. The 102/106 ledger landed
at `main@91547a488ba9a1a86abbb4e5ead7ad5aa98b6bde` with resulting-main CI
`36156516104` success.

P-KL-04 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 103 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful 103/106
promotion, the remaining P-IDs are exactly P-QSD-04, P-CTL-03, and P-KL-05.

The next theorem lane must be selected dynamically from the exact 103/106
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
