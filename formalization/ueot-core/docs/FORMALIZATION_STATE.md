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
| integrated/proof-complete, staged by this checkpoint | **96** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **10** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **95/106**.
P-EVO-04 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@ab9c4c220f442eec2b2e14709a3285e6dd01a066`; proof resulting-main root CI
`35560658256` succeeded.

This ledger branch stages **96/106**. Do not call 96/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-EVO-04

Frozen Core 3 §25.5 starts from a finite-type branching population satisfying
`E[Z_{n+1}|F_n]=Z_nM`. With K-PF-01 inputs `R>0`, `r>0`, `Mr=Rr`, it
requires the normalized reproductive value
`W_n=R^{-n}Z_nr` to be a nonnegative integrable martingale with
`EW_n=Z_0r` for finite deterministic initial counts.

The formalization keeps the vector conditional-mean identity literal, derives
the scalar recursion through a finite continuous-linear reproductive-value
readout, proves exact normalization by `R`, then derives adaptedness,
integrability, nonnegativity, the actual martingale, and constant expectation.
It adds no uniform-integrability, `L¹)-convergence, limit-identification, or
nonextinction-positivity conclusion forbidden by the source boundary.

Canonical theorem:
- `UEOT.V3.EvolutionReproductiveMartingale.p_evo_04`.

Supporting module:
- `UEOT.V3.EvolutionReproductiveMartingale`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- feature commit `f09c411f41c4386089cab17f6fcdc536314b762c`;
- feature tree `f162b2c9a1f34d55d58185eaaa9dfe0f94b2f540`;
- feature root CI `35539758527`: success;
- full local `lake build UEOT`: success (`8988` jobs);
- two independent final source/proof audits: PASS;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for
  `EvolutionReproductiveMartingale.p_evo_04`: only standard `propext`,
  `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pevo04-main-integration@1c167457bbfa27f7ec3f60861479aba6f75303f5`
  from `main@ee529be7008b38dbe928223ef1beebbd49db0912`;
- feature/integration tree hash
  `f162b2c9a1f34d55d58185eaaa9dfe0f94b2f540` identical;
- clean integration root CI `35559166344`: success;
- proof PR #123 root CI `35560162916`: success;
- proof main `ab9c4c220f442eec2b2e14709a3285e6dd01a066`;
- proof resulting-main root CI `35560658256`: success.

## Previous FULL-GREEN checkpoint — 95/106

P-GOA-03 and all earlier counted P-IDs remain closed. The 95/106 ledger landed
at `main@ee529be7008b38dbe928223ef1beebbd49db0912` with resulting-main CI
`35538326271` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Branchless frontier after the 96 ledger closes

No theorem branch is opened by this ledger lifecycle. The next lane must be
selected from an exact 96/106-main source/dependency audit. P-CORE-01 remains a
read-only candidate; P-EVO-03 remains uncounted and requires the full K-PF-01
asymptotic package; P-PER-02 / P-QSD-01 remain read-only alternatives requiring
continuous-time semigroup / occupation-measure infrastructure.

The next theorem lane must be selected dynamically from the exact 96/106
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
