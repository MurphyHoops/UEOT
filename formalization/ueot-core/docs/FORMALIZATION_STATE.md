# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-25**

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
| integrated/proof-complete, staged by this checkpoint | **101** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **5** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **100/106**.
P-ALI-01 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@d7cfc9975aed004123b5a3cf9a71fb28f434bc56`; proof resulting-main root CI
`36115569409` succeeded.

This ledger branch stages **101/106**. Do not call 101/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-ALI-01

Frozen Core 3 §24.2 states that on a connected smooth manifold, a `C¹` one-form
`ω` is globally exact exactly when its integral around every piecewise-smooth
closed curve vanishes.

The implementation represents `ω` as a `C¹` cotangent-bundle section, defines
piecewise-smooth paths from smooth arcs with concatenation and reversal, proves
the exact-form direction by the one-dimensional FTC on each arc, and proves the
reverse direction from a basepoint path integral. Closed periods give path
independence; connectedness gives smooth reachability; a local chart-segment
primitive supplies the endpoint derivative `dV = ω`. No simply-connectedness or
global convexity hypothesis is added.

Canonical theorem:
- `UEOT.V3.AlignmentGlobalExactness.p_ali_01`.

Supporting module:
- `UEOT.V3.AlignmentGlobalExactness`.

Promotion evidence:
- final source/proof audits: GREEN;
- feature commit `2307932f13ec9079350589eeada692f636bb9bcb`;
- feature tree `a645f597f2a8be274aba5b60b2896dfb19e6ec7e`;
- feature root CI `36113464991`: success;
- focused module, root import, and full feature checks: success (`8993` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pali01-main-integration@e178a46ce0d9454f45ca78dcf98f6e4feaef918c`
  from `main@7981d9c0b66a2bd834d75acedb8e152e25120da9`;
- feature/integration tree hash identical:
  `a645f597f2a8be274aba5b60b2896dfb19e6ec7e`;
- integration focused/root/full local checks: success (`8993` jobs);
- integration root CI `36114241467`: success;
- proof PR #133 exact-head root CI `36114862119`: success;
- proof main `d7cfc9975aed004123b5a3cf9a71fb28f434bc56`;
- proof resulting-main root CI `36115569409`: success.

## Previous FULL-GREEN checkpoint — 100/106

P-QSD-01 and all earlier counted P-IDs remain closed. The 100/106 ledger landed
at `main@7981d9c0b66a2bd834d75acedb8e152e25120da9` with resulting-main CI
`35905352725` success.

P-ALI-01 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 101 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful 101/106
promotion, the remaining P-IDs are exactly P-QSD-04, P-CTL-02, P-CTL-03,
P-KL-04, and P-KL-05.

The next theorem lane must be selected dynamically from the exact 101/106
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
