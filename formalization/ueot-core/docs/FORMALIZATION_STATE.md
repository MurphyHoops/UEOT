# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-24**

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
| integrated/proof-complete, staged by this checkpoint | **100** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **6** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **99/106**.
P-QSD-01 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@ac17ea1a0859b364542fa4996de1e7458b94b53a`; proof resulting-main root CI
`35900895439` succeeded.

This ledger branch stages **100/106**. Do not call 100/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-QSD-01

Frozen Core 3 §10.1 states that total-variation convergence of the literal
conditioned killed-semigroup laws to `q`, together with positive finite-time
survival and right continuity at zero, forces `q` to be quasi-stationary with
an exponential survival law `exp(-λt)`, `λ >= 0`.

The implementation keeps one fixed initial law, derives the conditional shift
identity from semigroup composition and normalization, derives the QSD
eigenmeasure law from TV convergence, derives survival multiplicativity, and
then obtains the exponential law from positivity plus right continuity. It does
not assume the QSD identity, the shift identity, or the rate conclusion.

Canonical theorem:
- `UEOT.V3.QSDTVLimit.p_qsd_01`.

Supporting module:
- `UEOT.V3.QSDTVLimit`.

Promotion evidence:
- final source/proof audits: GREEN;
- feature commit `b9625635c10cc114e854bfc1e1d7b2af277a47d8`;
- feature tree `f269847d42b34f5c7cd30236e011aa841a0aafb7`;
- feature root CI `35624526524`: success;
- focused/root/full feature checks: success (`8992` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pqsd01-main-integration@10a37206f049684c292c53d7826087f05580d489`
  from `main@9b00f80e091a80cc335cd592e527d0e98253f5f7`;
- feature/integration tree hash identical:
  `f269847d42b34f5c7cd30236e011aa841a0aafb7`;
- integration focused/root/full local checks: success (`8992` jobs);
- integration root CI `35628806058`: success;
- proof PR #131 exact-head root CI `35629472501`, attempt 2: success;
- proof main `ac17ea1a0859b364542fa4996de1e7458b94b53a`;
- proof resulting-main root CI `35900895439`: success.

## Previous FULL-GREEN checkpoint — 99/106

P-PER-02 and all earlier counted P-IDs remain closed. The 99/106 ledger landed
at `main@9b00f80e091a80cc335cd592e527d0e98253f5f7` with resulting-main CI
`35605364675` success.

P-QSD-01 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 100 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful 100/106
promotion, the remaining P-IDs are exactly P-QSD-04, P-CTL-02, P-CTL-03,
P-KL-04, P-KL-05, and P-ALI-01.

The next theorem lane must be selected dynamically from the exact 100/106
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
