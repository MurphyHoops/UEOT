# UEOT Core Lean — Live Formalization State

> Recovery entry point. Integrated source-count truth is `V3_COVERAGE_STATUS.md`.
> GitHub Issue #56 carries the live cross-chat construction log and overrides
> stale fallback snapshots.

Last synchronized: **2026-09-20**

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
| integrated/proof-complete, staged by this checkpoint | **91** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **15** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **90/106**.
P-DDH-03 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@6e2a179d9fad8293b02b0f47a971f4083eabbeb3`; proof resulting-main root CI
`35514827747` succeeded.

This ledger branch stages **91/106**. Do not call 91/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-DDH-03

Frozen Core 3 §23.3 requires a finite state space, strictly positive baseline
`p0`, a prescribed finite-dimensional feature map and an arbitrary finite
parameter whose exponential tilt realizes the target moment. That tilt must
minimize `KL(· || p0)` over every probability law with the same moment, with
equality only for the tilt itself. The source deliberately makes no claim that
boundary moment targets have a finite-parameter realization.

The formalization quantifies the competitor directly as an arbitrary probability
measure, proves full-support absolute continuity, derives the KL Pythagorean
identity from Mathlib's tilted log-likelihood-ratio identities, and establishes
all ENNReal finiteness gates before transferring order/equality through
`toReal`. No rank, feature-independence, strict-convexity, PD-covariance,
unique-parameter, or interior hypothesis is added.

Canonical theorem:
- `UEOT.V3.ExponentialFamilyIProjection.p_ddh_03`.

Supporting module:
- `UEOT.V3.ExponentialFamilyIProjection`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- feature commit `360f5b941d57a5d0b2edf73924c217034dfd0bcd`;
- feature root CI `35513672240`: success;
- full local `lake build UEOT`: success (`8983` jobs);
- two independent final source/proof audits: PASS;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms` for `ExponentialFamilyIProjection.p_ddh_03`: only standard `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pddh03-main-integration@4bce0870076e740f21e14411b8741493c4d61e84` from `main@22a0b0d68201a18d574c0d841679f511a86994b9`;
- feature/integration tree hash `1c0278bb9b21501ebb30733ed77f2cb48f3228a0` identical;
- clean integration root CI `35514069336`: success;
- proof PR #113 root CI `35514474988`: success;
- proof main `6e2a179d9fad8293b02b0f47a971f4083eabbeb3`;
- proof resulting-main root CI `35514827747`: success.

## Previous FULL-GREEN checkpoint — 90/106

P-DDH-04 and all earlier counted P-IDs remain closed. The 90/106 ledger landed
at `main@22a0b0d68201a18d574c0d841679f511a86994b9` with resulting-main CI
`35511293247` success.

P-QUO-03 and P-TEL-01 are already counted and must not be reopened or
re-counted merely because older compilation reports predate their promotion.

## Branchless frontier after the 91 ledger closes

No theorem branch is opened by this ledger lifecycle. Current read-only audits
place the leading uncounted fronts at:

- P-DDH-02: Class C, M / upper-M; finite log-partition gradient and
  Hessian/covariance, with gradient/raw-Hessian probes already compiling;
- P-GOA-04: Class C, L; finite spectral infrastructure exists but several
  source-strength perturbation bridges remain;
- P-DDH-05: Class D, L after deeper singular-value perturbation audit;
- P-GOA-03: Class D, L-XL; recurrent decomposition and full Cesaro-mixture
  machinery are still missing.

P-CORE-01 remains hard-blocked by P-GOA-03. The next theorem lane must be
selected dynamically from the exact 91/106 FULL-GREEN main after this ledger
finishes, rather than being opened early from this staged branch.

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
