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
| integrated/proof-complete, staged by this checkpoint | **102** |
| active theorem proof branch | **0** |
| pending/not yet counted after this promotion | **4** |
| total | **106** |

The authoritative FULL-GREEN baseline before this ledger branch is **101/106**.
P-CTL-02 has completed source audit, feature validation, clean integration,
proof PR, proof-main and proof resulting-main gates. Its proof is on
`main@6a334b4c9870cf73ecda97a65965f822cf5e9e26`; proof resulting-main root CI
`36142098525` succeeded.

This ledger branch stages **102/106**. Do not call 102/106 FULL-GREEN until the
ledger branch passes root CI, the ledger PR passes root CI, the ledger lands on
`main`, and that resulting-main root CI succeeds.

## Newly staged proof — P-CTL-02

Frozen Core 3 §19.3 states the compact discounted-control theorem for compact
metric state/action spaces, fixed nonempty action space, continuous reward,
weakly continuous Markov kernel, and `0 < β < 1`: the Bellman operator on
`C(X, ℝ)` is a `β`-contraction with a unique continuous fixed point and a
measurable stationary optimal selector.

The implementation represents weak continuity by continuity of every
continuous-test-function integral and proves this equals continuity in
Mathlib's weak topology on probability measures. Compact maximization gives a
Bellman self-map of `C(X, ℝ)`; sup-norm estimates prove the contraction and
Banach gives the unique continuous fixed point. A measurable maximizer is
constructed directly from shrinking compact neighborhoods of a dense sequence
and a measurable Cauchy limit, without assuming a general selection theorem.
Finally, full-history randomized causal policies are evaluated by nested
kernel recursion; Bellman domination bounds all of them and the measurable
stationary deterministic greedy policy attains the fixed-point value.

Canonical theorem:
- `UEOT.V3.CompactFellerControl.Model.p_ctl_02`.

Supporting modules:
- `UEOT.V3.CompactArgmaxSelector`;
- `UEOT.V3.CompactCausalOptimalityCore`;
- `UEOT.V3.CompactFellerControl`.

Promotion evidence:
- final frozen-source/proof audit: CLEAR, zero blockers;
- feature commit `4b17ec1219f95dd9fa0480f46beea6e585c122eb`;
- feature tree `7497670441126d08f2fdb91b15ada086d2a9565f`;
- feature root CI `36139857404`: success;
- focused module, root import, and full feature checks: success (`8996` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pctl02-main-integration@863c9679b9d025a5f58282af4548fe5587e37860`
  from `main@7add6a361c8c46f7539d48ace389d403219b053d`;
- feature/integration tree hash identical:
  `7497670441126d08f2fdb91b15ada086d2a9565f`;
- integration root CI `36140869360`: success;
- proof PR #135 exact-head root CI `36141205611`: success;
- proof main `6a334b4c9870cf73ecda97a65965f822cf5e9e26`;
- proof resulting-main root CI `36142098525`: success.

## Previous FULL-GREEN checkpoint — 101/106

P-ALI-01 and all earlier counted P-IDs remain closed. The 101/106 ledger landed
at `main@7add6a361c8c46f7539d48ace389d403219b053d` with resulting-main CI
`36125245565` success.

P-CTL-02 is proof-complete but remains staged, not counted FULL-GREEN, until
this separate ledger lifecycle completes.

## Branchless frontier after the 102 ledger closes

No theorem branch is opened by this ledger lifecycle. After a successful 102/106
promotion, the remaining P-IDs are exactly P-QSD-04, P-CTL-03, P-KL-04, and
P-KL-05.

The next theorem lane must be selected dynamically from the exact 102/106
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
