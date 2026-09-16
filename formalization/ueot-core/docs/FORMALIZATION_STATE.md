# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log when available.

Last synchronized: **2026-09-16**

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
| integrated proved, staged by this checkpoint | **83** |
| active proof / feature-green uncounted | **0** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **23** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **82/106** at
`main@86a2cd21e4693ae084e7bc904d38046f9b3a1519`, with ledger resulting-main CI
`35083749972` success. P-CTL-01 has now completed its source audit, feature,
clean-integration, PR and proof-main gates. Its proof landed at
`main@3efe7ebc74d8f2a6705c12a5218a7880f5a3688c`, and proof resulting-main CI
`35104140440` succeeded.

This ledger branch stages **83/106**. Do not call 83/106 full-green until the
ledger branch passes branch CI, PR CI, lands on `main`, and the resulting-main
CI succeeds.

## Newly staged proof — P-CTL-01

Frozen Core 3 P-CTL-01 is formalized at its finite discounted-control source
scope. The model retains finite states, state-dependent finite nonempty action
sets, bounded rewards, stochastic transition laws and `0 < beta < 1`.

The proof establishes:

1. Bellman is a global `beta` contraction in the finite-state sup metric;
2. the Bellman fixed point `V*` exists and is unique;
3. value iteration converges to `V*` from every initial value function;
4. the Bellman residual stopping certificate is machine checked;
5. arbitrary causal randomized policies are represented with arbitrary time-indexed memory, allowing complete history dependence rather than a Markov-only restriction;
6. finite-horizon causal values obey Bellman domination with an explicit geometric terminal tail;
7. bounded rewards make every finite-horizon value sequence Cauchy, yielding a well-defined infinite discounted value;
8. every causal history-dependent randomized policy has infinite value at most `V*`;
9. the Bellman greedy selector is encoded as a stationary deterministic causal policy whose infinite value equals `V*` statewise.

Canonical theorem:
- `UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality`.

Supporting source-facing facts:
- `UEOT.V3.FiniteDiscountedControl.Model.fixedPoint_unique`;
- `UEOT.V3.FiniteDiscountedControl.Model.valueIteration_tendsto`;
- `UEOT.V3.FiniteDiscountedControl.Model.valueError_le_residual`;
- `UEOT.V3.FiniteDiscountedControl.CausalPolicy.infiniteValue_le_optimal`;
- `UEOT.V3.FiniteDiscountedControl.greedy_infiniteValue_eq_optimal`.

Promotion evidence:
- feature `formal/pcomp01-multiblock-v1@47218ef06c63ed81ab3974d107f0d3d46cc49ecb`;
- feature official root CI `35098260086`: success;
- prohibited-proof audit clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration `formal/pcomp01-main-integration-v1@45440746a7086b74bc65ba741611f98a8da92f27`;
- clean integration official root CI `35099296408`: success;
- proof PR #93 PR-triggered CI `35102272835`: success;
- proof main `3efe7ebc74d8f2a6705c12a5218a7880f5a3688c`;
- proof resulting-main CI `35104140440`: success.

## Previous full-green checkpoint — 82/106

P-COMP-02 and all earlier counted P-IDs are already counted in the 82/106
baseline at `main@86a2cd21e4693ae084e7bc904d38046f9b3a1519`; ledger resulting-main CI
`35083749972` succeeded. P-TEL-01 is already counted and must not be reopened
merely because older compilation reports predate its later promotion.

## Grounded non-quick fronts

- P-CTL-02: compact-metric/Feller discounted control with continuity and measurable-selection infrastructure.
- P-PER-02: Polish/Feller occupation-law theorem with tightness, Prokhorov and Portmanteau; sample-path empirical-frequency weakening is forbidden.
- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/04: source-locked distinct non-A results.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; do not count an assumed-convergence
surrogate.

## Candidate next source-to-main audits after 83 full-green

- **P-QUO-01:** high-leverage after P-CTL-01. Frozen source requires a surjective control quotient with identical same-fiber action sets, reward closure and every-action pushforward transition closure; Bellman intertwining plus fixed-point uniqueness must yield exact value lifting and macro-optimal-policy lifting.
- **P-QUO-02:** follows the approximate version only after matching the span-sensitive P-MET-02 residual interface.
- **P-CTL-02:** larger analytic lane requiring compact/Feller and measurable-selection machinery.

No new proof branch is opened while the P-CTL-01 ledger gate is active. Remote
branch count is above the repository hard cap; after this promotion closes,
branch hygiene must run before a new proof lane opens.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available, `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green or proof-main green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent source/API audit without opening a conflicting proof branch.
