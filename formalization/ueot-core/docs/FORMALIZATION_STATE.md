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
| integrated proved, staged by this checkpoint | **81** |
| active proof / feature-green uncounted | **0** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **25** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **80/106** at
`main@e8749f66cf88817ae7df7703c6c55b1fc9c2cdd1`, with ledger resulting-main CI
`34991002841` success. P-COMP-01 has completed all source, feature, clean-
integration, PR and proof-main gates, including resulting-main CI `35015386126`
success at `main@c5ae119adad2e533205f58e9b95d8ffc5d6713df`.
This ledger branch stages **81/106**. Do not call 81/106 full-green until the
ledger branch passes branch CI, PR CI, lands on `main`, and the resulting-main
CI succeeds.

## Newly staged proof — P-COMP-01

Frozen Core 3 P-COMP-01 is represented at its declared conditional path-
integration scope:

1. one common joint source law `ρ : Measure (U × (∀ i, X i))` supplies every partition score;
2. Mathlib's canonical `ρ.condKernel` is tied back to that same `ρ` by the explicit disintegration identity `ρ.fst ⊗ₘ ρ.condKernel = ρ`;
3. partitions are actual finite set partitions of the common child-index set, with the complete finite family of all nontrivial partitions used in the minimum;
4. each partition only reblocks the same joint path coordinates; the reblocking and inverse are constructed and machine-checked rather than postulated as unrelated kernels;
5. `I_π` is the conditional KL between the reblocked common joint law and the product of its conditional block marginals;
6. `I_π = 0` iff the blocks of `π` are conditionally independent given `U`;
7. the exact finite all-partition margin is positive iff no nontrivial partition factorizes;
8. Standard-Borel/nonemptiness assumptions are only regular-conditional-probability infrastructure for the source joint-law bridge;
9. the historically rejected design with an unrelated conditional kernel for each partition is not used.

Canonical theorem surface:
- `UEOT.V3.CompositionPathSource.p_comp_01`.

Promotion evidence:
- feature branch `formal/pcomp01-multiblock-v1`;
- final feature head `70a9dc7a26e0f80ed03633efda00a48927a80e5e`;
- feature official root CI `35011604866`: success;
- source semantic audit: complete;
- prohibited-proof audit on the proof PR diff: clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration branch `formal/pcomp01-main-integration-v1`;
- clean integration head `5f0e0b0ba56c1f97024ac8568275e1bc9db257a4`;
- clean integration official root CI `35014183716`: success;
- proof PR #89 PR-triggered CI `35014787206`: success;
- proof main `c5ae119adad2e533205f58e9b95d8ffc5d6713df`;
- proof resulting-main CI `35015386126`: success.

## Previous full-green checkpoint — 80/106

P-REC-03 is closed and counted in the 80/106 baseline at
`main@e8749f66cf88817ae7df7703c6c55b1fc9c2cdd1`. Its proof resulting-main CI
`34987526584` and ledger resulting-main CI `34991002841` succeeded.

Recovery P-REC-01/P-REC-02/P-REC-03/P-REC-04 remains fully counted. P-PER-04,
P-QSD-03, P-BRG-01, P-REF-04 and P-REF-05 remain previously counted; wrapper
work must not be double-counted.

## Grounded non-quick fronts

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

## Candidate next fronts after 81 full-green

- **P-COMP-02:** next Composition-family source-first audit candidate; do not assume it follows automatically from P-COMP-01.
- **P-PER-02:** remains a larger analytic lane rather than a quick wrapper.

No second proof branch is opened while the P-COMP-01 ledger gate is active.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available, `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green or proof-main green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent source/API audit without opening a conflicting proof branch.
