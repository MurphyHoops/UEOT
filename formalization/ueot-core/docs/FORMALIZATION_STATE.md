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
| integrated proved, staged by this checkpoint | **82** |
| active proof / feature-green uncounted | **0** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **24** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **81/106** at
`main@0797123efc63f39ffd2169b1e9b9e86472419919`, with ledger resulting-main CI
`35067746154` success. P-COMP-02 has completed its source audit, feature,
clean-integration, PR and proof-main gates. Its proof landed at
`main@61135398787bb49e1a19f54903dcb75beea870d4`, and proof resulting-main CI
`35080641545` succeeded.

This ledger branch stages **82/106**. Do not call 82/106 full-green until the
ledger branch passes branch CI, PR CI, lands on `main`, and the resulting-main
CI succeeds.

## Newly staged proof — P-COMP-02

Frozen Core 3 P-COMP-02 is represented at its declared general probability-law
scope. For original record law `P`, declared cut law `Q`, and
`M=(P+Q)/2`, the implementation uses Mathlib's genuine KL divergence and proves:

1. `M` is the actual midpoint probability measure;
2. `P ≤ 2M` and `Q ≤ 2M`, hence both laws are absolutely continuous with respect to `M`;
3. the corresponding RN densities are bounded by two almost everywhere;
4. KL-integrand integrability is proved before any `ENNReal.toReal` conversion;
5. the exact affine `klFun` bound over `[0,2]` gives each `KL(·||M) ≤ log 2`;
6. therefore `0 ≤ JS(P,Q) ≤ log 2`;
7. `JS(P,Q)=0 ↔ P=Q` follows from KL converse Gibbs;
8. over a finite declared cut family, the exact minimum JS is positive iff every cut changes the declared record law;
9. zero observed cut effect is not interpreted as absence of microscopic coupling without additional observation-completeness / cut-faithfulness assumptions.

Canonical theorem surface:
- `UEOT.V3.CompositionInterventionJS.jsDiv_mem_Icc_logTwo`;
- `UEOT.V3.CompositionInterventionJS.jsDiv_eq_zero_iff`;
- `UEOT.V3.CompositionInterventionJS.cutJSMargin_pos_iff`.

Promotion evidence:
- feature `formal/pcomp01-multiblock-v1@2bd7642058f6da329ff8e0fb2a8fa5d1b72adb50`;
- feature official root CI `35077241084`: success;
- prohibited-proof audit clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration `formal/pcomp01-main-integration-v1@2bd7642058f6da329ff8e0fb2a8fa5d1b72adb50`;
- clean integration official root CI `35077915553`: success;
- proof PR #91 PR-triggered CI `35079990097`: success;
- proof main `61135398787bb49e1a19f54903dcb75beea870d4`;
- proof resulting-main CI `35080641545`: success.

## Previous full-green checkpoint — 81/106

P-COMP-01 is already counted in the 81/106 baseline at
`main@0797123efc63f39ffd2169b1e9b9e86472419919`; ledger resulting-main CI
`35067746154` succeeded. Recovery P-REC-01/P-REC-02/P-REC-03/P-REC-04,
P-PER-04, P-QSD-03, P-BRG-01, P-REF-04 and P-REF-05 remain previously counted;
wrapper work must not be double-counted.

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

## Candidate next source-to-main audits after 82 full-green

- **P-QUO-01 / P-QUO-02:** current main already contains `StructuredQuotient` and finite stable-partition infrastructure, so audit for an A/B bridge first. The frozen controlled Bellman/value-policy statements must still be matched exactly; generic quotient-law results are insufficient.
- **P-PER-02:** remains a larger analytic lane rather than a quick wrapper.

No second proof branch is opened while the P-COMP-02 ledger gate is active.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available, `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green or proof-main green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent source/API audit without opening a conflicting proof branch.
