# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log when available.

Last synchronized: **2026-09-15**

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
| integrated proved, staged by this checkpoint | **79** |
| active proof / feature-green uncounted | **0** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **27** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **78/106** at
`main@22f536ea27eecf78de5005f47ecfea21edd001c6`, with ledger resulting-main CI
`34866495921` success. P-REC-04 has completed all source, feature, clean-
integration, PR and proof-main gates, including resulting-main CI `34882613059`
success at `main@4946a4435d3c15efbf0ca13aed7b44e65defc79c`.
This ledger branch stages **79/106**. Do not call 79/106 full-green until the
ledger branch passes branch CI, PR CI, lands on `main`, and the resulting-main
CI succeeds.

## Newly staged proof — P-REC-04

Frozen Core 3 P-REC-04 is represented at its declared discrete-time Markov
recovery scope:

1. `P` is a homogeneous Markov transition kernel;
2. `A` is a measurable target/hit set;
3. `V` is a measurable nonnegative potential;
4. the source drift outside `A` is encoded as the equivalent nonnegative form `PV + c <= V`;
5. `c` is positive and finite;
6. the Markov path law is derived from `P`, not postulated as an independent process assumption;
7. hitting time is represented by its nonnegative survival-tail truncations;
8. the one-step survival-potential drift is integrated and telescoped over finite horizons;
9. monotone convergence gives the full hitting-time expectation;
10. no finite-state specialization, assumed stopped inequality, or global future-integrability premise is introduced.

Canonical theorem surface:
- `UEOT.V3.RecoveryHittingBound.p_rec_04_hitting_time_bound`.

Promotion evidence:
- feature branch `formal/prec04-drift-hitting-time-v1`;
- final feature head `3ea9086976ac595eb034a125390d69264e12772e`;
- feature CI `34875538212`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean;
- clean integration branch `formal/prec04-main-integration-v1`;
- clean integration head `50ac5834ff74fe4aa5229b60be87a256e762c778`;
- clean integration CI `34877803577`: success;
- proof PR #85 PR-triggered CI `34880820942`: success;
- proof main `4946a4435d3c15efbf0ca13aed7b44e65defc79c`;
- proof resulting-main CI `34882613059`: success.

## Previous full-green checkpoint — 78/106

P-PER-04 is closed and counted in the 78/106 baseline at
`main@22f536ea27eecf78de5005f47ecfea21edd001c6`. Its proof resulting-main CI
`34863965181` and ledger resulting-main CI `34866495921` succeeded.

P-QSD-03 is also closed and counted. P-BRG-01, P-REF-04 and P-REF-05 were
already counted before these cycles; wrapper work must not be double-counted.

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

## Candidate next fronts after 79 full-green

- **P-REC-03:** first-step Markov identity for the finite hitting-time potential; the genuine identity `PV_A - V_A = -1` outside `A` must be derived.
- **P-COMP-01:** binary conditional-mutual-info machinery exists, but arbitrary finite nontrivial partitions and multi-block conditional product laws remain.

No second proof branch is opened while the P-REC-04 ledger gate is active.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available, `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green or proof-main green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent source/API audit without opening a conflicting proof branch.
