# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log when available.

Last synchronized: **2026-09-14**

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
| integrated proved, staged by this checkpoint | **72** |
| active proof | **0** |
| source audit | **1** |
| blocked | **0** |
| pending/unclassified | **33** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **71/106** at
`main@5218e615d852c1ffee72107f35435ee378709166`, CI `34771573465` success.
P-ALG-01 has now completed all proof-side gates and this branch stages 72/106.
Do not call 72/106 full-green until this ledger branch passes PR CI, lands on
`main`, and the resulting main CI succeeds.

## Newly staged proof — P-ALG-01

Frozen §28.5 is implemented literally as an exact finite controlled stable
partition algorithm and quotient theorem. Canonical theorem:

- `UEOT.V3.PAlg01.p_alg_01`.

It exposes terminal fixed-point/stability, coarsestness among stable refinements
of the output/complete-reward initial partition, quotient output/reward and
all-action one-step preservation, stochastic normalization, and arbitrary
finite-horizon output-word law preservation. The finite termination is
machine-checked by the well-founded `stabilizeStep` construction.

Evidence:
- layered `formal/palg01-layered@e28c9dbb4882b936889a9aedf5ec42796eed7c86`, CI `34776635531` success;
- quotient `formal/palg01-quotient-law@4f5390e4eac897bae9930ebf58149971d040b851`, CI `34774150913` success;
- clean integration `formal/palg01-main-integration-v1@cd0a36f2663adb1ac17fc30776d6a48e3e8dbb52`;
- PR #66 CI `34777304473`: success;
- proof main `9c638eee8448059221232fa764a2f3ebf00d46bd`;
- proof post-main CI `34777649215`: success;
- source semantic audit complete;
- prohibited-proof audit clean.

The proof is scoped to the specified finite Markov state domain. It does not
claim unconditional full-history FFIPS equivalence, does not add §28.4
constraint indicators and does not use floating-tolerance clustering.

## Recovery correction — P-BRG-02

The authoritative 71/106 ledger already counts **P-BRG-02**. A redundant feature
branch (`formal/pbrg02-behavioral-equivalence`) was opened during CI waiting
before that old counted list was rechecked. It is not a new proof lane, must not
be merged, and must not change coverage. The protocol rule
`do_not_reopen_counted_green_pids_without_source_mismatch_or_regression` remains
in force.

## Current source audit — P-REF-01

P-REF-01 requires the augmented-state path law under **arbitrary causal policy**
to be uniquely determined by the initial law and measurable controlled kernel.
Pinned Mathlib contains the Ionescu--Tulcea `traj` and `trajMeasure` machinery,
including projective-limit uniqueness and conditional-distribution interfaces.
The eventual proof must preserve arbitrary history-dependent randomized
policies; a Markov-only or deterministic-policy surrogate is not source-equivalent.
Deterministic structural modification is a special case/corollary.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron--Frobenius asymptotics / martingale foundations.
- P-REF-03: arbitrary signal-space conditional expectation.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron--Frobenius asymptotic package; do not count an assumed-convergence
surrogate.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent audit/proof lane.
