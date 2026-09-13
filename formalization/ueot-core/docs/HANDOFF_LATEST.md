# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot on `main` and is updated at
> meaningful lifecycle transitions.

## Current lifecycle snapshot

- authoritative full-green baseline before this ledger checkpoint: **71/106**;
- this branch stages **72/106** after P-ALG-01 completed all proof-side and
  post-main gates;
- remaining not-yet-counted P-IDs after staging: **34**;
- full-green 71 baseline: `5218e615d852c1ffee72107f35435ee378709166`;
- P-ALG-01 proof main: `9c638eee8448059221232fa764a2f3ebf00d46bd`;
- newest staged promotion: **P-ALG-01**;
- P-ALG-01 layered CI `34776635531`: success;
- P-ALG-01 quotient CI `34774150913`: success;
- P-ALG-01 clean-integration PR #66 CI `34777304473`: success;
- P-ALG-01 post-main CI `34777649215`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean.

**Do not call 72/106 full-green until this ledger/recovery branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.**

## P-ALG-01 — completed proof contract

Frozen §28.5 is implemented literally:

- finite state set and common finite action set;
- known exact transition matrices, reward vector and output label;
- initial partition = equal output label + equal complete action-reward vector;
- each refinement retains the current block and splits by transition mass to
  every current block under every action;
- finite termination via well-founded finite relation-pair descent;
- terminal controlled stability/lumpability;
- terminal partition is the coarsest stable refinement of the initial one;
- quotient preserves output, reward, every action's one-step law and
  normalization;
- all corresponding finite-horizon output-word laws are preserved.

Canonical theorem:
- `UEOT.V3.PAlg01.p_alg_01`.

Scope guards:
- specified finite Markov state domain only;
- no unconditional identification with full-history FFIPS;
- no §28.4 constraint-data injection;
- no floating-tolerance weakening.

Evidence:
- layered `formal/palg01-layered@e28c9dbb4882b936889a9aedf5ec42796eed7c86`, CI `34776635531` success;
- quotient `formal/palg01-quotient-law@4f5390e4eac897bae9930ebf58149971d040b851`, CI `34774150913` success;
- clean integration `formal/palg01-main-integration-v1@cd0a36f2663adb1ac17fc30776d6a48e3e8dbb52`;
- PR #66 CI `34777304473` success;
- proof main `9c638eee8448059221232fa764a2f3ebf00d46bd`;
- proof post-main CI `34777649215` success.

## Previous full-green checkpoint — 71/106

P-API-01 and all earlier counted P-IDs are fully green at the baseline
`main@5218e615d852c1ffee72107f35435ee378709166`, CI `34771573465` success.
Do not reopen counted P-IDs absent a source mismatch or CI regression.

## Active feature lane — P-BRG-02

Frozen §26.4 says: in one fixed environment, if replication is completely a
function of the declared behavioral response `Q`, equal responses imply equal
replication rates. It is an interface-consistency theorem, not a claim that
mutation/material cost/other channels are absent in nature.

Current feature:
- branch `formal/pbrg02-behavioral-equivalence`;
- head `8ddd9ebf847592b9a62546f468c4f25d515a4a88`;
- theorem `UEOT.V3.SelectionBehavioralEquivalence.p_brg_02`;
- feature CI `34777917118`.

Feature green must not change the coverage count. If green, clean-integrate only
from the then-latest full-green main.

## Audited next stochastic lane — P-REF-01

Frozen P-REF-01 requires arbitrary causal-policy augmented-state path-law
existence/uniqueness from initial law and measurable controlled kernel. Pinned
Mathlib contains Ionescu--Tulcea `traj`/`trajMeasure`, so reuse that machinery.
Do not weaken to deterministic or Markov-only policies. Deterministic structural
update is a corollary/special case, not the general theorem.

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

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green never increments coverage;
- no `sorry`, `admit`, `native_decide`, unsourced `axiom`;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes concentration/extinction/maximizer-ratio clauses;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56 when available;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. live main/branches/CI.
