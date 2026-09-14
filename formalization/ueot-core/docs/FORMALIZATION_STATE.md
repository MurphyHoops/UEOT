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
| integrated proved, staged by this checkpoint | **76** |
| active proof / feature-green uncounted | **0** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **30** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **75/106** at
`main@b4c8cd81c62b2e175998ebc4e855901e4b46f125`. P-BRG-01 has completed all
source, feature, clean-integration, PR and proof-main gates, including resulting
main CI `34818138195` success at
`main@667471f1627ef762ebb116d082f2ed588132fa67`. This ledger branch stages
**76/106**. Do not call 76/106 full-green until this ledger branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.

## Newly staged proof — P-BRG-01

Frozen §26.3 is implemented at its declared finite fixed-positive-fitness,
no-mutation replicator scope:

1. exact recurrence and explicit closed form;
2. recurrence + declared initial condition uniquely imply that closed form;
3. initially absent types stay absent;
4. `R_*` is attained on the initially positive support;
5. each supported strictly suboptimal type has an explicit geometric envelope
   with factor `(R_i/R_*)^n`;
6. total supported suboptimal mass is bounded by a finite sum of those geometric
   terms and tends to zero;
7. equal-fitness support maximizers preserve their initial relative proportions.

Canonical theorem surface:
- `UEOT.V3.FixedFitnessRecurrenceUniqueness.p_brg_01_closedForm_of_recurrence`;
- `UEOT.V3.FixedFitnessConcentration.p_brg_01`.

Promotion evidence:
- feature branch `formal/pbrg01-fixed-fitness-v1`;
- feature head `b3f47b89ad901fb11f322d7f386d5a86ba06e708`;
- feature CI `34815094214`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean;
- clean integration branch `formal/pbrg01-main-integration-v1`;
- clean integration head `a40b18ddc99617b25d873b376edf2aab3b096061`;
- clean integration CI `34817101777`: success;
- PR #75 PR-triggered CI `34817631959`: success;
- proof main `667471f1627ef762ebb116d082f2ed588132fa67`;
- proof resulting-main CI `34818138195`: success.

## Counted-source reconciliation — P-REF-04 / P-REF-05

P-REF-04 and P-REF-05 already belong to the counted baseline. Audit/interface
wrapper branches do not open new coverage slots:

- `formal/pref04-source-wrapper-v1@e63e74bfcd72273204bcd5608506d8c50ac40416`, CI `34812442268` success;
- `formal/pref05-source-wrapper-v1@756e0862f36bc272a727b81ba11e3d6aa7019d9b`, CI `34815023569` success.

Existing counted infrastructure proves the frozen content through
`UEOT.V3.Decision.goal_regret` and `UEOT.V3.Agency.feasibleValue_mono` /
`feasibleValueReal_mono`. No substantive source mismatch was found; do not
reopen or double-count them.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; do not count an assumed-convergence
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
