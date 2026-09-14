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
| integrated proved, staged by this checkpoint | **77** |
| active proof / feature-green uncounted | **0** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **29** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **76/106** at
`main@b461bdf8b37250fae9fca923ea243e1182f9e5cc`. P-QSD-03 has completed all
source, feature, clean-integration, PR and proof-main gates, including resulting
main CI `34848676178` success at
`main@bab0b0718afaee90e858d71e41340066ba1774d8`. This ledger branch stages
**77/106**. Do not call 77/106 full-green until this ledger branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.

## Newly staged proof — P-QSD-03

Frozen Core 3 §10.3 is implemented at its declared same-initial-law scope:

1. conditional-stability error is bounded by `C * exp (-γ t)` for `t ≥ t0`;
2. survival probability is bounded below by `c * exp (-λ t)` for the same initial law;
3. positive constants and thresholds satisfy `C,c,γ,λ,ε,p > 0` and `p ≤ c`;
4. the mixing inequality gives the lower time constraint `log(C/ε)/γ`;
5. the survival inequality gives the upper time constraint `log(c/p)/λ`;
6. their intersection with `t ≥ t0` and `t ≥ 0` is the source closed window;
7. endpoint equality is retained, so a singleton window is valid.

Canonical theorem surface:
- `UEOT.V3.QSDDurationWindow.p_qsd_03`;
- `UEOT.V3.QSDDurationWindow.window_nonempty_iff`.

Promotion evidence:
- feature branch `formal/pqsd03-duration-window-v1`;
- feature head `11076f31eec199a4e80ba13e00e037c5e62a2de2`;
- feature CI `34831456183`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean;
- clean integration branch `formal/pqsd03-main-integration`;
- clean integration head `8e85e687ea11a8dac89ebe7ebbab8240551d8f99`;
- clean integration CI `34847211649`: success;
- PR #79 PR-triggered CI `34848043040`: success;
- proof main `bab0b0718afaee90e858d71e41340066ba1774d8`;
- proof resulting-main CI `34848676178`: success.

## Previous full-green checkpoint — 76/106

P-BRG-01 is closed and counted in the 76/106 baseline. P-REF-04 and P-REF-05
were already counted before that cycle; wrapper work must not be double-counted.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/04: source-locked distinct non-A results.

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
