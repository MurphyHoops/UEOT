# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification.

## Verification contract

- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- canonical source object: project File Library
- exact canonical source bytes in public repo: pending synchronization

A P-ID is counted `proved` only after frozen-source semantic matching, official
import reachability, feature/integration/post-main CI gates, prohibited-proof
audit, safe main integration, and ledger synchronization. Feature-green work
alone never changes this ledger.

## Current source-level coverage

| status | count |
|---|---:|
| **proved, staged by this ledger checkpoint** | **77** |
| **partial** | **0** |
| **pending / not yet counted** | **29** |
| **total** | **106** |

This branch stages **77/106** after P-QSD-03 completed source-semantic, feature,
clean-integration, PR and proof-main gates, including successful resulting-main
CI. **77/106 is not called full-green until this ledger checkpoint itself passes
PR CI, lands on `main`, and the resulting main CI succeeds.**

`pending` means only “not yet counted proved”; it does not mean no relevant
mathematics or Lean code exists.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-06, P-STAT-07, P-STAT-08, P-STAT-09
- **Invariant / identifiability:** P-INV-01, P-INV-02, P-INV-03, P-INV-04, P-INV-05
- **Quotient:** P-QUO-03
- **Refinement / agency:** P-REF-01, P-REF-02, P-REF-03, P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-01, P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02, P-QSD-03
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `76 + P-QSD-03 = 77`.

## Newly staged promotion — P-QSD-03

Frozen Core 3 §10.3 is formalized without swapping it with P-QSD-01 or P-QSD-04.
For one fixed initial law `μ`, the theorem assumes, for `t ≥ t0`,

- conditional-stability error `≤ C exp(-γ t)`;
- survival probability `≥ c exp(-λ t)`;
- `C,c,γ,λ > 0`, `ε > 0`, and `0 < p ≤ c`.

The source-facing result proves that every

` t ∈ [max{t0,0,log(C/ε)/γ}, log(c/p)/λ] `

simultaneously satisfies conditional-stability error `≤ ε` and survival
probability `≥ p`, provided the closed interval is nonempty. Endpoint equality
is retained, so a singleton window is valid. Both estimates use the same
initial law.

Canonical theorem surface:
- `UEOT.V3.QSDDurationWindow.p_qsd_03`;
- helper endpoint characterization `UEOT.V3.QSDDurationWindow.window_nonempty_iff`.

Promotion evidence:
- feature branch: `formal/pqsd03-duration-window-v1`;
- feature head: `11076f31eec199a4e80ba13e00e037c5e62a2de2`;
- feature CI `34831456183`: success;
- source-semantic audit: complete;
- prohibited-proof audit: clean (`sorry=0`, `admit=0`, `native_decide=0`, unsourced `axiom=0`);
- clean integration branch: `formal/pqsd03-main-integration`;
- clean integration head: `8e85e687ea11a8dac89ebe7ebbab8240551d8f99`;
- clean integration CI `34847211649`: success;
- proof PR #79;
- PR-triggered CI `34848043040`: success;
- proof main commit `bab0b0718afaee90e858d71e41340066ba1774d8`;
- proof resulting-main CI `34848676178`: success.

**Status: PROVED / COUNTED pending this ledger/recovery checkpoint's own PR and
resulting-main CI.**

## Previous full-green checkpoint — 76/106

The authoritative full-green baseline before this P-QSD-03 promotion is
`main@b461bdf8b37250fae9fca923ea243e1182f9e5cc`. P-BRG-01 is closed and
counted there. All 76 counted P-IDs at that checkpoint remain closed absent a
substantive frozen-source mismatch or CI regression.

P-REF-04 and P-REF-05 were already members of the earlier counted baseline. The
source-facing wrapper branches audited during that cycle are interface hardening
only and must **not** be double-counted as new P-IDs.

## Grounded pending fronts

The remaining 29 not-yet-counted P-IDs require fresh source-first audits. Known
non-quick fronts include:

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds;
- P-DDH-02/03: finite exponential-family calculus and KL variational duality;
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis;
- P-EVO-03/04: Perron-Frobenius asymptotics / martingale foundations;
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation;
- P-QSD-01/04: source-locked distinct non-A results.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; an assumed-convergence surrogate is not
countable.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers, feature-green branches, source
audits or proof-main commits never count on their own.
