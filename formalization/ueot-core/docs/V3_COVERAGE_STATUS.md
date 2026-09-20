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
audit, safe main integration, and the separate ledger lifecycle. Feature-green,
clean-integration-green, proof-PR-green, or proof-main-green alone never changes
the FULL-GREEN count.

## Current source-level coverage

| status | count |
|---|---:|
| **proved, staged by this ledger checkpoint** | **91** |
| **partial** | **0** |
| **pending / not yet counted** | **15** |
| **total** | **106** |

This branch stages **91/106** after P-DDH-03 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**91/106 is not called FULL-GREEN until this ledger checkpoint itself passes
branch CI, PR CI, lands on `main`, and the resulting-main CI succeeds.**

`pending` means only “not yet counted proved”; it does not mean no relevant
mathematics or Lean code exists.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-06, P-STAT-07, P-STAT-08, P-STAT-09
- **Invariant / identifiability:** P-INV-01, P-INV-02, P-INV-03, P-INV-04, P-INV-05
- **Quotient:** P-QUO-01, P-QUO-02, P-QUO-03, P-QUO-04, P-QUO-05
- **Control:** P-CTL-01
- **Refinement / agency:** P-REF-01, P-REF-02, P-REF-03, P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-01, P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02, P-REC-03, P-REC-04
- **QSD:** P-QSD-02, P-QSD-03
- **Persistence:** P-PER-01, P-PER-03, P-PER-04
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-DDH-03, P-DDH-04, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02

Count check: `90 + P-DDH-03 = 91`.

## Newly staged promotion — P-DDH-03

Frozen Core 3 §23.3 states that on a finite state space with strictly positive
baseline law `p0`, whenever a finite exponential-family parameter `theta`
realizes a prescribed moment target `m`, the corresponding exponential tilt
uniquely minimizes `KL(· || p0)` over every probability law with the same
moment. Boundary targets not represented by a finite parameter are deliberately
outside the claim.

The formalization preserves that contract literally:

1. `Γ` is finite and `p0` is strictly positive on every state;
2. the feature map `F : Γ → Fin k → ℝ` and finite parameter
   `theta : Fin k → ℝ` are arbitrary, including `k = 0`;
3. the source-facing premise only assumes that the displayed tilt realizes
   the target moment `m`;
4. competitors are quantified directly as arbitrary probability measures with
   the same coordinate moments;
5. KL minimality and equality iff exact optimizer-law equality are proved.

No full-rank, feature-independence, strict-convexity, positive-definite
covariance, unique-parameter, or interior assumption is added. Redundant or
constant features and singular covariance remain allowed, and there is no
logical dependency on P-DDH-02.

Canonical theorem surface:
- `UEOT.V3.ExponentialFamilyIProjection.p_ddh_03`.

Supporting module:
- `UEOT/V3/ExponentialFamilyIProjection.lean`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commit `360f5b941d57a5d0b2edf73924c217034dfd0bcd`;
- feature tree `1c0278bb9b21501ebb30733ed77f2cb48f3228a0`;
- feature root CI `35513672240`: success;
- full local `lake build UEOT`: success (`8983` jobs);
- independent source/proof audits: PASS (two final reviewers);
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...ExponentialFamilyIProjection.p_ddh_03`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pddh03-main-integration@4bce0870076e740f21e14411b8741493c4d61e84` from `main@22a0b0d68201a18d574c0d841679f511a86994b9`;
- feature and clean-integration tree hashes identical: `1c0278bb9b21501ebb30733ed77f2cb48f3228a0`;
- clean integration root CI `35514069336`: success;
- proof PR #113 exact-head root CI `35514474988`: success;
- proof main commit `6e2a179d9fad8293b02b0f47a971f4083eabbeb3`;
- proof resulting-main root CI `35514827747`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 90/106

P-DDH-04 and all earlier counted P-IDs form the authoritative 90/106 baseline.
Its ledger landed at `main@22a0b0d68201a18d574c0d841679f511a86994b9`
with ledger resulting-main CI `35511293247` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. Current source/API audits place
the leading uncounted fronts at:

- P-DDH-02: Class C, M / upper-M; finite log-partition gradient and
  Hessian/covariance. Exact-main probes compile the gradient and raw Hessian;
  the covariance wrapper and second-derivative bookkeeping remain the main
  local bridge;
- P-GOA-04: Class C, L; finite self-adjoint spectral infrastructure exists, but
  source-strength gap/Rayleigh/eigenvector/TV perturbation bridges remain;
- P-DDH-05: Class D, L after deeper audit; pinned Mathlib has singular values
  but no packaged operator-norm singular-value Lipschitz/Weyl theorem;
- P-GOA-03: Class D, L-XL; finite transient/recurrent decomposition,
  absorption weights, and periodic-safe full Cesaro-mixture machinery remain.

P-CORE-01 remains hard-blocked by the recurrent-structure branch of P-GOA-03.
The next proof lane must be selected dynamically only after this 91/106 ledger
becomes FULL-GREEN.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
