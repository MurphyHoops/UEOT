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
| **proved, staged by this ledger checkpoint** | **90** |
| **partial** | **0** |
| **pending / not yet counted** | **16** |
| **total** | **106** |

This branch stages **90/106** after P-DDH-04 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**90/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Dual-drive / alignment:** P-DDH-01, P-DDH-04, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02

Count check: `89 + P-DDH-04 = 90`.

## Newly staged promotion — P-DDH-04

Frozen Core 3 §23.4 assumes one common differentiable two-dimensional
bottleneck `z(B) ∈ R^2`, shared across every compared environment, with
`m_e = g_e ∘ z` in the fixed budget coordinates.  At one and the same budget
point `B`, the source conclusion is that the vertically stacked environment
response Jacobian has rank at most two.

The formalization preserves that contract literally:

1. all compared scalar response rows share the same differentiable
   `z : Budget k → Latent`, where `Latent = Fin 2 → ℝ`;
2. every response factors through that same map, `m r x = g r (z x)`;
3. all derivatives are evaluated at the same budget point `B`;
4. the stacked derivative factors through one shared `Dz(B)` by the Fréchet
   chain rule;
5. matrix rank is bounded by the two-column outer derivative factor.

It does not replace the common bottleneck by separate per-environment rank-two
assumptions, does not stack different budget points, and does not assume or
claim exact rank two, injectivity/full rank of `Dz`, a converse, or nonempty
response families.

Canonical theorem surface:
- `UEOT.V3.CommonBottleneckRank.p_ddh_04`.

Supporting module:
- `UEOT/V3/CommonBottleneckRank.lean`.

Promotion evidence:
- canonical frozen source hash independently reverified before implementation;
- source-facing feature commit `91a5043899a843fe7a43c43e9aa827700636e461`;
- feature tree `ac5bd0c2f12c89a333c5d56324a1706a0554401a`;
- feature root CI `35364508901`: success;
- full local `lake build UEOT`: success (`8982` jobs);
- independent source-semantic audit: PASS against frozen §23.4;
- independent final Lean audit: PASS;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...CommonBottleneckRank.p_ddh_04`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pddh04-main-integration@4f9df47cad85da878a528c08f05d64c8665b656d` from `main@aa9c2473849a960a3c25ad35410da68a79c9e164`;
- feature and clean-integration tree hashes identical: `ac5bd0c2f12c89a333c5d56324a1706a0554401a`;
- clean integration root CI `35388778412`: success;
- proof PR #111 exact-head root CI `35389378056`: success;
- proof main commit `a0a92b015e4a95b97baa569e44ddbda41b1f3b0b`;
- proof resulting-main root CI `35390116056`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 89/106

P-GOA-02 and all earlier counted P-IDs form the authoritative 89/106 baseline.
Its ledger landed at `main@aa9c2473849a960a3c25ad35410da68a79c9e164`
with ledger resulting-main CI `35352566122` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. Current source/API audits place
the leading uncounted fronts at:

- P-DDH-03: Class C, M; finite exponential-family moment-constrained KL
  minimization.  `Measure.tilted`, log-likelihood-ratio, finite PMF and KL APIs
  are available; no dependency on P-DDH-02 is required;
- P-DDH-02: Class C, M; finite log-partition gradient/Hessian = mean/covariance;
  first-derivative infrastructure is standard, while the Hessian matrix wrapper
  and second derivative bookkeeping remain the main local bridge;
- P-GOA-04: Class C, L; finite self-adjoint spectral infrastructure exists, but
  source-strength gap/Rayleigh/eigenvector/TV perturbation bridges remain;
- P-DDH-05: Class D, L after deeper audit; pinned Mathlib has singular values
  but no packaged operator-norm singular-value Lipschitz/Weyl theorem;
- P-GOA-03: Class D, L-XL; finite transient/recurrent decomposition,
  absorption weights, and periodic-safe full Cesaro-mixture machinery remain.

P-CORE-01 remains hard-blocked by the recurrent-structure branch of P-GOA-03.
The next proof lane must be selected dynamically only after this 90/106 ledger
becomes FULL-GREEN.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
