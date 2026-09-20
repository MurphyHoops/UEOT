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
| **proved, staged by this ledger checkpoint** | **94** |
| **partial** | **0** |
| **pending / not yet counted** | **12** |
| **total** | **106** |

This branch stages **94/106** after P-DDH-05 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**94/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Dual-drive / alignment:** P-DDH-01, P-DDH-02, P-DDH-03, P-DDH-04, P-DDH-05, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-04

Count check: `93 + P-DDH-05 = 94`.

## Newly staged promotion — P-DDH-05

Frozen Core 3 §23.5 requires singular-value stability for a finite rectangular
sensitivity matrix under a genuine Euclidean operator 2-norm perturbation. If
`‖Shat - S‖₂ ≤ eta`, then every corresponding singular value must satisfy
`|sigma_i(Shat) - sigma_i(S)| ≤ eta`. If the source threshold window
`sigma_3(S) + eta < tau < sigma_2(S) - eta` holds, exactly two singular values
of `Shat` must exceed `tau`.

The formalization preserves that contract literally:

1. `S` and `Shat` are arbitrary finite rectangular real matrices;
2. the matrix norm is Mathlib `Matrix.Norms.L2Operator`, definitionally the
   Euclidean continuous-linear-map operator norm of `Matrix.toEuclideanLin`;
3. singular-value Lipschitz stability is proved for every `i : ℕ`, including
   Mathlib's zero-padded indices beyond the domain finrank;
4. source one-based `sigma_2` / `sigma_3` are translated exactly to Mathlib
   zero-based indices `1` / `2`;
5. the threshold conclusion is exactly
   `tau < sigma_i(Shat) ↔ i < 2`, hence precisely two estimated singular values
   exceed `tau`;
6. the indexed perturbation theorem is derived from explicit top/tail right
   singular subspaces and a dimension-forced nonzero intersection.

No Frobenius-norm substitution, rank-two premise, P-DDH-04 dependency,
singular-vector-closeness assumption, dimension strengthening, or assumed
Weyl/min-max theorem is added.

Canonical theorem surface:
- `UEOT.V3.SingularValueEffectiveDimension.p_ddh_05`.

Supporting module:
- `UEOT/V3/SingularValueEffectiveDimension.lean`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commit `16a954ace676f342872ac5b4e7dd3df993d9c34c`;
- feature tree `0a5cfca620f6290eca0eac8043594725db0d646a`;
- feature root CI `35527630169`: success;
- full local `lake build UEOT`: success (`8986` jobs);
- independent source-semantic and proof-quality audits: PASS;
- executable audit verified the genuine L2 operator norm bridge, all-index
  singular-value Lipschitz theorem, zero-padding, and exact threshold indexing;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...SingularValueEffectiveDimension.p_ddh_05`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pddh05-main-integration@3bbb902bb6c7971026e2aa40a139cfc0eb8eace6` from `main@a96e49711b46feecbd8cff541408fc28e9926832`;
- feature and clean-integration tree hashes identical: `0a5cfca620f6290eca0eac8043594725db0d646a`;
- clean integration root CI `35528080435`: success;
- proof PR #119 exact-head root CI `35528531712`: success;
- proof main commit `34dfa9cdfe48ed05370bbc32f755b41a8f8c0510`;
- proof resulting-main root CI `35528930852`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 93/106

P-GOA-04 and all earlier counted P-IDs form the authoritative 93/106 baseline.
Its ledger landed at `main@a96e49711b46feecbd8cff541408fc28e9926832`
with ledger resulting-main CI `35526426358` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. Current source/API audits place
the leading uncounted fronts at:

- P-GOA-03: Class D, L-XL; finite transient/recurrent decomposition,
  absorption weights, and periodic-safe full Cesaro-mixture machinery remain;
- P-PER-02 / P-QSD-01: next read-only alternatives, both still requiring new
  continuous-time semigroup / occupation-measure infrastructure.

P-CORE-01 remains hard-blocked by the recurrent-structure branch of P-GOA-03.
The next proof lane must be selected dynamically only after this 94/106 ledger
becomes FULL-GREEN.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
