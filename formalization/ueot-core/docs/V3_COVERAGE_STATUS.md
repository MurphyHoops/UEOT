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
| **proved, staged by this ledger checkpoint** | **95** |
| **partial** | **0** |
| **pending / not yet counted** | **11** |
| **total** | **106** |

This branch stages **95/106** after P-GOA-03 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**95/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04

Count check: `94 + P-GOA-03 = 95`.

## Newly staged promotion — P-GOA-03

Frozen Core 3 §21.4 requires perturbation stability for a finite Markov chain
whose transient set and recurrent-class partition are preserved. Writing
`N=(I-Q)⁻¹` and `H=NR`, the source fixes the exact absorption-matrix bound

`‖Hhat-H‖∞ ≤ (‖N‖∞² epsQ + ‖N‖∞ epsR) / (1 - ‖N‖∞ epsQ)`,

under `‖Qhat-Q‖∞ ≤ epsQ`, `‖Rhat-R‖∞ ≤ epsR` and
`‖N‖∞ epsQ < 1`. For the same initial state, the actual Cesaro limits must
then satisfy the source total-variation bound with coefficient `1/2` and the
perturbed recurrent-class weights multiplying the within-class stationary-law
errors.

The formalization preserves that contract literally:

1. baseline and perturbed objects are actual finite row-stochastic kernels on
   one common state type `T ⊕ R` with one literal shared recurrent partition;
2. the stored transient block `Q` and direct class-entry block `R` are tied
   pointwise to the full kernel by explicit audit lemmas;
3. recurrent classes are closed and communicate internally, while positivity
   and the stationary class formula are derived rather than assumed;
4. the class laws are invariant for the actual full kernels and supported
   exactly on their recurrent classes;
5. periodic-safe full Cesaro convergence is proved from P-GOA-01, transient
   invariant-mass elimination, harmonic absorption potentials and class-law
   uniqueness, for the same initial state before and after perturbation;
6. the exact source `B_H` numerator/denominator, the canonical `1/2`
   coefficient, and the perturbed weights `what_j` are retained, including
   the empty-transient-set degeneracy.

No arbitrary-mixture surrogate, aperiodicity assumption, `P^n` convergence
premise, changed recurrent support, primitive stationary-class formula, or
strengthened positivity hypothesis is added.

Canonical theorem surface:
- `UEOT.V3.FiniteRecurrentDecompositionStability.p_goa_03`.

Supporting module:
- `UEOT/V3/FiniteRecurrentDecompositionStability.lean`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commits
  `8cd02864498ff369b59e9e4b1913082558bd2820` and
  `c1ff6baecdaa7c56a8ade42fbffaeeddf42ec909`;
- feature tree `3c956eadc54fd67a0784af9d46d21ecb88acd764`;
- final feature root CI `35535448015`: success;
- full local `lake build UEOT`: success (`8987` jobs);
- independent source-semantic and proof-quality audits: PASS;
- executable audits verified the exact row-sum norm/resolvent algebra, actual
  kernel Q/R links, communication-based class-law uniqueness, same-initial-state
  Cesaro convergence, the empty-`T` branch, and exact TV orientation;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...FiniteRecurrentDecompositionStability.p_goa_03`: only
  `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pgoa03-main-integration@4d518420cd93e4130a1cd59ceccf888dc9638b6c`
  from `main@cf8aaa8b91b3096cd05d60ad148ada14cc773924`;
- feature and clean-integration tree hashes identical:
  `3c956eadc54fd67a0784af9d46d21ecb88acd764`;
- clean integration root CI `35536081037`: success;
- proof PR #121 exact-head root CI `35536497250`: success;
- proof main commit `6f9173ee290e01838e4746faba6429928399b98c`;
- proof resulting-main root CI `35536908530`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 94/106

P-DDH-05 and all earlier counted P-IDs form the authoritative 94/106 baseline.
Its ledger landed at `main@cf8aaa8b91b3096cd05d60ad148ada14cc773924`
with ledger resulting-main CI `35530223703` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. P-GOA-03 has now discharged the
recurrent-structure blocker that previously prevented a source-faithful
P-CORE-01 attempt. P-CORE-01 therefore returns to the read-only frontier and
must be re-audited against exact 95/106 `main` before any proof branch opens.
P-PER-02 / P-QSD-01 remain read-only alternatives requiring new
continuous-time semigroup / occupation-measure infrastructure.

The next proof lane must be selected dynamically only after this 95/106 ledger
becomes FULL-GREEN.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
