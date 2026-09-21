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
| **proved, staged by this ledger checkpoint** | **96** |
| **partial** | **0** |
| **pending / not yet counted** | **10** |
| **total** | **106** |

This branch stages **96/106** after P-EVO-04 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**96/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Evolution:** P-EVO-01, P-EVO-02, P-EVO-04
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04

Count check: `95 + P-EVO-04 = 96`.

## Newly staged promotion — P-EVO-04

Frozen Core 3 §25.5 considers a finite-type branching population with true
count vector `Z_n`, natural filtration `F_n`, and finite mean offspring
matrix `M`. Its mechanism-level first-moment identity is

`E[Z_{n+1} | F_n] = Z_n M`.

With the positive Perron data from K-PF-01, `R>0`, `r>0`, `Mr=Rr`, the
source defines

`W_n = R^{-n} Z_n r`

and requires `W` to be a nonnegative integrable martingale with
`E W_n = Z_0 r` for finite deterministic initial counts.

The formalization preserves that contract literally:

1. `I` is finite and `W` is exactly `(R^n)⁻¹ * Σ_i Z_n(i) r_i`;
2. the vector conditional-mean premise is kept literal and the scalar
   reproductive-value recursion is derived through a finite continuous-linear
   readout plus `Mr=Rr`;
3. strong adaptedness, integrability and nonnegativity are explicit process
   interfaces corresponding to the source natural-filtration/count setup;
4. `martingale_nat` builds the actual martingale from the derived one-step
   conditional expectation relation;
5. constant expectation is derived from the martingale and the deterministic
   finite initial count vector `z0 : I → ℕ`;
6. only the Perron consequences needed by P-EVO-04 are inputs; no Perron
   existence or asymptotic theorem is falsely claimed here.

No uniform-integrability conclusion, `L¹` convergence, almost-sure limit
identification, nonextinction positivity claim, or other K-MAR-01 overclaim is
added.

Canonical theorem surface:
- `UEOT.V3.EvolutionReproductiveMartingale.p_evo_04`.

Supporting module:
- `UEOT/V3/EvolutionReproductiveMartingale.lean`.

Promotion evidence:
- canonical frozen source hash/source-lock evidence re-audited before commit;
- source-facing feature commit
  `f09c411f41c4386089cab17f6fcdc536314b762c`;
- feature tree `f162b2c9a1f34d55d58185eaaa9dfe0f94b2f540`;
- feature root CI `35539758527`: success;
- full local `lake build UEOT`: success (`8988` jobs);
- independent source-semantic and proof-quality audits: PASS;
- executable audits verified vector-to-scalar conditional-expectation transport,
  exact `R^{-(n+1)} R = R^{-n}` normalization, deterministic initial-value
  expectation, root-import reachability, and absence of forbidden asymptotic
  overclaims;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...EvolutionReproductiveMartingale.p_evo_04`: only
  `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pevo04-main-integration@1c167457bbfa27f7ec3f60861479aba6f75303f5`
  from `main@ee529be7008b38dbe928223ef1beebbd49db0912`;
- feature and clean-integration tree hashes identical:
  `f162b2c9a1f34d55d58185eaaa9dfe0f94b2f540`;
- clean integration root CI `35559166344`: success;
- proof PR #123 exact-head root CI `35560162916`: success;
- proof main commit `ab9c4c220f442eec2b2e14709a3285e6dd01a066`;
- proof resulting-main root CI `35560658256`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 95/106

P-GOA-03 and all earlier counted P-IDs form the authoritative 95/106 baseline.
Its ledger landed at `main@ee529be7008b38dbe928223ef1beebbd49db0912`
with ledger resulting-main CI `35538326271` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. The next lane must be selected
only after an exact 96/106-main source/dependency audit. P-CORE-01 remains a
read-only candidate after the P-GOA-03 recurrent-structure blocker was removed;
P-EVO-03 is still uncounted and requires the full K-PF-01 asymptotic package;
P-PER-02 / P-QSD-01 remain read-only alternatives requiring continuous-time
semigroup / occupation-measure infrastructure.

The next proof lane must be selected dynamically only after this 96/106 ledger
becomes FULL-GREEN.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
