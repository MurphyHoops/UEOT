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
| **proved, staged by this ledger checkpoint** | **105** |
| **partial** | **0** |
| **pending / not yet counted** | **1** |
| **total** | **106** |

This branch stages **105/106** after P-QSD-04 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**105/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Control:** P-CTL-01, P-CTL-02
- **Refinement / agency:** P-REF-01, P-REF-02, P-REF-03, P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-01, P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02, P-REC-03, P-REC-04
- **QSD:** P-QSD-01, P-QSD-02, P-QSD-03, P-QSD-04
- **Persistence:** P-PER-01, P-PER-02, P-PER-03, P-PER-04
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-DDH-02, P-DDH-03, P-DDH-04, P-DDH-05, P-ALI-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03, P-KL-04, P-KL-05
- **Evolution:** P-EVO-01, P-EVO-02, P-EVO-03, P-EVO-04
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04
- **Core assembly:** P-CORE-01

Count check: `104 + P-QSD-04 = 105`.

## Newly staged promotion — P-QSD-04

Frozen Core 3 §10.4 requires the reversible killed-diffusion spectral QSD
statement: a self-adjoint compact-resolvent killed generator with positive
principal mode and strict spectral gap yields exponential convergence of the
conditioned law in total variation at the gap rate, together with an eventual
survival lower bound at the principal decay rate.

The formalization preserves that contract:

1. `SpectralData` contains a genuine continuous-time killed/subprobability
   kernel semigroup, not a finite-state surrogate;
2. its evolved law is explicitly identified with the spectral density relative
   to the finite reference measure `m`;
3. a concrete compact symmetric resolvent witness acts on `L²(m)`, with the
   principal resolvent mode and an orthogonal spectral bound tied to
   `lambda1` and `lambda2`;
4. the standard self-adjoint compact-resolvent spectral expansion and L²
   remainder estimate are the Appendix-C-licensed spectral input, while the
   source TV/survival conclusions are not assumed;
5. Lean proves the finite-measure Cauchy--Schwarz L²→L¹ step, principal-mass
   lower bound, normalization estimate, and exponential TV bound;
6. redundant positivity certificates are derived from the positive principal
   mode / spectral remainder rather than inserted as final assumptions; and
7. the source-facing survival conclusion is stated on the actual killed
   semigroup survival mass.

Canonical theorem surface:
- `UEOT.V3.ReversibleKilledSpectralQSD.SpectralData.p_qsd_04`.

Supporting module:
- `UEOT/V3/ReversibleKilledSpectralQSD.lean`.

Promotion evidence:
- frozen §10.4 source contract rechecked against the canonical source;
- final feature head `ee0d942c8c6e4913afd6fc803b8ecd0a1f26491c`;
- feature root CI `36242678627`: success;
- clean integration head `7b37181280718b7ca73a3ba7cf46f39e75a13359`
  from `main@9a8a6261ca18c45cd2773c4cb1026bc450b32428`;
- feature/integration tree identity:
  `0c88c8fd5d29281bdaf9896935d697127dbfa1da`;
- clean integration root CI `36242788142`: success;
- proof PR #141 exact-head root CI `36243218374`: success;
- proof main `5c88124a5c2f8ef0fd53d685c82f553917a1c6f7`;
- proof resulting-main root CI `36243627501`: success;
- final local `lake build UEOT`: success (`9010/9010` jobs);
- `git diff --check`: clean;
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms` for `p_qsd_04`: only `propext`,
  `Classical.choice`, `Quot.sound`.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 104/106

P-KL-05 and all earlier counted P-IDs form the authoritative 104/106 baseline.
Its ledger landed at `main@9a8a6261ca18c45cd2773c4cb1026bc450b32428`
with ledger resulting-main CI `36234355278` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. P-QSD-04 is proof-complete on the current proof main but is not
counted FULL-GREEN until this independent ledger lifecycle completes.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. After a successful 105/106
ledger lifecycle, the exact remaining P-ID is:

- P-CTL-03

The final theorem lane must be opened only after the exact 105/106 FULL-GREEN
`main` exists and the source/dependency/branch preflight is repeated.
## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
