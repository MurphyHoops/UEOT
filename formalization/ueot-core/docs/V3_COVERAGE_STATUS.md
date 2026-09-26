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
| **proved, staged by this ledger checkpoint** | **103** |
| **partial** | **0** |
| **pending / not yet counted** | **3** |
| **total** | **106** |

This branch stages **103/106** after P-KL-04 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**103/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **QSD:** P-QSD-01, P-QSD-02, P-QSD-03
- **Persistence:** P-PER-01, P-PER-02, P-PER-03, P-PER-04
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-DDH-02, P-DDH-03, P-DDH-04, P-DDH-05, P-ALI-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03, P-KL-04
- **Evolution:** P-EVO-01, P-EVO-02, P-EVO-03, P-EVO-04
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04
- **Core assembly:** P-CORE-01

Count check: `102 + P-KL-04 = 103`.

## Newly staged promotion — P-KL-04

Frozen Core 3 §22.4 states the finite continuous-time jump-process
likelihood/compensator KL identity. Under a common initial state and support
inclusion, the controlled path-space KL divergence equals the controlled-path
expectation of the literal clock-time jump-rate integral, with `0 log 0 = 0`.

The formalization preserves that contract:

1. `FiniteJumpGenerator` gives finite-state continuous-time generators with
   nonnegative jump rates, zero self-jump rates, and derived escape rates;
2. `pathLawFrom` is the explicit normalized full finite-jump path law, not a
   fixed-jump-count surrogate;
3. `SupportIncluded Gu G0` is the source support condition;
4. the common-reference likelihood, absolute continuity, Radon--Nikodym
   derivative, and real log-likelihood are derived on the actual path law;
5. Campbell/renewal identities are proved from path densities rather than
   assumed as compensator certificates;
6. signed jump-log and escape-rate terms are recombined with an integrability
   proof; and
7. the holding-time representation is bridged to the literal clock-time
   trajectory integral in the final source-facing theorem.

Canonical theorem surface:
- `UEOT.V3.FiniteCTMCPathKL.p_kl_04`.

Supporting module:
- `UEOT/V3/FiniteCTMCPathKL.lean`;
- finite-jump path-law infrastructure under
  `UEOT/V3/ThirdParty/CrooksJarzynski/`, with Apache-2.0 provenance pinned in
  `UPSTREAM.md`.

Promotion evidence:
- final frozen-source/proof audit: CLEAR, zero blockers;
- source-facing feature commit
  `79bc6873d9b445627f70017ae37c43e498332158`;
- feature tree `79049834494228824abbe6a7de487f790f926edc`;
- feature root CI `36222018778`: success;
- focused module, root import, and full local `lake build UEOT`: success
  (`9008/9008` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pkl04-main-integration@1117010ab9554ab073d47a6f7f16e7fc78ada214`
  from `main@91547a488ba9a1a86abbb4e5ead7ad5aa98b6bde`;
- feature and clean-integration tree hashes identical:
  `79049834494228824abbe6a7de487f790f926edc`;
- clean integration root CI `36222441619`: success;
- proof PR #137 exact-head root CI `36222997612`: success;
- proof main commit `7af0d8970a33063bb31a216bce97235a380571c0`;
- proof resulting-main root CI `36224107001`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 102/106

P-CTL-02 and all earlier counted P-IDs form the authoritative 102/106 baseline.
Its ledger landed at `main@91547a488ba9a1a86abbb4e5ead7ad5aa98b6bde`
with ledger resulting-main CI `36156516104` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. P-KL-04 is proof-complete on the current proof main but is not
counted FULL-GREEN until this independent ledger lifecycle completes.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. After a successful 103/106 ledger
lifecycle, the exact remaining three P-IDs are:

- P-QSD-04
- P-CTL-03
- P-KL-05

The next theorem lane must be selected dynamically only after the exact 103/106
FULL-GREEN `main` exists and the source/dependency/branch preflight is repeated.
## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
