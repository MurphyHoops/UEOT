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
| **proved, staged by this ledger checkpoint** | **97** |
| **partial** | **0** |
| **pending / not yet counted** | **9** |
| **total** | **106** |

This branch stages **97/106** after P-CORE-01 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**97/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Core assembly:** P-CORE-01

Count check: `96 + P-CORE-01 = 97`.

## Newly staged promotion — P-CORE-01

Frozen Core 3 §31.1 is the finite operational assembly theorem. It requires one
common high-probability event on which the already-proved response, quotient,
control, path, long-run, history-transport and integrity components are assembled
without changing the underlying source objects or double-counting shared event
failures.

The formalization preserves that source contract:

1. `FixedSourceApproximation` fixes the candidate map, true micro model and
   approximation tolerances across samples; only the estimated quotient varies;
2. response recovery, exact carrier family and blocker recovery use the same
   certified sample event;
3. quotient value error `D`, policy regret `2D`, and the action-gap certificate
   are derived from the source approximation data rather than assumed;
4. control and finite-path conclusions use the same lifted greedy policy;
5. both conditional long-run ports are present: mixing GOA and recurrent GOA;
   the recurrent port carries explicit `HEq` source-identity guards and kernel
   equality to the policy-induced matrices;
6. P-ID history transport appears on the same pointwise certificate and keeps the
   adjacent-error accumulation contract;
7. integrity robustness uses the source-direction margin hypothesis; and
8. the finite family of failure keys is combined through one common event with a
   union bound, so reused events are not counted twice.

Canonical theorem surface:
- `UEOT.V3.CoreOperationalAssembly.p_core_01`.

Supporting module:
- `UEOT/V3/CoreOperationalAssembly.lean`.

Promotion evidence:
- canonical frozen §31.1 source contract independently re-audited twice: GREEN;
- source-facing feature commit
  `bad381814a902047ece0f813d6b3385c71bc9db1`;
- feature tree `85ba74aaa1fbabb36a1b766ad8cd32f34e70f185`;
- feature root CI `35569184015`: success;
- full local `lake build UEOT`: success (`8989` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- audited `#print axioms` outputs only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pcore01-main-integration@a34423f7abd99a172605eb6a321e39c5c45921fb`
  from `main@5a18daa6a14edd0dc609fd0db72661e422991b17`;
- feature and clean-integration tree hashes identical:
  `85ba74aaa1fbabb36a1b766ad8cd32f34e70f185`;
- clean integration full local `lake build UEOT`: success (`8989` jobs);
- clean integration root CI `35569862884`: success;
- proof PR #125 exact-head root CI `35570425596`: success;
- proof main commit `1a6d7d90d06988e0e0bda7a29061df955dfd0096`;
- proof resulting-main root CI `35570915485`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 96/106

P-EVO-04 and all earlier counted P-IDs form the authoritative 96/106 baseline.
Its ledger landed at `main@5a18daa6a14edd0dc609fd0db72661e422991b17`
with ledger resulting-main CI `35562298378` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. P-CORE-01 is proof-complete on the current proof main but is not
counted FULL-GREEN until this independent ledger lifecycle completes.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. After a successful 97/106 ledger
lifecycle, the exact remaining nine P-IDs are:

- P-PER-02
- P-QSD-01
- P-QSD-04
- P-CTL-02
- P-CTL-03
- P-KL-04
- P-KL-05
- P-ALI-01
- P-EVO-03

The next theorem lane must be selected dynamically only after the exact 97/106
FULL-GREEN `main` exists and the source/dependency/branch preflight is repeated.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
