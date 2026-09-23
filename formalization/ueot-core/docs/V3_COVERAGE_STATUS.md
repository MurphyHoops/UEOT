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
| **proved, staged by this ledger checkpoint** | **100** |
| **partial** | **0** |
| **pending / not yet counted** | **6** |
| **total** | **106** |

This branch stages **100/106** after P-QSD-01 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**100/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **QSD:** P-QSD-01, P-QSD-02, P-QSD-03
- **Persistence:** P-PER-01, P-PER-02, P-PER-03, P-PER-04
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-DDH-02, P-DDH-03, P-DDH-04, P-DDH-05, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02, P-EVO-03, P-EVO-04
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04
- **Core assembly:** P-CORE-01

Count check: `99 + P-QSD-01 = 100`.

## Newly staged promotion — P-QSD-01

Frozen Core 3 §10.1 starts from a killed subprobability semigroup `P_t^V` and
the literal conditioned marginals
`μ_t^c = μ P_t^V / (μ P_t^V 1)`. If these conditioned laws converge in total
variation to `q`, if `q P_s^V 1 > 0` for every finite nonzero `s`, and the
survival function is right-continuous at zero, then `q` is quasi-stationary and
there is `λ >= 0` such that
`q P_s^V = exp(-λ s) q`. The source allows the degenerate no-absorption case
`λ = 0`.

The formalization preserves that contract:

1. `KilledSemigroup` carries the killed subprobability semigroup and a single
   initial probability law; `initialSurvivalPos` is only the well-definedness
   condition for the literal conditioned family;
2. the conditioned-shift identity is derived from the kernel semigroup and
   normalization, rather than assumed as a hypothesis;
3. total-variation convergence is pushed through each fixed subprobability
   kernel to derive the QSD/eigenmeasure identity
   `q P_s = (q P_s 1) q`;
4. survival multiplicativity is then derived from that identity;
5. positivity away from zero plus `P_0 = id` gives positivity at zero, and
   `ContinuousAt` at zero on `NNReal = [0,∞)` is exactly the required
   right-continuity interface; and
6. the positive multiplicative survival function is logarithmically linearized
   to obtain the exponential law with a nonnegative rate, without assuming the
   desired rate/eigenmeasure conclusion.

Canonical theorem surface:
- `UEOT.V3.QSDTVLimit.p_qsd_01`.

Supporting module:
- `UEOT/V3/QSDTVLimit.lean`.

Promotion evidence:
- frozen §10.1 source contract independently audited against the final theorem:
  GREEN;
- source-facing feature commit
  `b9625635c10cc114e854bfc1e1d7b2af277a47d8`;
- feature tree `f269847d42b34f5c7cd30236e011aa841a0aafb7`;
- feature root CI `35624526524`: success;
- focused module, root import, and full local `lake build UEOT`: success
  (`8992` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pqsd01-main-integration@10a37206f049684c292c53d7826087f05580d489`
  from `main@9b00f80e091a80cc335cd592e527d0e98253f5f7`;
- feature and clean-integration tree hashes identical:
  `f269847d42b34f5c7cd30236e011aa841a0aafb7`;
- clean integration focused/root/full local checks: success (`8992` jobs);
- clean integration root CI `35628806058`: success;
- proof PR #131 exact-head root CI `35629472501`, attempt 2: success
  (attempt 1 failed only in pinned-Lean download with a runner SSL reset);
- proof main commit `ac17ea1a0859b364542fa4996de1e7458b94b53a`;
- proof resulting-main root CI `35900895439`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 99/106

P-PER-02 and all earlier counted P-IDs form the authoritative 99/106 baseline.
Its ledger landed at `main@9b00f80e091a80cc335cd592e527d0e98253f5f7`
with ledger resulting-main CI `35605364675` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. P-QSD-01 is proof-complete on the current proof main but is not
counted FULL-GREEN until this independent ledger lifecycle completes.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. After a successful 100/106 ledger
lifecycle, the exact remaining six P-IDs are:

- P-QSD-04
- P-CTL-02
- P-CTL-03
- P-KL-04
- P-KL-05
- P-ALI-01

The next theorem lane must be selected dynamically only after the exact 100/106
FULL-GREEN `main` exists and the source/dependency/branch preflight is repeated.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
