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
| **proved, staged by this ledger checkpoint** | **99** |
| **partial** | **0** |
| **pending / not yet counted** | **7** |
| **total** | **106** |

This branch stages **99/106** after P-PER-02 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**99/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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

Count check: `98 + P-PER-02 = 99`.

## Newly staged promotion — P-PER-02

Frozen Core 3 §8.4 takes a continuous-time Feller Markov semigroup `P_t` on a
Polish state space, with `P_t : C_b -> C_b`, and the literal occupation-average
law

`bar μ_T = (1/T) ∫_0^T μ₀ P_t dt`.

If the family for `T >= 1` is tight, every diverging time sequence has a
weakly convergent subsequence; every such weak limit is invariant under every
`P_s`. If every time marginal `μ₀P_t` is supported on a closed set `V`, the
weak limit also has mass one on `V`. The source explicitly does **not** claim
sample-path empirical-frequency convergence without additional ergodicity.

The formalization preserves that contract:

1. `FellerOccupationSystem` fixes the same Markov semigroup and initial
   probability law, with marginals defined canonically as `μ₀ P_t`;
2. the Feller action is represented on `BoundedContinuousFunction X ℝ`, and
   the occupation object exposes the literal time-average identity through its
   bounded-continuous expectation face plus the measurable-event face needed for
   closed-support retention;
3. minimal scalar interval-integrability is explicit so the time-shift
   decomposition can be proved without smuggling in invariance;
4. Prokhorov compactness of the tight occupation family yields a subsequence for
   every `T_n -> ∞`;
5. the source estimate
   `|(bar μ_T P_s - bar μ_T) f| <= 2 s ||f||∞ / T`
   is proved and passed to weak limits using the Feller action, yielding
   invariance for every weak limit, not only the selected one; and
6. closed support is first derived for every occupation average from the
   marginal support hypothesis, then passed to the weak limit with the closed-set
   Portmanteau inequality.

Canonical theorem surface:
- `UEOT.V3.PersistenceOccupation.FellerOccupationSystem.p_per_02`.

Supporting module:
- `UEOT/V3/PersistenceOccupation.lean`.

Promotion evidence:
- frozen §8.4 source contract independently audited against the final theorem:
  GREEN;
- source-facing feature commit
  `2e12c0dbad89f8cddf8f2d195353580a5559c190`;
- feature tree `fd32905323e09e14cba3b3950322a0e2dc5b47f7`;
- feature root CI `35600355442`: success;
- focused module, root import, and full local `lake build UEOT`: success
  (`8991` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pper02-main-integration@959586d1161f27a7a5bbec88b0d1672cac39bc90`
  from `main@4d2016267c246400ce0a6e025f9330eae820eef8`;
- feature and clean-integration tree hashes identical:
  `fd32905323e09e14cba3b3950322a0e2dc5b47f7`;
- clean integration focused/root/full local checks: success (`8991` jobs);
- clean integration root CI `35601197925`: success;
- proof PR #129 exact-head root CI `35601980474`: success;
- proof main commit `1aa9d4c0dd745a2909903c8d1083676b0ec11751`;
- proof resulting-main root CI `35602757494`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 98/106

P-EVO-03 and all earlier counted P-IDs form the authoritative 98/106 baseline.
Its ledger landed at `main@4d2016267c246400ce0a6e025f9330eae820eef8`
with ledger resulting-main CI `35582525823` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. P-PER-02 is proof-complete on the current proof main but is not
counted FULL-GREEN until this independent ledger lifecycle completes.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. After a successful 99/106 ledger
lifecycle, the exact remaining seven P-IDs are:

- P-QSD-01
- P-QSD-04
- P-CTL-02
- P-CTL-03
- P-KL-04
- P-KL-05
- P-ALI-01

The next theorem lane must be selected dynamically only after the exact 99/106
FULL-GREEN `main` exists and the source/dependency/branch preflight is repeated.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
