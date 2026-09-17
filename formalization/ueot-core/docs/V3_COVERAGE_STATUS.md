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
audit, safe main integration, and ledger synchronization. Feature-green,
clean-integration-green, proof-PR-green, or proof-main-green alone never changes
the FULL-GREEN count.

## Current source-level coverage

| status | count |
|---|---:|
| **proved, staged by this ledger checkpoint** | **86** |
| **partial** | **0** |
| **pending / not yet counted** | **20** |
| **total** | **106** |

This branch stages **86/106** after P-QUO-04 completed source-semantic, feature,
clean-integration, proof-PR, proof-main and proof resulting-main gates.
**86/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Quotient:** P-QUO-01, P-QUO-02, P-QUO-03, P-QUO-04
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
- **Dual-drive / alignment:** P-DDH-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `85 + P-QUO-04 = 86`.

## Newly staged promotion — P-QUO-04

Frozen Core 3 §20.4 fixes a policy `pi` and bounded reference function `w`,
defines

`b_pi = r^pi + beta P^pi w - w`,

`d_mu^pi = (1-beta) * sum_{t>=0} beta^t mu(P^pi)^t`,

and requires the exact identities

`V^pi - w = (I-beta P^pi)^(-1)b_pi`,

`mu(V^pi-w) = E_{d_mu^pi}[b_pi]/(1-beta)`.

The finite source branch is formalized with stationary randomized policies.
Their induced reward and kernel are defined exactly, the policy kernel is proved
stochastic, and the fixed-policy Bellman value is bridged to the repository's
existing infinite-horizon causal-policy semantics. The linear operator
`I-beta P^pi` is proved to have a genuine two-sided inverse. Its inverse equals
the explicitly summable Neumann series `sum_n beta^n (P^pi)^n`.

The discounted state occupancy is defined by the exact frozen geometric series,
proved nonnegative with total mass one, and satisfies the row fixed point

`d = (1-beta) mu + beta d P^pi`.

The same stationary policy induces state-action occupancy `d(x) pi(a|x)`, with
nonnegativity, exact state marginal and total mass one. The source expectation
identity is then proved exactly; no sup-norm residual bound substitutes for the
frozen equality.

Canonical theorem surface:
- `UEOT.V3.FiniteDiscountedControl.Model.p_quo_04`.

Supporting modules:
- `UEOT/V3/FiniteDiscountedPolicyResolvent.lean`;
- `UEOT/V3/FiniteDiscountedOccupancy.lean`.

Promotion evidence:
- frozen source original `UEOT_Core_Mathematics_v3.0_Complete.md` independently re-read from the project File Library and hash-matched to the canonical SHA-256;
- feature branch `formal/pquo04-resolvent-occupancy-v1`;
- source-facing feature commit `17a7d44d9d43b592f1aa35ecaeb6b8392707a9d3`;
- feature `lake build UEOT`: success (`8978` jobs);
- source-semantic audit: complete against frozen §20.4;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...Model.p_quo_04`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pquo04-main-integration@8e3675e99f0959734d4a20257e90f1ad86a0ad63` from `main@aaea53a70902e138d123ef700a99c372214708d9`;
- feature and clean-integration tree hashes identical: `7ae9843d1d8060cd0c2141ab6e7b664b47888ab2`;
- clean integration root CI `35203214739`: success;
- proof PR #103;
- proof PR root CI `35203814134`: success;
- proof main commit `c5cc58e49ef820fb3e9ed7d3555722578f4c4b9c`;
- proof resulting-main root CI `35205157977`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 85/106

P-QUO-02 and all earlier counted P-IDs form the authoritative 85/106 baseline.
Its ledger landed at `main@aaea53a70902e138d123ef700a99c372214708d9`
with ledger resulting-main CI `35165216681` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Next source-first front after this ledger closes

No further theorem lane is opened by this promotion. Frozen §20.5 (P-QUO-05)
has already been source-audited and depends on the exact state-action occupancy
semantics established by P-QUO-04, but it remains a separate later lifecycle.
Other uncounted fronts include P-CTL-02/03, P-PER-02, P-ALI-01,
P-DDH-02/03/04/05, P-KL-04/05, P-EVO-03/04, P-QSD-01/04 and the remaining
GOA/control propositions. No weaker finite/toy/assumed-conclusion surrogate may
be counted.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron-Frobenius asymptotic package; assumed convergence is not a substitute.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
