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
| **proved, staged by this ledger checkpoint** | **87** |
| **partial** | **0** |
| **pending / not yet counted** | **19** |
| **total** | **106** |

This branch stages **87/106** after P-QUO-05 completed source-semantic, feature,
clean-integration, proof-PR, proof-main and proof resulting-main gates.
**87/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Dual-drive / alignment:** P-DDH-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `86 + P-QUO-05 = 87`.

## Newly staged promotion — P-QUO-05

Frozen Core 3 §20.5 uses local state-action model errors

`delta(x,a) = epsilon_r(x,a) + beta * epsilon_p(x,a) * span(Vbar*)`

and requires the occupancy-weighted quotient-policy regret bound

`J(pi*;mu) - J(hatpi;mu) <=
 (E_{d_mu^{pi*}} delta + E_{d_mu^{hatpi}} delta)/(1-beta)`.

The finite source branch retains the local reward and pushed-forward transition-TV
errors pointwise in `(x,a)` rather than replacing them by the uniform P-QUO-02
radius. It sets `w = Vbar* o f`, proves the actionwise reference residual upper
bound `b(x,a) <= delta(x,a)`, and proves the matching lower bound on every
designated lifted macro-optimal selector action.

P-QUO-04's exact discounted state-action occupancy identity is then applied to
an arbitrary designated true-optimal stationary micro policy `pi*` and to the
lifted macro-optimal policy `hatpi`. Subtracting the two identities yields the
source RHS with the two policies' actual occupancies and exactly one division by
`1-beta`. Tied true or macro optima remain allowed.

Canonical theorem surface:
- `UEOT.V3.FiniteDiscountedControl.LocalApproxControlQuotient.p_quo_05`.

Supporting modules:
- `UEOT/V3/FiniteDiscountedPolicyResolvent.lean`;
- `UEOT/V3/FiniteDiscountedOccupancy.lean`;
- `UEOT/V3/FiniteDiscountedOccupancyRegret.lean`.

Promotion evidence:
- frozen source original `UEOT_Core_Mathematics_v3.0_Complete.md` independently re-read from the project File Library and hash-matched to the canonical SHA-256;
- source-facing feature commit `66472785c54fc5863554455a6a717009679f11f3`;
- feature `lake build UEOT`: success (`8979` jobs);
- independent source-semantic re-audit: PASS against frozen §20.5;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...LocalApproxControlQuotient.p_quo_05`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pquo05-main-integration@3b647e3f078d7ef94377fe2139ecd9dfd910daeb` from `main@208d9758a90f6c28623b3adac82eb26ea030e5dd`;
- feature and clean-integration tree hashes identical: `eacc3f3e56faf3b97ebb16250ee1da7ef6ca2218`;
- clean integration root CI `35219313969`: success;
- proof PR #105;
- proof PR root CI `35332002471`: success;
- proof main commit `7d0f7dae8b6db34994707a3453a4c827a8dfd89e`;
- proof resulting-main root CI `35332494188`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 86/106

P-QUO-04 and all earlier counted P-IDs form the authoritative 86/106 baseline.
Its ledger landed at `main@208d9758a90f6c28623b3adac82eb26ea030e5dd`
with ledger resulting-main CI `35207737414` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Next source-first front after this ledger closes

No further theorem lane is opened by this promotion. The independent dynamic
frontier audit recommends P-GOA-01 next, followed by P-GOA-02. Frozen §21.2
requires only that Cesaro averages for a fixed finite stochastic kernel have a
convergent subsequence and that every subsequential limit is invariant. Full
Cesaro convergence and attractivity are not part of the P-GOA-01 anchor and
must not be substituted for it.

Current main already provides generic finite matrix row action
`UEOT.V3.QSDPerron.rowApply` / `rowApply_mul` and finite probability-row
infrastructure. Pinned Mathlib provides compactness of the finite standard
simplex and `IsCompact.tendsto_subseq`; the missing source bridge is the
stochastic-row preservation, Cesaro telescope, vanishing boundary term and
limit-to-invariance argument. P-GOA-01 remains class C, estimated S/M.

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
