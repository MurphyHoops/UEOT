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
| **proved, staged by this ledger checkpoint** | **89** |
| **partial** | **0** |
| **pending / not yet counted** | **17** |
| **total** | **106** |

This branch stages **89/106** after P-GOA-02 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**89/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **GOA:** P-GOA-01, P-GOA-02

Count check: `88 + P-GOA-02 = 89`.

## Newly staged promotion — P-GOA-02

Frozen Core 3 §21.3 uses canonical event-supremum total variation, which on a
finite space has the standard `1/2 * L1` normalization. For a finite stochastic
kernel `P`, it defines the literal Dobrushin coefficient

`alpha(P) = max_{x,x'} D_TV(P_x, P_x')`

and the exact contraction

`D_TV(mu P, nu P) <= alpha(P) D_TV(mu, nu)`.

When `alpha(P) < 1`, the frozen anchor requires a unique invariant probability.
For stationary `mu P = mu`, `muhat Phat = muhat`, and uniform same-state row
error at most `epsilon`, it also requires

`D_TV(mu, muhat) <= epsilon / (1 - alpha(P))`.

The formalization stays in UEOT's canonical event-supremum TV, defines the
literal finite maximum over row pairs, proves the exact contraction, obtains
invariant-law existence from P-GOA-01 and uniqueness from contraction, and
proves the stationary perturbation bound with the baseline `alpha(P)`.
It does not assume `alpha(Phat)<1`, irreducibility, aperiodicity, a Doeblin
condition, a symmetric denominator, or any factor-two renormalization.

Canonical theorem surface:
- `UEOT.V3.FiniteDobrushin.p_goa_02`.

Supporting module:
- `UEOT/V3/FiniteDobrushin.lean`.

Promotion evidence:
- canonical frozen source hash reverified before implementation;
- source-facing feature commit `e04946d6ef9a9408a5e36aa67fa7a0c0f7cfdf96`;
- feature root CI `35345265060`: success;
- full local `lake build UEOT`: success (`8981` jobs);
- independent source-semantic re-audit: PASS against frozen §21.3;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...FiniteDobrushin.p_goa_02`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pgoa02-main-integration@c3a0355e380a6d4e25179515599c2594db65d921` from `main@465796d119483f60eb2c1b296d78870a79f92522`;
- feature and clean-integration tree hashes identical: `6aeeaab1e2abc61cee27ee8b7d470e0ba0226709`;
- clean integration root CI `35346669326`: success;
- proof PR #109 root CI `35347283556`: success;
- proof main commit `c2e2f56736aa29965a4d964c28c13688d5b237c2`;
- proof resulting-main root CI `35347998899`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 88/106

P-GOA-01 and all earlier counted P-IDs form the authoritative 88/106 baseline.
Its ledger landed at `main@465796d119483f60eb2c1b296d78870a79f92522`
with ledger resulting-main CI `35343788114` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. Branchless source/API audits
currently classify the leading uncounted fronts as:

- P-DDH-04: Class C, S/M; common two-dimensional differentiable bottleneck
  implies the vertically stacked environment-response Jacobian has rank at most 2;
- P-DDH-03: Class C, M; finite exponential-family KL minimization;
- P-GOA-04: Class C, L; symmetric killed-kernel spectral/Q-process stability;
- P-GOA-03: Class D, L-XL; requires a new finite transient/recurrent decomposition,
  absorption-weight, and periodic-safe full Cesaro-mixture stack.

P-CORE-01 remains hard-blocked by the recurrent-structure branch of P-GOA-03.
The next proof lane must be selected dynamically only after this 89/106 ledger
becomes FULL-GREEN.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
