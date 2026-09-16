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
the full-green count.

## Current source-level coverage

| status | count |
|---|---:|
| **proved, staged by this ledger checkpoint** | **84** |
| **partial** | **0** |
| **pending / not yet counted** | **22** |
| **total** | **106** |

This branch stages **84/106** after P-QUO-01 completed source-semantic, feature,
clean-integration, proof-PR, proof-main and proof resulting-main gates.
**84/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Quotient:** P-QUO-01, P-QUO-03
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

Count check: `83 + P-QUO-01 = 84`.

## Newly staged promotion — P-QUO-01

Frozen Core 3 §20.1 is the exact controlled quotient theorem. On top of the
counted finite discounted-control foundation it requires a surjection `f`, the
same admissible action type on each fibre, exact reward closure and exact
**all-action** pushed-forward transition closure. These hypotheses imply
Bellman intertwining on pulled-back macro values; uniqueness of the Bellman
fixed point then gives

`V* = Vbar* ∘ f`.

The formalization also proves actionwise optimal-Q equality and lifts any macro
stationary argmax selector, including tie cases, to a micro stationary policy
whose infinite discounted value is optimal against the full causal
history-dependent randomized policy class. It does not replace all-action
closure by Markovity under one policy and does not substitute the unrelated
P-INT-02 `StructuredQuotient` interface.

Canonical theorem surface:
- `UEOT.V3.FiniteDiscountedControl.ExactControlQuotient.p_quo_01`.

Supporting modules:
- `UEOT/V3/FiniteDiscountedSelector.lean`;
- `UEOT/V3/FiniteDiscountedExactQuotient.lean`.

Promotion evidence:
- feature branch: `formal/pquo01-exact-control-quotient`;
- final feature head: `8ffa1e4cbbe73eeb3867c152630a1029c998e231`;
- selector checkpoint root CI `35113940062`: success;
- clean integration branch: `formal/pquo01-main-integration-v1`;
- clean integration head: `0427733fe363ba3b0a697879df42d2d141786a72`;
- clean integration root CI `35118874289`: success;
- source-semantic audit: complete;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- proof PR #96;
- proof PR root CI `35120644387`: success;
- proof main commit: `25af2f3d8d537600453b5be3bcb30de6af6c0e3e`;
- proof resulting-main root CI `35121419393`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 83/106

P-CTL-01 and all earlier counted P-IDs form the authoritative 83/106 baseline.
Its ledger landed at `main@995c99683e0ae225f8df46108fd1442038c3963a`
with ledger resulting-main CI `35109381744` success. The subsequent audited
branch-governance main `2d1373a0eb417496cdd83bfc948e1806f4427587`
kept the same 83/106 source coverage and passed root CI `35112629545`.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-TEL-01 is already counted and must not be
reopened or double-counted.

## Next source-first front — P-QUO-02

A fresh frozen-source audit was completed during the P-QUO-01 CI window, but no
second proof branch was opened. Frozen §20.2 requires uniform reward error
`epsilon_r`, all-action pushed-forward transition TV error `epsilon_p`,

`w = Vbar* ∘ f`,
`delta = epsilon_r + beta * epsilon_p * span(Vbar*)`,
`D = delta / (1 - beta)`,

and both

`||V* - w||_infinity <= D`

and the lifted macro-optimal-policy regret bound

`0 <= V* - V^hatpi <= 2D`.

The source explicitly prioritizes the actual span. The proof lane must reuse the
counted P-MET-02 span-times-TV expectation bound and P-CTL-01 Bellman residual
certificate, plus the generic selector evaluation layer introduced with
P-QUO-01. An expectation-gap premise may not replace the source TV premise, and
one-policy closure may not replace all-action closure.

## Grounded non-quick fronts

Among the remaining source propositions are P-CTL-02/03, P-PER-02, P-ALI-01,
P-DDH-02/03/04/05, P-KL-04/05, P-EVO-03/04, P-QSD-01/04, P-QUO-04/05 and the
remaining GOA/control-quotient fronts. Their exact order remains source/API
dependent; no weaker finite/toy/assumed-conclusion surrogate may be counted.

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
