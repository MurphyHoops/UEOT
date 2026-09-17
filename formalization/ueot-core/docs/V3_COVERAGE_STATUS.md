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
| **proved, staged by this ledger checkpoint** | **85** |
| **partial** | **0** |
| **pending / not yet counted** | **21** |
| **total** | **106** |

This branch stages **85/106** after P-QUO-02 completed source-semantic, feature,
clean-integration, proof-PR, proof-main and proof resulting-main gates.
**85/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Quotient:** P-QUO-01, P-QUO-02, P-QUO-03
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

Count check: `84 + P-QUO-02 = 85`.

## Newly staged promotion — P-QUO-02

Frozen Core 3 §20.2 is the span-sensitive approximate controlled quotient
theorem. On top of the finite discounted-control foundation it assumes the same
fibre/action correspondence as P-QUO-01, reward approximation error
`epsilon_r`, and **all-action pushed-forward transition total variation** error
`epsilon_p`.

The formalization represents the TV premise itself as event-supremum total
variation of exact finite PMFs. P-MET-02 derives the continuation expectation
error with the actual macro optimal-value span; no expectation-gap premise is
substituted. Defining

`w = Vbar* ∘ f`,

`delta = epsilon_r + beta * epsilon_p * span(Vbar*)`,

`D = delta / (1-beta)`,

the all-action Q comparison gives an optimal Bellman residual for `w`, and the
counted P-CTL-01 residual certificate yields

`||V* - w||_infinity <= D`.

For any macro stationary argmax selector, including tied argmax cases, the same
actionwise comparison gives a fixed-policy Bellman residual. Its selector value
is therefore within `D` of `w`; causal optimal domination plus the two `D`
bounds gives the source policy guarantee

`0 <= V* - V^hatpi <= 2D`

pointwise.

Canonical theorem surface:
- `UEOT.V3.FiniteDiscountedControl.ApproxControlQuotient.p_quo_02`.

Supporting modules:
- `UEOT/V3/FiniteDiscountedSelectorValue.lean`;
- `UEOT/V3/FiniteDiscountedApproxQuotient.lean`;
- `UEOT/V3/FiniteDiscountedApproxQuotientBounds.lean`.

Promotion evidence:
- feature branch `formal/pquo02-span-approx-quotient-v1`;
- selector-value checkpoint `5b7d0e919c4800c27544b427ba41b0f61e123f67`, root CI `35125066423`: success;
- true-TV/span checkpoint `c8c21e39037f808fbc4559709f0aca92c8dc4cc8`, root CI `35125945423`: success;
- source-facing head `f2de244a32a29c336cb07a943489d00c5d11a3a8`, root CI `35128138029`: success;
- source-semantic audit: complete;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- clean integration `formal/pquo02-main-integration-v1@f2de244a32a29c336cb07a943489d00c5d11a3a8`;
- clean integration root CI `35128929614`: success;
- proof PR #98;
- proof PR root CI `35129778828`: success;
- proof main commit `28b872857b2cd8b4a546433f858015443f861ce4`;
- proof resulting-main root CI `35162246623`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 84/106

P-QUO-01 and all earlier counted P-IDs form the authoritative 84/106 baseline.
Its ledger landed at `main@b9fc5751f4a04de210740f5df8a8699a0faada2d`
with ledger resulting-main CI `35124093049` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Next source-first front — P-QUO-04

Frozen §20.4 requires, for fixed policy `pi` and bounded reference function `w`,

`b_pi = r^pi + beta P^pi w - w`,

`d_mu^pi = (1-beta) * sum_{t>=0} beta^t mu(P^pi)^t`,

and the exact identities

`V^pi - w = (I-beta P^pi)^(-1)b_pi`,

`mu(V^pi-w) = E_{d_mu^pi}[b_pi]/(1-beta)`.

A sup-norm residual bound is not a source-equivalent substitute. The preferred
finite implementation will introduce a stationary randomized policy interface,
induced reward/kernel, policy-evaluation value, a Neumann/resolvent operator
proved to invert `I-beta P^pi`, and a discounted occupancy probability row.
Deterministic selectors then embed as a special case.

This infrastructure must expose state-action discounted occupancy because the
already-audited P-QUO-05 depends on it. Frozen §20.5 uses local

`delta(x,a)=epsilon_r(x,a)+beta*epsilon_p(x,a)*span(Vbar*)`

and requires

`J(pi*;mu)-J(hatpi;mu) <=
 (E_{d_mu^{pi*}} delta + E_{d_mu^{hatpi}} delta)/(1-beta)`.

P-QUO-05 remains a later lane; it must not be opened concurrently with
P-QUO-04.

## Grounded non-quick fronts

Among the remaining source propositions are P-CTL-02/03, P-PER-02, P-ALI-01,
P-DDH-02/03/04/05, P-KL-04/05, P-EVO-03/04, P-QSD-01/04, P-QUO-04/05 and the
remaining GOA/control fronts. Their exact order remains source/API dependent;
no weaker finite/toy/assumed-conclusion surrogate may be counted.

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
