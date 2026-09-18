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
| **proved, staged by this ledger checkpoint** | **88** |
| **partial** | **0** |
| **pending / not yet counted** | **18** |
| **total** | **106** |

This branch stages **88/106** after P-GOA-01 completed source-semantic, feature,
clean-integration, proof-PR, proof-main and proof resulting-main gates.
**88/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **GOA:** P-GOA-01

Count check: `87 + P-GOA-01 = 88`.

## Newly staged promotion — P-GOA-01

Frozen Core 3 §21.2 fixes a finite stochastic kernel `P`, an arbitrary initial
probability `mu0`, and the positive-N Cesaro averages

`bar_mu_N = N^(-1) * sum_{t=0}^{N-1} mu0 P^t`.

The source-facing claim has exactly two parts:

1. the Cesaro sequence has at least one convergent subsequence;
2. every convergent subsequential limit `nu` is invariant: `nu P = nu`.

The formalization uses `Matrix.rowStochastic ℝ S` and `stdSimplex ℝ S`.  It
packages the exact orbit `mu0 P^t`, defines the source average with `N=n+1`, and
proves the exact telescope

`bar_mu_N P - bar_mu_N = (mu0 P^N - mu0)/N`.

The boundary term tends to zero from the simplex coordinate bounds. Compactness
of the finite probability simplex yields a convergent subsequence, and continuity
of the residual plus its global convergence to zero proves invariance for every
convergent subsequential limit. No irreducibility, aperiodicity, mixing,
uniqueness, full Cesaro convergence, convergence of `mu0 P^N`, or attractivity
assumption/conclusion is used as a substitute for the frozen anchor.

Canonical theorem surface:
- `UEOT.V3.FiniteCesaroInvariant.p_goa_01`.

Supporting modules:
- `UEOT/V3/FiniteCesaroInvariant.lean`.

Promotion evidence:
- frozen source original `UEOT_Core_Mathematics_v3.0_Complete.md` independently re-read from the project File Library and hash-matched to the canonical SHA-256;
- source-facing feature commit `3920995eb111c01cffcd0c6369182f70bb78e7f3`;
- feature `lake build UEOT`: success (`8980` jobs);
- independent source-semantic re-audit: PASS against frozen §21.2;
- prohibited-proof audit: clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- `#print axioms ...FiniteCesaroInvariant.p_goa_01`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration `formal/pgoa01-main-integration@0f61d3539fae0c72b9465189122f5308b7079621` from `main@f3f7945ddae12ad95eedf3c7e773354456d59564`;
- feature and clean-integration tree hashes identical: `91af9fcb4901be6719a9ac61cd502a1de11915d1`;
- clean integration root CI `35340642119`: success;
- proof PR #107;
- proof PR root CI `35341218386`: success;
- proof main commit `85cf2781c78b63b0f69981951eacc86f54015b50`;
- proof resulting-main root CI `35341843473`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 87/106

P-QUO-05 and all earlier counted P-IDs form the authoritative 87/106 baseline.
Its ledger landed at `main@f3f7945ddae12ad95eedf3c7e773354456d59564`
with ledger resulting-main CI `35335445145` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. In particular P-QUO-03 and P-TEL-01 are already counted and must
not be reopened or double-counted.

## Next source-first front after this ledger closes

No further theorem lane is opened by this promotion. The dynamic frontier now
recommends P-GOA-02. Frozen §21.3 defines

`alpha(P) = max_{x,x'} D_TV(P_x, P_x')`

and uses the exact finite-kernel contraction

`D_TV(mu P, nu P) <= alpha(P) D_TV(mu,nu)`.

The main P-GOA-02 anchor requires uniqueness of an invariant probability when
`alpha(P)<1`, plus the stationary perturbation bound

`D_TV(mu,muhat) <= epsilon/(1-alpha(P))`

under `mu P=mu`, `muhat Phat=muhat`, and row error at most `epsilon`.  The
denominator uses `alpha(P)`; the later source remark about
`alpha(Phat) <= alpha(P)+2epsilon` is separate from the main anchor.  Existing
UEOT TV semantics are event-supremum TV.  The finite Dobrushin layer therefore
needs an exact finite-row TV algebra bridge preserving the standard `1/2`
normalization, then the pairwise-row convexity/contraction argument. P-GOA-02
remains class C, estimated M.

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
