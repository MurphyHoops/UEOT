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
| **proved, staged by this ledger checkpoint** | **98** |
| **partial** | **0** |
| **pending / not yet counted** | **8** |
| **total** | **106** |

This branch stages **98/106** after P-EVO-03 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**98/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Evolution:** P-EVO-01, P-EVO-02, P-EVO-03, P-EVO-04
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04
- **Core assembly:** P-CORE-01

Count check: `97 + P-EVO-03 = 98`.

## Newly staged promotion — P-EVO-03

Frozen Core 3 §25.4 is the finite primitive mean-matrix Perron growth theorem.
For a finite nonnegative primitive matrix `M`, K-PF-01 supplies the positive
Perron data `R`, `r`, `l`, the normalizations `l 1 = 1`, `l r = 1`, the
asymptotic rank-one limit `R⁻ⁿ Mⁿ → r l`, and positive Perron-eigendirection
uniqueness. For every nonzero nonnegative initial count row `z₀`, the source
requires both scaled mean growth and normalized composition convergence, and it
characterizes every strictly positive linear reproductive valuation.

The formalization preserves that source contract:

1. `KPF01Certificate M` is an explicit standard-theorem interface tied to the
   same primitive nonnegative matrix `M`; it carries the source Perron
   eigenrelations, normalizations, rank-one power limit, positive-eigenvector
   uniqueness, and strict spectral dominance without claiming an unsourced
   constructor from `Matrix.IsPrimitive M`;
2. the source initial row is represented by finite natural counts and converted
   canonically to a nonnegative real row; nonzero counts plus `r > 0` derive the
   strictly positive initial reproductive value `z₀ r`;
3. `scaledMean_tendsto` derives
   `R⁻ⁿ (z₀ Mⁿ)_j → (z₀ r) l_j` directly from the K-PF coordinate limit and a
   finite sum;
4. `scaledMass_tendsto` and eventual positivity of the mean mass derive the
   denominator limit `(z₀ r)` using `∑ l = 1`;
5. `composition_tendsto` cancels the common Perron scaling and proves
   `(z₀ Mⁿ)_j / (z₀ Mⁿ 1) → l_j`, with the finite exceptional prefix handled
   only through eventual positivity; and
6. the valuation identity for every nonnegative row is specialized to coordinate
   unit rows to derive `Mw = ρw`; K-PF positive-eigenvector uniqueness then gives
   `ρ = R` and `w = c r` for some `c > 0`.

Canonical theorem surface:
- `UEOT.V3.EvolutionPerronGrowth.p_evo_03`.

Supporting module:
- `UEOT/V3/EvolutionPerronGrowth.lean`.

Promotion evidence:
- frozen §25.4 / K-PF-01 source contract independently re-audited twice: GREEN;
- source-facing feature commit
  `340a56d4ca19236bba141b79b8471ed95a512995`;
- feature tree `7ee94553049f5d6de825a9883695719e2399a4a7`;
- feature root CI `35576131678`: success;
- focused module, root import, and full local `lake build UEOT`: success (`8990` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`, `native_decide=0`, unsourced new `axiom=0`);
- audited `#print axioms` outputs only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pevo03-main-integration@11e17eaab6385017c1515afaaff1a460a91e79c6`
  from `main@85b3e410ab9a1ef71ca512c0e8f8f6a2f9aa6cb2`;
- feature and clean-integration tree hashes identical:
  `7ee94553049f5d6de825a9883695719e2399a4a7`;
- clean integration focused/root/full local checks: success (`8990` jobs);
- clean integration root CI `35576926135`: success;
- proof PR #127 exact-head root CI `35577642954`: success;
- proof main commit `4d581a675f4057069dbe19db7d0e182bfdf91ff8`;
- proof resulting-main root CI `35578270234`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 97/106

P-CORE-01 and all earlier counted P-IDs form the authoritative 97/106 baseline.
Its ledger landed at `main@85b3e410ab9a1ef71ca512c0e8f8f6a2f9aa6cb2`
with ledger resulting-main CI `35573090853` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. P-EVO-03 is proof-complete on the current proof main but is not
counted FULL-GREEN until this independent ledger lifecycle completes.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. After a successful 98/106 ledger
lifecycle, the exact remaining eight P-IDs are:

- P-PER-02
- P-QSD-01
- P-QSD-04
- P-CTL-02
- P-CTL-03
- P-KL-04
- P-KL-05
- P-ALI-01

The next theorem lane must be selected dynamically only after the exact 98/106
FULL-GREEN `main` exists and the source/dependency/branch preflight is repeated.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
