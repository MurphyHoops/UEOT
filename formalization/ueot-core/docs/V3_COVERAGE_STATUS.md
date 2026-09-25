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
| **proved, staged by this ledger checkpoint** | **102** |
| **partial** | **0** |
| **pending / not yet counted** | **4** |
| **total** | **106** |

This branch stages **102/106** after P-CTL-02 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**102/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **Control:** P-CTL-01, P-CTL-02
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
- **Dual-drive / alignment:** P-DDH-01, P-DDH-02, P-DDH-03, P-DDH-04, P-DDH-05, P-ALI-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-01, P-COMP-02, P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02, P-EVO-03, P-EVO-04
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04
- **Core assembly:** P-CORE-01

Count check: `101 + P-CTL-02 = 102`.

## Newly staged promotion — P-CTL-02

Frozen Core 3 §19.3 states the compact discounted-control theorem: for compact
metric state and action spaces, a fixed nonempty action space, continuous
reward, a weakly continuous Markov kernel, and `0 < β < 1`, the Bellman
operator on `C(X, ℝ)` is a `β`-contraction with a unique continuous fixed
point and admits a measurable stationary optimal selector.

The formalization preserves that contract:

1. `CompactFellerControl.Model` uses compact metric `X` and `A`, fixed
   nonempty `A`, a continuous reward `C(X × A, ℝ)`, a Markov transition
   kernel, and `0 < β < 1`;
2. weak continuity is stored as continuity of
   `(x,a) ↦ ∫ v dP(x,a)` for every `v : C(X, ℝ)`, and
   `transitionPM_continuous` proves this is literal continuity into Mathlib's
   weak topology on `ProbabilityMeasure X`;
3. compact-action maximization keeps the Bellman operator inside `C(X, ℝ)`,
   and the expectation/sup-norm estimates prove the exact `β`-contraction;
4. Banach contraction gives the unique continuous fixed point
   `optimalValue` (with value-iteration convergence and a residual bound);
5. the measurable argmax selector is constructed directly from a fixed dense
   sequence, shrinking compact balls, countable `measurable_find`, a summable
   Cauchy bound, and a measurable limit; no general measurable-selection
   theorem or assumed optimal selector is imported;
6. arbitrary randomized full-history causal policies are evaluated by exact
   nested action/transition kernel recursion. Bellman domination bounds every
   such causal policy, while the measurable deterministic stationary greedy
   policy attains `optimalValue`.

Canonical theorem surface:
- `UEOT.V3.CompactFellerControl.Model.p_ctl_02`.

Supporting modules:
- `UEOT/V3/CompactArgmaxSelector.lean`;
- `UEOT/V3/CompactCausalOptimalityCore.lean`;
- `UEOT/V3/CompactFellerControl.lean`.

Promotion evidence:
- frozen §19.3 source/proof contract independently audited against the final
  implementation: CLEAR, zero blockers;
- source-facing feature commit
  `4b17ec1219f95dd9fa0480f46beea6e585c122eb`;
- feature tree `7497670441126d08f2fdb91b15ada086d2a9565f`;
- feature root CI `36139857404`: success;
- focused module, root import, and full local `lake build UEOT`: success
  (`8996` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, unsourced new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- clean integration
  `formal/pctl02-main-integration@863c9679b9d025a5f58282af4548fe5587e37860`
  from `main@7add6a361c8c46f7539d48ace389d403219b053d`;
- feature and clean-integration tree hashes identical:
  `7497670441126d08f2fdb91b15ada086d2a9565f`;
- clean integration root CI `36140869360`: success;
- proof PR #135 exact-head root CI `36141205611`: success;
- proof main commit `6a334b4c9870cf73ecda97a65965f822cf5e9e26`;
- proof resulting-main root CI `36142098525`: success.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 101/106

P-ALI-01 and all earlier counted P-IDs form the authoritative 101/106 baseline.
Its ledger landed at `main@7add6a361c8c46f7539d48ace389d403219b053d`
with ledger resulting-main CI `36125245565` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. P-CTL-02 is proof-complete on the current proof main but is not
counted FULL-GREEN until this independent ledger lifecycle completes.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. After a successful 102/106 ledger
lifecycle, the exact remaining four P-IDs are:

- P-QSD-04
- P-CTL-03
- P-KL-04
- P-KL-05

The next theorem lane must be selected dynamically only after the exact 102/106
FULL-GREEN `main` exists and the source/dependency/branch preflight is repeated.

## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
