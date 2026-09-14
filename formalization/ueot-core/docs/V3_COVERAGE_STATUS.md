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
audit, safe main integration, and ledger synchronization. Feature-green work
alone never changes this ledger.

## Current source-level coverage

| status | count |
|---|---:|
| **proved, staged by this ledger checkpoint** | **74** |
| **partial** | **0** |
| **pending / not yet counted** | **32** |
| **total** | **106** |

This branch stages **74/106** after P-REF-02 completed source-semantic,
feature/assembly, clean-integration, PR CI, proof-main merge and resulting-main
CI gates. **74/106 is not called full-green until this ledger checkpoint itself
passes PR CI, lands on `main`, and the resulting main CI succeeds.**

`pending` means only “not yet counted proved”; it does not mean no relevant
mathematics or Lean code exists.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-06, P-STAT-07, P-STAT-08, P-STAT-09
- **Invariant / identifiability:** P-INV-01, P-INV-02, P-INV-03, P-INV-04, P-INV-05
- **Quotient:** P-QUO-03
- **Refinement / agency:** P-REF-01, P-REF-02, P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-ALI-02, P-ALI-03
- **Composition:** P-COMP-03, P-COMP-04, P-COMP-05, P-COMP-06, P-COMP-07
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03
- **Evolution:** P-EVO-01, P-EVO-02
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01

Count check: `73 + P-REF-02 = 74`.

## Newly staged promotion — P-REF-02

Frozen Core 3 §27.2 is implemented at the declared belief-state interface:

- finite latent static parameter and hidden state model;
- normalized joint beliefs and controlled prediction;
- predictive next-observation law depends only on current belief and action;
- positive-evidence Bayes posterior is the displayed normalized formula;
- zero evidence is explicit `modelConflict`, never an arbitrary posterior;
- a general Standard-Borel posterior/disintegration interface reconstructs the
  same one-step joint law and averages back to the predicted latent law;
- one-step bounded-discount reward/continuation data are functions of `(b,a)`,
  which is the frozen source's belief-control reduction boundary;
- no duplicate or stronger generic Bellman theorem is claimed by this P-ID.

Canonical theorem surface:
- `UEOT.V3.PRef02.p_ref_02_general_joint`;
- `UEOT.V3.PRef02.p_ref_02_general_update`;
- `UEOT.V3.PRef02.p_ref_02_discrete_observation`;
- `UEOT.V3.PRef02.p_ref_02_discrete_posterior`;
- `UEOT.V3.PRef02.p_ref_02_discrete_modelConflict`;
- `UEOT.V3.PRef02.p_ref_02_discounted_step`.

Promotion evidence:
- proof feature family: `formal/pref02-belief-core-v1`;
- clean integration branch: `formal/pref02-main-integration-v1`;
- clean integration head: `0037fc0e494b46200ead20e2f5c3ce84a66eb577`;
- clean integration push CI `34808870460`: success;
- clean integration PR #71;
- PR-triggered CI `34810019287`: success;
- proof main commit `c1213a6014f37a84bdfe128cced1a472b682248e`;
- proof resulting-main CI `34810452071`: success;
- frozen-source semantic audit: complete;
- prohibited-proof audit: clean (`sorry=0`, `admit=0`, `native_decide=0`,
  unsourced `axiom=0`).

**Status: PROVED / COUNTED pending this ledger/recovery checkpoint's own PR and
resulting-main CI.**

## Previous full-green checkpoint — 73/106

The authoritative full-green baseline before this P-REF-02 promotion was
`main@0285b7b8da4c94cc7d8d890336cd97e5e64718cb`, with official resulting-main
CI `34808329108` successful. All 73 counted P-IDs at that checkpoint remain
closed absent a substantive frozen-source mismatch or CI regression.

## Active uncounted lanes

### P-REF-03 — feature-green, awaiting clean integration

Branch `formal/pref03-free-information-v1` preserves the frozen arbitrary-signal
scope by representing the information as an arbitrary sub-sigma-algebra. Only
the action set is finite and each action payoff is integrable. Current final
feature head is `7ed287043f6da1e3d53bc67a95b7377bb989382a`; official run
`34809014590` succeeded. The effective source change is only
`UEOT/V3/FreeInformationValue.lean` plus one top-level import. Because its
feature history diverged from main, it must be clean-integrated from the next
full-green main and remains **uncounted** here.

### P-BRG-01 — active proof

Frozen §26.3 requires the exact no-mutation fixed-fitness replicator closed
form, preservation of initial support, exponential disappearance of all
initially supported strictly suboptimal mass, and preservation of initial
relative proportions among support maximizers. Branch
`formal/pbrg01-fixed-fitness-v1` is proving this source contract. The current
feature work contains an algebraic layer plus a concentration layer with
explicit geometric envelopes; it remains **uncounted** until CI and semantic
review establish the full frozen clause.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers, feature-green branches, source
audits or proof-main commits never count on their own.
