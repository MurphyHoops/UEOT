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
| **proved, staged by this ledger checkpoint** | **75** |
| **partial** | **0** |
| **pending / not yet counted** | **31** |
| **total** | **106** |

This branch stages **75/106** after P-REF-03 completed source-semantic,
feature, clean-integration, PR CI, proof-main merge and resulting-main CI gates.
**75/106 is not called full-green until this ledger checkpoint itself passes PR
CI, lands on `main`, and the resulting main CI succeeds.**

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
- **Refinement / agency:** P-REF-01, P-REF-02, P-REF-03, P-REF-04, P-REF-05
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

Count check: `74 + P-REF-03 = 75`.

## Newly staged promotion — P-REF-03

Frozen Core 3 §27.3 is implemented at its declared one-decision information-value
scope:

- the signal is represented by an arbitrary sub-σ-algebra; it is not
  finite-ized;
- the action set is finite and nonempty;
- every action payoff is integrable;
- free information may be ignored because every fixed action remains feasible;
- the pointwise maximum of conditional expected payoffs dominates each fixed
  action;
- integration plus the conditional-expectation tower identity yields that the
  informed expected value weakly dominates the best fixed-action value.

Canonical theorem surface:
- `UEOT.V3.FreeInformationValue.p_ref_03`.

Promotion evidence:
- feature branch: `formal/pref03-free-information-v1`;
- feature head: `7ed287043f6da1e3d53bc67a95b7377bb989382a`;
- feature CI `34809014590`: success;
- clean integration branch: `formal/pref03-main-integration-v1`;
- clean integration head: `1403f8529ec6920bfe2fb4ecb86ab55a2cfb6c3b`;
- clean integration CI `34812358314`: success;
- clean integration PR #73;
- PR-triggered CI `34812784352`: success;
- proof main commit `0ebef06b4a2be2eb88d5b5708ca4bd5901db7b92`;
- proof resulting-main CI `34814852905`: success;
- frozen-source semantic audit: complete;
- prohibited-proof audit: clean (`sorry=0`, `admit=0`, `native_decide=0`,
  unsourced `axiom=0`).

**Status: PROVED / COUNTED pending this ledger/recovery checkpoint's own PR and
resulting-main CI.**

## Previous full-green checkpoint — 74/106

The authoritative full-green baseline before this P-REF-03 promotion was
`main@11dcc0349aeeba6444655752e1aca40eeaf75e02`, with official resulting-main
CI `34811815264` successful. All 74 counted P-IDs at that checkpoint remain
closed absent a substantive frozen-source mismatch or CI regression.

P-REF-04 and P-REF-05 are already members of that counted set. The later
source-facing wrapper branches audited during this cycle are interface
hardening only and must **not** be double-counted as new P-IDs.

## Active uncounted lane

### P-BRG-01 — feature-green, awaiting clean integration

Frozen §26.3 requires the exact no-mutation fixed-fitness replicator recurrence
to imply its explicit closed form, preservation of initial support, exponential
disappearance of all initially supported strictly suboptimal mass, and
preservation of initial relative proportions among support maximizers.

Branch `formal/pbrg01-fixed-fitness-v1` now contains:

- `UEOT/V3/FixedFitnessSelection.lean`: positive denominators, exact closed-form
  trajectory, recurrence, normalization, support preservation and equal-fitness
  ratio laws;
- `UEOT/V3/FixedFitnessRecurrenceUniqueness.lean`: the missing converse/uniqueness
  direction proving that any trajectory with the frozen initial condition and
  recurrence equals the displayed closed form;
- `UEOT/V3/FixedFitnessConcentration.lean`: support maximizer, explicit
  per-type geometric envelopes, a finite sum of those exponential envelopes for
  total suboptimal mass, convergence to zero, and maximizer-ratio preservation.

Latest feature head `b3f47b89ad901fb11f322d7f386d5a86ba06e708` passed official CI
`34815094214`. Frozen-source semantic audit and prohibited-proof audit are
complete. P-BRG-01 remains **uncounted** until it is clean-integrated from the
then-latest FULL-GREEN main and passes the complete promotion lifecycle.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers, feature-green branches, source
audits or proof-main commits never count on their own.
