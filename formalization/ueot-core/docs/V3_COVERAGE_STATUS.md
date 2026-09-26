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
| **proved, staged by this ledger checkpoint** | **104** |
| **partial** | **0** |
| **pending / not yet counted** | **2** |
| **total** | **106** |

This branch stages **104/106** after P-KL-05 completed source-semantic, feature,
clean-integration, proof-PR, proof-main, and proof resulting-main gates.
**104/106 is not called FULL-GREEN until this ledger checkpoint itself passes
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
- **KL / path information:** P-KL-01, P-KL-02, P-KL-03, P-KL-04, P-KL-05
- **Evolution:** P-EVO-01, P-EVO-02, P-EVO-03, P-EVO-04
- **Process interface:** P-API-01
- **Algorithmic quotient:** P-ALG-01
- **GOA:** P-GOA-01, P-GOA-02, P-GOA-03, P-GOA-04
- **Core assembly:** P-CORE-01

Count check: `103 + P-KL-05 = 104`.

## Newly staged promotion — P-KL-05

Frozen Core 3 §22.5 distinguishes the full Girsanov noise/probability space
from the observed state-path law. Under the source Girsanov setup and finite
control energy, the full-space relative entropy is exactly one half the
expected clock-time control energy, whereas an observed state path receives
only the data-processing upper bound in general.

The formalization preserves that distinction:

1. `TerminalGirsanovData` explicitly records a progressively measurable
   control relative to a continuous-time filtration and a.e. interval
   integrability of the clock-time energy;
2. the controlled law is the actual density change `Q = P0.withDensity Z`,
   with the source exponential density for `Z`;
3. the terminal Girsanov stochastic-integral shift is part of the source
   setup, but neither KL conclusion is assumed;
4. the controlled stochastic integral is represented as the terminal value
   of a zero-start martingale, so integrability and zero expectation are
   derived from Mathlib martingale lemmas rather than inserted as certificates;
5. the full-space KL equality is derived from the actual Radon--Nikodym
   derivative and Mathlib `klDiv_of_ac_of_integrable`; and
6. the observed-state-path statement is a measurable pushforward inequality
   from Mathlib `klDiv_map_le`, not an incorrect equality.

Canonical theorem surface:
- `UEOT.V3.GirsanovPathKL.TerminalGirsanovData.p_kl_05`.

Supporting module:
- `UEOT/V3/GirsanovPathKL.lean`.

Promotion evidence:
- frozen §22.5 source contract rechecked against the canonical source;
- final feature head `c8bb0e2cf05e17be6c720b3493354165de712bd0`;
- feature root CI `36228481080`: success;
- clean integration head `9b5623ded2c67fe972ca8507b73f94b312446bd6`
  from `main@e4590074b7d292e5c24e8f19ce79d198f543c69f`;
- feature/integration tree identity:
  `9ff34d07229c17912c9b96655fe767867bb23621`;
- clean integration root CI `36228493685`: success;
- proof PR #139 exact-head root CI `36228972886`: success;
- proof main `15005abdb80bcf059077e08a33b2b80965b12b4e`;
- proof resulting-main root CI `36229427792`: success;
- final local `lake build UEOT`: success (`9009/9009` jobs);
- prohibited-proof audit clean (`sorry=0`, Lean `admit=0`,
  `native_decide=0`, new `axiom=0`, escape-hatch `opaque=0`);
- audited `#print axioms` for `p_kl_05` and the main supporting conclusions:
  only `propext`, `Classical.choice`, `Quot.sound`.

**Status: PROVED / PROOF-COMPLETE, staged for counting by this ledger checkpoint.**

## Previous FULL-GREEN checkpoint — 103/106

P-KL-04 and all earlier counted P-IDs form the authoritative 103/106 baseline.
Its ledger landed at `main@e4590074b7d292e5c24e8f19ce79d198f543c69f`
with ledger resulting-main CI `36225697848` success.

All counted P-IDs remain closed absent a substantive frozen-source mismatch or
CI regression. P-KL-05 is proof-complete on the current proof main but is not
counted FULL-GREEN until this independent ledger lifecycle completes.

## Branchless frontier evidence after this ledger closes

No theorem branch is opened by this promotion. After a successful 104/106
ledger lifecycle, the exact remaining two P-IDs are:

- P-QSD-04
- P-CTL-03

The next theorem lane must be selected dynamically only after the exact 104/106
FULL-GREEN `main` exists and the source/dependency/branch preflight is repeated.
## Reproducibility task

The exact canonical source bytes are still not synchronized into the public
repository. Source theorem proof status remains distinct from that artifact
synchronization task.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract. Helpers, source audits, feature-green
branches, proof-main commits, or ledger staging do not count on their own.
