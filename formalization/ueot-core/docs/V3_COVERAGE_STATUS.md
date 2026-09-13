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
| **proved, staged by this ledger checkpoint** | **70** |
| **partial** | **0** |
| **pending / not yet counted** | **36** |
| **total** | **106** |

This branch stages 70/106 after P-KL-02 completed its proof, clean-integration,
and post-main proof gates. **70/106 is not called full-green until this ledger
checkpoint itself passes PR CI, lands on `main`, and the resulting main CI
succeeds.**

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
- **Refinement / agency:** P-REF-04, P-REF-05
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

Count check: `69 + 1 = 70`.

## Newly staged promotion — P-KL-02

Frozen source §22.2 is implemented at full strength. For `q = P0(A)`,
`0 < q < 1`, and `0 ≤ p ≤ 1`, the optimization is literally over **all**
probability laws `Q ≪ P0` satisfying `Q(A) ≥ p`:

- if `p ≤ q`, the infimum is `0`, attained by `P0`;
- if `p > q`, the infimum is exactly `dBern p q`;
- the active optimizer is the explicit two-region RN tilt
  `(p/q) 1_A + ((1-p)/(1-q)) 1_{Aᶜ}`;
- the optimizer is proved to be a probability law, absolutely continuous with
  respect to `P0`, to have exact event mass `p`, and to have exact KL cost
  `dBern p q`;
- the endpoint `p = 1` is retained.

Canonical theorem:
- `UEOT.V3.PathEventIProjection.p_kl_02`.

Supporting source-facing construction includes:
- `UEOT.V3.PathEventIProjection.eventIProjection`;
- `UEOT.V3.PathEventIProjection.eventIProjection_klDiv_eq_dBern`;
- `UEOT.V3.BernoulliKLMonotone.dBern_mono_active`;
- literal feasible-law infimum `EventFeasibleLaw` / `eventKLIInf`.

Promotion evidence:
- full-contract feature head `cb78b0df87ef64fc0bc61e1e320ff901247d00cd`;
- feature CI `34768634473`: success;
- clean integration branch `formal/pkl02-clean-int-cb78`;
- clean integration head `d30d31e15f38b349488edf4a5b12c94bace70031`;
- clean integration PR #62;
- clean integration CI `34769135038`: success;
- proof main commit `60ac78273200f5152a5e8d8286c840697e69bb51`;
- proof post-main CI `34769394882`: success;
- exact clean-integration diff: four P-KL-02 modules plus four top-level imports;
- prohibited-proof audit: clean;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED pending this ledger/recovery checkpoint's own PR and
main CI.**

## Previous full-green checkpoint — P-EVO-02 / 69 of 106

P-EVO-02 is already fully counted. Its exact shared-label mutual-information
identity is on main with joint-pair independence encoded structurally and exact
copying preserved. Feature CI `34763489145`, clean-integration CI `34765061853`,
proof post-main CI `34765399086`, and 69/106 ledger main CI `34766813335` all
succeeded. The later recovery checkpoint `main@e3f046fcf4096a1bb6acb561afe1e31244e3aaad`
also passed CI `34767624927`.

## Promotion-ready next lane — P-API-01

P-API-01 is **not counted** in the 70 above. Its frozen §28.3 process-interface
contract has completed a feature proof and source audit:

- branch `formal/papi01-process-interface-fresh`;
- feature head `0f76d04a4dcc34b2d2aaa806d5803e4823561bbc`;
- feature CI `34769177051`: success;
- exact clause composes protocol lifts and measurable path readouts;
- approximate clause proves TV defect at most
  `min 1 (εAB + εBC)` using P-MET-01 and the TV triangle inequality;
- no control-interface structures from §28.4 are silently added;
- prohibited-proof audit: clean.

It must be clean-integrated only from the eventual **70/106 full-green main**.
Feature green alone does not increment coverage.

## Grounded next audit — P-ALG-01

Frozen §28.5 requires a genuine finite partition-refinement algorithm: finite
termination, stable/lumpable quotient correctness, coarsest stable refinement of
the initial output/reward partition, preservation of output/reward/all-action
one-step quotient laws, and induction to all corresponding finite-horizon output
laws. Mathlib provides `Finpartition` / refinement infrastructure, but no existing
UEOT implementation was found. This is a real algorithmic proof lane, not a
wrapper or an approximate floating-point clustering theorem.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
