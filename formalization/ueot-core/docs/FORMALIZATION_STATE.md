# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`.

Last synchronized: **2026-09-12**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

Promotion requires semantic source match, official import reachability, green
feature CI, clean-port CI, PR CI, main integration, green post-main CI, and
ledger synchronization.

## Current integrated checkpoint

| state | count |
|---|---:|
| integrated proved | **49** |
| promotion running | **1** |
| source audit | **3** |
| blocked warm lane | **1** |
| source P-IDs total | **106** |

The coverage ledger remains **49 proved / 57 pending** until P-STAT-06 finishes
promotion. `pending` does not mean "needs a new proof".

## Lane A — P-STAT-06 [PROMOTION]

P-STAT-06 is mathematically/source complete. Do not add another theorem/helper
unless PR/post-main CI exposes a real defect or a frozen-source mismatch.

Current evidence:

- feature head `5a5cb89d600059525cb775c9561aa50d031da38d`;
- feature full-repo CI `34684444280`: success;
- clean-port branch `formal/pstat06-clean-port`;
- clean-port head `2338d5fe7a5e9ae8a08cdfd469d0eacd35a80205`;
- clean-port CI `34684655595`: success;
- PR #40 against `main`;
- PR CI `34685272294`: running at this synchronization.

Canonical source theorem:
`UEOT.V3.HilbertMeanSourceFeatureRaw.source_feature_tail_exact_radius_raw_assumptions`.

Frozen radius:
`(1 + sqrt(2*log(L/alpha)))/sqrt(N)`.

Next actions are promotion only:
`PR CI -> merge main -> post-main CI -> ledger sync -> 50/106`.

## Lane B — P-INFO-02/03/04 [SOURCE_AUDIT]

Existing integrated reusable stack includes:

- `InformationCore.lean`: KL-backed MI/residual and KL data processing;
- `InformationStatistic.lean`: deterministic-statistic MI data processing,
  exact MI chain identity and conditional-information residual;
- `InformationDiscreteEntropy.lean`: discrete Shannon/KL bridge;
- `InformationMemoryBound.lean`: P-INFO-01 predictive-memory lower bound;
- `InformationEntropy.lean`: finite/uniform entropy results.

Source-audit result:

- **P-INFO-02:** CMI-to-average-TV theorem; missing the canonical conditional
  kernel TV expectation bridge and source wrapper. Likely a small proof lane.
- **P-INFO-04:** Fano identity-memory lower bound; existing entropy machinery is
  reusable, but the source-matched Fano theorem is not yet present. Likely a
  small/medium proof lane.
- **P-INFO-03:** zero-distortion predictive rate-distortion equality with random
  encoders; requires a genuine random-encoder/conditional-entropy interface.
  This is the main information-theory proof lane and must not be replaced by
  another deterministic wrapper.

Recommended proof order: **P-INFO-02 -> P-INFO-04 -> P-INFO-03**.

## Lane C — P-INT-01 [BLOCKED]

Blocked until the information packet fixes the canonical conditional-information
interface. Reuse prediction and information infrastructure; do not create a
second conditional-independence stack.

## Recovery protocol

1. Read `PID_STATUS.yaml`, then this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch current `main` SHA and latest relevant Actions.
3. For each active P-ID, distinguish `source_audit`, `proof`, `integration`,
   `promotion`, `blocked`, and `proved`.
4. Never infer "needs proof" from coverage `pending` alone.
5. Read the frozen proof contract before writing Lean.
6. Prove only listed missing obligations and reuse integrated infrastructure.
7. New proof modules must be reachable from `UEOT` / `UEOT.V3`.
8. Feature green is not coverage. Count only after post-main green + ledger sync.
9. If documentation and merged green Lean disagree, repair state documentation
   before opening another proof lane.

## Repository truth hierarchy

1. frozen source specification;
2. `docs/V3_COVERAGE_STATUS.md` for counted integrated coverage;
3. `docs/PID_STATUS.yaml` for machine-readable per-lane state;
4. `docs/FORMALIZATION_STATE.md` for human recovery;
5. `UEOT/V3.lean` for official import reachability;
6. `docs/PARALLEL_FORMALIZATION_ROADMAP.md` for execution order.
