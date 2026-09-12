# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification. Historical detailed
promotion narratives remain in Git and in `docs/archive/`.

## Verification contract

- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- exact frozen source bytes in public repo: **pending synchronization**

A P-ID is counted as `proved` only after semantic source matching, official
import reachability, feature CI, clean-port CI, PR CI, main integration, green
post-main CI, and ledger synchronization. While the canonical source artifact is
not synchronized into the repository, mathematically complete new P-IDs remain
uncounted until the exact-hash source audit can be executed.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **50** |
| **partial** | **0** |
| **pending** | **56** |
| **total** | **106** |

There are no partial P-IDs. `pending` means only “not yet counted proved”; it
does not imply that no mathematical or Lean proof exists on a feature branch or
on `main`.

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
- **Internal/external factorization:** P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01
- **Representation covariance:** P-FAC-01

Count check: `4 + 6 + 3 + 4 + 9 + 5 + 1 + 2 + 1 + 1 + 2 + 2 + 1 + 2 + 1 + 2 + 1 + 2 + 1 + 1 = 50`.

## Latest counted promotion — P-STAT-06

Frozen source-facing result: for a finite family of Hilbert/RKHS empirical-mean
errors on a common raw sample, the simultaneous failure probability is at most
`alpha` at the exact radius

`(1 + sqrt(2*log(L/alpha))) / sqrt(N)`.

Canonical source-facing theorem:
`UEOT.V3.HilbertMeanSourceFeatureRaw.source_feature_tail_exact_radius_raw_assumptions`.

Verification evidence:

- source-facing feature head: `5a5cb89d600059525cb775c9561aa50d031da38d`
- feature full-target CI run `34684444280`: success
- clean promotion branch: `formal/pstat06-clean-port`
- clean promotion head: `2338d5fe7a5e9ae8a08cdfd469d0eacd35a80205`
- clean-port CI run `34684655595`: success
- PR #40 CI run `34685272294`: success
- integrated main commit: `d17d0e78ec7bf9cd35b1d314afa93aaeecdcb092`
- post-main CI run `34685534516`: success

P-STAT-06 is **closed and counted**.

## Recent promotion evidence

| P-ID | integrated commit | post-main CI |
|---|---|---|
| P-FAC-01 | `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0` | #502 success |
| P-DYN-02 | `8ac668253c4d8bc62ab22f250701bc0a190b6049` | #506 success |
| P-REC-02 | `189fa6b476b0199b321c8d8c2b521f744c0b64ef` | #519 success |
| P-PER-01 | `3d3ecb46416ea156e06fffd70684937f8d94caf3` | #540 success |
| P-ID-01 | `72b0703270df84d5a92f90d5e01c034777ff37dc` | #547 success |
| P-STAT-02 | `5886c7baa4d94936e21dbd5639d7c893af22053` | #563 success |
| P-INFO-01 | `0dd65bc8ae40fdd1afbfdf0cf61c155585a5a2ac` | #572 success |
| P-STAT-05 | `5e5071820a5e30554b23f8344b3315841b0e4b6a` | #584 success |
| P-STAT-01 | `9b3a65ee836e32fa99f6670530e3f7afe72ab070` | #599 success |
| P-STAT-07 | `97533726d71e28b8f4aac1d956db7f65fe98ebda` | #629 success |
| P-STAT-09 | `b21f91f233e7cb65c6f1d6ec928b4870ceee3db4` | #641 success |
| P-STAT-08 | `f03ea2ae9996228d86c742d7f787b95a85ad5898` | #648 success |
| P-INV-01 | `e653401b51594d86f03c317bdd12decae1c27159` | #666 success |
| P-INV-02 | `cbfe8eff494a558f113d2e79136655b9ddb61ca7` | #682 success |
| P-INV-04 | `efd1f529e739aecd4b1331f7324ce5660384cd8c` | #697 success |
| P-INV-03 | `93de8c70353566e806a65afa3f29330cd69da29e` | `34576124342` success |
| P-INV-05 | `7d52e949b9788a32e3c5ce7ab9eec0f4ad85e58d` | `34626175917` success |
| P-STAT-06 | `d17d0e78ec7bf9cd35b1d314afa93aaeecdcb092` | `34685534516` success |

## Integrated but not yet source-counted information work

### P-INFO-02

The source-faithful predictive-TV theorem is mathematically complete and
integrated on `main`:

- canonical theorem: `UEOT.V3.InformationPInfo02.p_info_02_ennreal`;
- all-cases main commit: `c1d0d94b7d01a5d6f370d2de4f40e8c1674bcd8f`;
- post-main CI `34692828935`: success.

It remains outside the proved count solely because the exact frozen source
artifact is not yet synchronized into the repository for the final literal
source/hash audit.

### P-INFO-04 multiway clause

The sharp multiway Fano theorem is also integrated and post-main green:

- canonical theorem: `UEOT.V3.InformationPInfo04.p_info_04`;
- main commit: `94e16dfb9cc9a2db6e000d8f5394c1b07869ce40`;
- post-main CI `34693509298`: success.

P-INFO-04 itself is not countable yet because its frozen contract also contains
a conditional-binary identity-information clause. That remaining clause is the
active proof lane.

## Active unresolved parallel front

- **P-INFO-04 — PROOF:** conditional binary Fano and the finite-binary
  `I(M;B|U)=H(B|U)-H(B|M,U)` bridge remain to close the full P-ID.
- **P-INFO-03 — SOURCE_AUDIT:** extend the same disintegration architecture to
  countable discrete conditional entropy and the random-encoder zero-distortion
  rate-distortion theorem.
- **P-INFO-02 — SOURCE-ARTIFACT BLOCKED:** no further proof work; wait only for
  exact source-byte synchronization and final literal audit.
- **P-INT-01 — BLOCKED:** reuse the canonical conditional-information bridge
  produced by the P-INFO packet; do not build a duplicate stack.

The machine-readable live details are in `docs/PID_STATUS.yaml`.

## Completion rule

UEOT Core v3.0 formalization is complete only when all **106** source P-IDs pass
the full verification contract above.
