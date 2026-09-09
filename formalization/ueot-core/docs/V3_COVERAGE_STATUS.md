# UEOT Core v3.0 Lean Coverage Status

This document records the source-level P-ID coverage state separately from the
subset of Lean modules currently synchronized into this public repository.

The mathematical source of truth remains
`UEOT_Core_Mathematics_v3.0_Complete.md` with 106 P-IDs. Historical verification
documents and earlier package states are preserved; no P-ID is deleted or
downgraded merely to simplify the completion gate.

## Recovered baseline before remote synchronization

The verified 2026-09-06 baseline contained:

- 9 proved
- 7 partial
- 90 pending
- 106 total P-IDs
- 81 named Lean theorems
- no `sorry`, no `sorryAx`, no UEOT-specific proof axioms

The proved P-IDs were:

- P-CAR-01
- P-CAR-02
- P-CAR-03
- P-RES-03
- P-RES-04
- P-STAT-03
- P-STAT-04
- P-QUO-03
- P-REF-04

The partial P-IDs were:

- P-PRED-01
- P-PRED-02
- P-DYN-01
- P-RES-05
- P-TEL-01
- P-BRG-02
- P-REF-05

## 2026-09-09 advance: P-RES-05

P-RES-05 has been promoted from `partial` to `proved`.

The source statement is the exact microscopic-realization interval

[
\pi_*\mathcal C=\mathcal D
\iff
\uparrow J^-_\pi(\mathcal D)
\subseteq\uparrow\mathcal C
\subseteq\uparrow J^+_\pi(\mathcal D).
]

The resumed Lean track now contains:

- `UEOT.V3.Resolution.UpClosure`
- `UEOT.V3.Resolution.IsAntichain`
- `UEOT.V3.Resolution.PushMin`
- `UEOT.V3.Resolution.imageFamily`
- `UEOT.V3.Resolution.MinimalFamily`
- `UEOT.V3.Resolution.pushFamily`
- `UEOT.V3.Resolution.restrict_upClosure_iff_pushMin`
- `UEOT.V3.Resolution.pushFamily_eq_iff_pushMin`
- `UEOT.V3.Resolution.clutter_realization_interval`
- `UEOT.V3.Resolution.pushFamily_realization_interval`

Here `pushFamily π C` literally encodes the inclusion-minimal members of
`{π '' c | c ∈ C}`, i.e. the source definition of `π_* C`.  The proof uses
finiteness only to obtain a minimal image below each image, and antichain
minimality to force the exact coarse edge.

### Verification evidence

- finite-clutter interval bridge commit:
  `b65ad3e54397927f0aa563a246abf5766404a38b`
- literal `π_*` / minimal-image bridge commit:
  `fa3161688cb1248cee0d1cc1f938893c298ac206`
- GitHub Actions run for `fa316168...`:
  `34336212073`
- result: pinned Lean verified, dependencies resolved, `lake build UEOT` passed.

## Current source-level coverage

| Status | Count |
|---|---:|
| proved | 15 |
| partial | 5 |
| pending | 86 |
| total | 106 |

The five remaining partial P-IDs are:

- P-PRED-02
- P-DYN-01
- P-TEL-01
- P-BRG-02
- P-REF-05

The newly proved set is the previous nine plus **P-RES-05**, **P-RES-06**, **P-CAR-04**, **P-RES-02**, and **P-RES-01**.

## 2026-09-09 advance: P-PRED-01

P-PRED-01 has been promoted from `partial` to `proved`.

The exact source permits a countable protocol family with protocol-dependent
future spaces. The current formalization therefore includes both the original
common-codomain layer and the stronger source-matched dependent layer.

Key declarations:

- `UEOT.V3.PredictionAE.common_factorization`
- `UEOT.V3.PredictionAE.canonical_ae_minimal`
- `UEOT.V3.PredictionAE.canonical_ae_sigma_minimal`
- `UEOT.V3.PredictionAE.canonical_kernel_sufficient`
- `UEOT.V3.PredictionAE.canonical_event_condExp`
- `UEOT.V3.PredictionDependent.common_factorization`
- `UEOT.V3.PredictionDependent.canonical_ae_sigma_minimal`
- `UEOT.V3.PredictionDependent.canonical_kernel_sufficient`
- `UEOT.V3.PredictionDependent.canonical_event_condExp`

The source assumes standard-Borel statistic/future spaces. Once the measurable
response kernels are supplied, the Lean factorization theorem only uses the
measurable-space structure, so the formal result is more general at this stage;
it does not claim existence of regular conditional probabilities without the
source hypotheses.

Verification evidence:

- AE factor/minimality work: `b3f7faea...`, `794d1aeb...`
- measurable-space repair: `eb4b6440...`, CI run `34341861473` success
- canonical coordinate kernel: `860193ba...`, run `34342312233` success
- conditional-expectation layer: `986babdd...`
- sigma-notation repair: `9d7b118a...`, run `34342707993` success
- dependent-future-space closure: `d6ac5874...`, run `34343117149`,
  full `lake build UEOT` success (8724 jobs)

The two failed intermediate runs are retained as audit history and were not used
as proof evidence.

## 2026-09-09 advance: P-RES-01

P-RES-01 has been promoted from `pending` to `proved`.

Source statement:

[
\mathcal M_r=
\min_{\subseteq}\{\operatorname{cl}_r(M):M\in\mathcal M_s\}.
]

Lean theorem:

- `UEOT.V3.ClosureResolution.minimal_property_coarse_graining`

Definitions:

- `admissibleMin L A = min(A ∩ L)`
- `resolutionMap L M = min{closure L M | M ∈ M}`

The proof assumes upward closure of the admissible property and explicit
finiteness of the fine admissible family. The source works over a finite carrier,
so this is the source-relevant minimal-existence assumption rather than a new
physical/mathematical restriction.

Verification evidence:

- theorem commit: `09196536122e5976161dbfc5db04f3d0c86731fa`
- successful official-target CI run: `34339206795`

With this promotion, P-RES-01 through P-RES-06 are all source-matched as
`proved`.

## 2026-09-09 advance: P-RES-02

P-RES-02 has been promoted from `pending` to `proved`.

The source has two composition statements:

[
\operatorname{cl}_r\operatorname{cl}_s=\operatorname{cl}_r
]

for nested closure systems, and

[
\mathcal R_{r\leftarrow t}
=
\mathcal R_{r\leftarrow s}\mathcal R_{s\leftarrow t}
]

for minimal families.

Lean module `UEOT.V3.ClosureResolution` now contains:

- `ClosureSystem`
- `closure`
- `closure_comp_of_nested`
- `imageClosure`
- `resolutionMap`
- `minimalFamily_cofinal`
- `resolutionMap_comp`

The formal closure system is represented as a Moore family. On the finite
carrier of the source specification this is equivalent to closure under finite
intersections. The minimal-family theorem assumes the source-relevant finiteness
of the input family and is stronger than the written three-scale form because
the top-scale family need not be separately declared closed.

Verification evidence:

- operator theorem commit: `703bd7972318e440d9c23230729cbde5dba09846`
- syntax repair: `849ca9d470197cedf9a8fd1adedb8b141a8568a7`
- minimal-family theorem commit: `386086c234aeb2adedd8ef0b2083c977e88cdbf2`
- successful CI run for the complete module: `34338838686`

The failed intermediate run is retained and was caused by using the
`Set.mem_sInter` equivalence as a tactic without first unfolding `closure`.

## 2026-09-09 advance: P-CAR-04

P-CAR-04 has been promoted from `pending` to `proved`.

Source statement:

[
\tfrac12 e(S) \le r(S) \le e(S).
]

The Lean module `UEOT.V3.DecoderRadius` proves the metric theorem in a more
general pseudometric setting. `FiberDistances` is the set of all response
distances inside one readout fiber and `DecoderBounds` is the set of all
uniform decoder error bounds. If `e` is their least upper bound and `r` is
the greatest lower bound of decoder bounds, Lean proves

- `diameter_half_le_decoder_radius`
- `decoder_radius_le_diameter`
- `decoder_radius_bounds`

The source TV-distance result is the direct specialization of this metric
argument. No attainment assumption for the decoder infimum is added.

Verification evidence:

- theorem commit: `8115eb3f38c71d9f5b7027e1939448c9d88f408f`
- official-target import commit: `ac5b6db04924db2d52b521ad97c60fba2351f8aa`
- successful CI run after official import: `34337696868`

The earlier green run for `8115eb3f...` is not used as proof evidence because
the new module had not yet been imported by the default `UEOT` target. This
verification gap was detected and repaired before status promotion.

## 2026-09-09 advance: P-RES-06

P-RES-06 has been promoted from `pending` to `proved`.

Lean theorem:

- `UEOT.V3.Resolution.endpoint_equality_iff_unique_active_fibers`

The source fiber-cardinality condition `|π⁻¹(w)| = 1` is represented by
`UniqueFiber π w`: an inhabitant of the fiber exists and every other
inhabitant is equal to it. `Active D w` means that `w` occurs in some coarse
minimal edge. Under surjectivity of `π` and antichain minimality of `D`, Lean
proves that the lower and upper realization endpoints coincide exactly when
every active fiber is unique.

Verification evidence:

- theorem commit: `430202b81bedae8bfb10a0778f9e6071c2080fb5`
- equality-transport repair: `9baa0b95892293167cf212d4875138da4f665a46`
- successful locked/cache CI run: `34337047643`

The failed intermediate run is intentionally retained in Git history; it
reported three equality-transport type errors and led to the repair commit.

## Synchronization note

Only a subset of the earlier 16-module Lean package has been restored to the
public repository so far. Therefore the source-level coverage table above must
not be confused with “number of modules currently present on GitHub.” The
remaining verified historical modules and their documentation will be restored
incrementally without replacing the UEOT manuscript/research materials already
in the repository.

## Completion rule

The complete v3.0 formalization is not finished until all 106 source P-IDs have
been semantically matched and machine-checked. A green build proves the Lean
statements currently imported; it does not by itself prove that every natural
language source statement has been covered.
