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
| proved | 11 |
| partial | 6 |
| pending | 89 |
| total | 106 |

The six remaining partial P-IDs are:

- P-PRED-01
- P-PRED-02
- P-DYN-01
- P-TEL-01
- P-BRG-02
- P-REF-05

The newly proved set is the previous nine plus **P-RES-05** and **P-RES-06**.

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
