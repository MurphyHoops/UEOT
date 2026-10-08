# SISC C7/SQLITE-METHOD-01 — Frozen Method-Pilot Recomputability Audit

Status: **LOCAL METHOD PASS / INDEPENDENT REVIEW PENDING / EXTERNAL SUPPORT UNVERIFIED**.
Pre-collection registration+runner+verifier commit: `ff309603`.
The producer ran that already committed implementation **once**; it created
new `events.jsonl` and `manifest.json` in a non-overwriting output folder.

## Evidence inventory

- Protocol: `SISC_C7_SQLITE_METHOD_PREREG.md`, no changed criteria after data.
- Raw evidence: `evidence/c7_sisc_sqlite_method_v1/events.jsonl`.
- Raw SHA-256: `7484c8212c5aba6ad076d4359aa6c467ea3063f339400405211a5739052ff9d5`.
- Registered order: exactly five rows `INITIAL,COPY,RENAME,UPDATE,COMPLETE`.
- New method output: `PASS_METHOD`, recomputed with separately authored
  `sisc_c7_sqlite_verify.py`, **not** from terminal producer flags alone.
- Safety: all SQLite writes to a fresh private temporary database, no
  production service, no destructive external infrastructure operation.

## What the measurements support

The SQLite engine produced same-query clone files with different OS inode
provenance; an on-filesystem rename preserved inode provenance; subsequent
intervention on the moved original changed only that file, not the copy.
The experiment therefore provides a concrete *digital method witness* that
same declared responses may coexist with independent physical carrier
histories, while an externally instrumented operation distinguishes them.

The experiment is **not** a data-driven classification of ontological
`SameObject`. Inode provenance is a distinct measurable physical carrier
property; it is not the universal semantics of identity.

## Mutational negative controls

The added test works exclusively on disposable temporary copies of the raw:

1. unmanifested tampering → `UNRESOLVED`;
2. missing registered UPDATE with recomputed manifest → `UNRESOLVED`;
3. coherent COPY contradiction with matching manifest and terminal report →
   `REJECTED_METHOD`.

No failed run is silently discarded, and no original archived byte is
rewritten. The self-authored test/verifier cannot claim independent collection,
independent third-party analysis, external validity of UEOT or generic FBT
defect calibration. The registered experiment's fixed response/copy operations
do not provide quantitative `epsF, epsB, L` for natural systems.

## Required next gate (UNSATISFIED)

Select an external operator-controlled resettable service or physical system,
freeze independent causal/protocol/identity responses and error budget,
independently collect and authenticate **all** attempted runs, independently
recompute without trusting the producer, and hold out interventions and
negative controls. Until then `independent_review=REVIEW_PENDING`,
`real_world_support=UNVERIFIED`, and **SI-5 remains OPEN**.
