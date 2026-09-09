# UEOT Core Lean Formalization

This directory is the machine-checked Lean 4 track for the active
UEOT Core Mathematics v3.0 source specification.

The canonical source identity is registered in
`core/specifications/manifest.yaml`. The exact v3.0 source file still needs
byte-for-byte synchronization into the public repository; no regenerated
substitute is treated as canonical.

## Role in the repository

The formalization is an epistemic verification layer:

```text
core specification
      ↓ semantic matching
Lean formal statement
      ↓ pinned kernel build
machine-checked theorem
      ↓ coverage promotion
source P-ID status
```

A Lean theorem does not replace the source specification, and a green build does
not automatically promote a natural-language claim.

## Toolchain

- Lean: 4.33.1
- Mathlib:
  `0df444a360eaa60ab8c11dca51a86af692955474`
- Lake dependency graph preserved in `lake-manifest.json`
- default library target: `UEOT`

All official theorem modules must be imported by an official build target.
A module that merely exists on disk is not accepted as verified evidence.

## Recovered historical baseline

Before public-repository synchronization, the verified v3 package baseline was:

- source baseline commit: `fa0106e67d4c4b09fe3cc193019c8eec8c6e05d3`
- 106 source P-IDs
- 9 `proved`
- 7 `partial`
- 90 `pending`
- 81 named Lean theorems
- no `sorry`, no `sorryAx`, no UEOT-specific proof axioms

Historical theorem count is not a completion percentage.

## Current source-level status

The authoritative current ledger is:

- `docs/V3_COVERAGE_STATUS.md`

As of the completed P-RES-02 promotion:

- 14 `proved`
- 6 `partial`
- 86 `pending`
- 106 total source P-IDs

Newly completed since the recovered baseline include:

- P-CAR-04 — decoder-radius / fiber-diameter inequality
- P-RES-01 — coarse-graining of minimal admissible properties
- P-RES-02 — closure and minimal-family resolution composition
- P-RES-05 — exact microscopic realization interval
- P-RES-06 — object-relative uniqueness from active fibers

The complete P-RES-01..06 resolution block is now source-matched as proved.
The next priority is restoration of the previously verified package modules, followed by closure of the remaining six partial P-IDs.

## Current synchronized modules

The public package currently includes the resumed resolution/decoder layer and
is still a subset of the previously verified 16-module package.

Important current modules include:

- `UEOT/Core/Resolution.lean`
- `UEOT/V3/Resolution.lean`
- `UEOT/V3/DecoderRadius.lean`
- `UEOT/V3/ClosureResolution.lean`

Previously verified prediction, dynamics, access, blocker, threshold, decision,
reward, and boundary-case modules still need full restoration from the
historical package.

## Proof-status gate

A source P-ID can be promoted to `proved` only when:

1. the exact source statement is identified;
2. the Lean statement is semantically matched;
3. the theorem is imported into an official target;
4. the pinned build passes;
5. no prohibited proof holes or UEOT-specific axioms are introduced;
6. the coverage ledger is updated.

`partial` is used when a strict subset or weaker form is proved.
`pending` is never removed simply to make the completion gate pass.

## Commit discipline

Each independent proof advance is committed separately.

Typical sequence:

1. theorem/definition commit;
2. repair commit(s), if CI exposes errors;
3. proof-status documentation commit only after successful verification.

Failed intermediate CI runs and repair commits are retained as audit evidence.

## Repository preservation

The formalization does not replace the manuscript, historical theory documents,
physics research, or validation artifacts. The repository-wide architecture is
documented in `docs/PROJECT_ARCHITECTURE.md`.

## Branch policy

Active development is committed to `main`.

GitHub still reports `master` as the repository default-branch setting. No
independent formalization development is maintained on `master`; changing the
repository default-branch setting remains an administrative follow-up.
