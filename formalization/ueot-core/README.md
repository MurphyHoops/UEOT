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

## Start here: current state

Use these files in this order when resuming work:

1. `docs/FORMALIZATION_STATE.md` — live branch / CI / PR / integration state.
2. `docs/V3_COVERAGE_STATUS.md` — authoritative source-level P-ID ledger.
3. `docs/PARALLEL_FORMALIZATION_ROADMAP.md` — forward execution plan.

At the 2026-09-10 synchronized checkpoint the integrated count is
**30 proved / 0 partial / 76 pending** out of 106 source P-IDs.

Do not infer current status from historical counts or stale feature branches.
The official imported module graph is `UEOT/V3.lean`.

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

`main` is the serialized integration branch and the only merged state that
contributes to the source-level coverage ledger.

Independent proof packets may run concurrently on `formal/*` branches. A
green feature branch is candidate evidence, not a proved P-ID, until semantic
audit, merge, and green post-merge main CI are complete.

The current HOT/archive branch map is maintained in
`docs/FORMALIZATION_STATE.md`.
