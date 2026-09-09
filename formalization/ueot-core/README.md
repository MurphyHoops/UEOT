# UEOT Core Lean Formalization

This directory is the machine-checked Lean 4 track for
`UEOT_Core_Mathematics_v3.0_Complete.md`.

## Preservation policy

The repository-level UEOT manuscript, source archives, constitution, and historical
research documents are not replaced by the formalization. Lean sources live under
`formalization/ueot-core/`, and formalization changes should preserve the related
mathematical specifications, coverage ledger, verification reports, and history.

## Current recovered baseline

The latest verified local/session baseline before remote synchronization was:

- mathematical specification: UEOT Core Mathematics v3.0
- Lean package baseline: 0.2.0
- source baseline commit: `fa0106e67d4c4b09fe3cc193019c8eec8c6e05d3`
- Lean: 4.33.1
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- 106 source P-IDs
- 9 `proved`, 7 `partial`, 90 `pending`
- 81 named Lean theorems in the recovered baseline
- no `sorry`, no `sorryAx`, no UEOT-specific proof axioms

This remote subtree is being synchronized incrementally. A theorem is not promoted
from `partial`/`pending` to `proved` until its source statement has been semantically
matched and the corresponding Lean target has passed the build/audit gate.

## Commit discipline

Each independent formalization advance is committed separately. Coverage and
verification documentation must be updated in the same logical advance or in an
immediately following documentation commit; source P-IDs are never deleted merely
to make the completion gate pass.

## Immediate target

The first resumed proof target is `P-RES-05` (exact microscopic uncertainty
interval), whose upward-family interval was already formalized while the finite
clutter / `J^-`, `J^+`, and `pi_*` bridge remained incomplete.
