# UEOT Core Lean Formalization

This directory is the machine-checked Lean 4 track for the active
UEOT Core Mathematics v3.0 source specification.

The canonical source identity is registered in
`core/specifications/manifest.yaml`. The exact v3.0 source file still needs
byte-for-byte synchronization into the public repository; no regenerated
substitute is treated as canonical. Until that synchronization is completed,
source-facing promotion must preserve the registered source hash and the audited
P-ID proof contract; a chat summary or stale roadmap is never a source substitute.

## Role in the repository

The formalization is an epistemic verification layer:

```text
core specification
      ↓ semantic matching / proof contract
Lean formal statement
      ↓ pinned kernel build
machine-checked theorem
      ↓ promotion gate
source P-ID status
```

A Lean theorem does not replace the source specification, and a green build does
not automatically promote a natural-language claim.

## Toolchain

- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Lake dependency graph: `lake-manifest.json`
- official library target: `UEOT`
- serialized integration branch: `main`

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

This section is historical only. Historical theorem counts are not completion
percentages and must never be used as the current project state.

## Start here: current state

Resume work in this order:

1. `docs/PID_STATUS.yaml` — machine-readable per-P-ID state and proof contracts;
2. `docs/FORMALIZATION_STATE.md` — live branch / CI / PR / integration state;
3. `docs/V3_COVERAGE_STATUS.md` — authoritative **counted** source-level ledger;
4. `docs/PARALLEL_FORMALIZATION_ROADMAP.md` — forward execution plan;
5. `UEOT/V3.lean` — official imported module graph.

At the 2026-09-12 synchronized checkpoint the source-level coverage is:

- **50 proved**;
- **0 partial**;
- **56 pending**;
- **106 total**.

`pending` means only “not yet counted proved”. It does **not** mean “the
mathematics has not been proved”. Consult `PID_STATUS.yaml` to distinguish
`source_audit`, `proof`, `integration`, `promotion`, `blocked`, `proved`, and
`archive` before opening a Lean proof lane.

P-STAT-06 is closed and counted. The active proof lane is P-INFO-02; P-INFO-03
and P-INFO-04 are source-audit lanes; P-INT-01 is blocked on the canonical
conditional-information interface.

## Proof-status gate

A source P-ID can be promoted to `proved` only when all of the following hold:

1. the exact frozen source statement and assumptions are identified;
2. an explicit proof contract records existing reusable theorems and the actual
   missing obligations;
3. the Lean theorem is semantically source-faithful, or a source correction is
   explicitly audited;
4. the theorem is reachable from `UEOT` / `UEOT.V3`;
5. feature full-target CI is green;
6. a minimal clean port is made onto the newest green Lean-affecting `main`;
7. clean-port CI and PR CI are green;
8. the change is serialized into `main`;
9. post-main `lake build UEOT` is green;
10. no `sorry`, UEOT-specific proof axiom, `native_decide`, or hidden weakening
    has been introduced;
11. the source ledger and machine-readable state are synchronized.

Helpers and isolated green files do not increment source coverage.

## Anti-churn rule

Before writing Lean:

1. read `PID_STATUS.yaml`;
2. audit the frozen source-facing statement;
3. audit the existing integrated theorem stack;
4. prove only the listed missing obligations.

Do not add another helper/wrapper merely because the coverage ledger still says
`pending`. If a P-ID is in `promotion`, CI waiting time belongs to a different
proof/audit lane; repeated CI polling is not formalization progress.

## Commit discipline

Each independent proof advance is committed separately:

1. theorem/definition commit;
2. repair commit(s), if CI exposes actual errors;
3. source-facing theorem/integration commit;
4. proof-status documentation only after successful verification.

Failed intermediate CI runs and repair commits are retained as audit evidence.

## Repository preservation

The formalization does not replace the manuscript, historical theory documents,
physics research, or validation artifacts. The repository-wide architecture is
documented in `docs/PROJECT_ARCHITECTURE.md`.

## Branch policy

`main` is the serialized integration branch and the only merged state that
contributes to the source-level coverage ledger.

Independent proof packets may run concurrently on `formal/*` branches. A green
feature branch is candidate evidence, not a proved P-ID, until semantic audit,
merge, and green post-main CI are complete.
