# UEOT Core Lean Formalization

This directory is the machine-checked Lean 4 track for the active
UEOT Core Mathematics v3.0 source specification.

The canonical source identity is registered in
[core/specifications/manifest.yaml](../../core/specifications/manifest.yaml).
The exact v3.0 source file still needs
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

## Start here: current state

The frozen Core v3 source baseline is **106/106 FULL-GREEN**: 106 proved,
0 partial, 0 pending. The authoritative count is maintained in
[V3_COVERAGE_STATUS.md](docs/V3_COVERAGE_STATUS.md). Post-106 Compression and
TheoryCompletion research has separate scientific and integration obligations;
this count does not certify every physical or empirical UEOT claim.

Recover using the existing
[Compression authority hierarchy](docs/compression/COMPRESSION_OPERATIONS.md#1-authority-hierarchy):

1. **Source semantics:** the exact frozen Core v3 statement and assumptions,
   identified by the [canonical source manifest](../../core/specifications/manifest.yaml).
2. **Counted Core baseline:** [V3_COVERAGE_STATUS.md](docs/V3_COVERAGE_STATUS.md)
   on canonical `main`.
3. **Compression scope and counted claims:**
   [COMPRESSION_MISSION.md](docs/compression/COMPRESSION_MISSION.md) controls the
   scientific Definition of Done;
   [COMPRESSION_LEDGER.yaml](docs/compression/COMPRESSION_LEDGER.yaml) controls
   counted compression claims.
4. **Integrated implementation:** canonical
   [main source](https://github.com/MurphyHoops/UEOT/tree/main), the relevant
   [pull requests](https://github.com/MurphyHoops/UEOT/pulls) and
   [Actions/CI](https://github.com/MurphyHoops/UEOT/actions). Match evidence to
   the actual commit before treating a branch or theorem as integrated.
5. **Path and track policy:**
   [COMPRESSION_RESEARCH_TRACKS.json](docs/compression/COMPRESSION_RESEARCH_TRACKS.json)
   and [COMPRESSION_OPERATIONS.md](docs/compression/COMPRESSION_OPERATIONS.md).
6. **Current intent and task recovery:**
   [Issue #146](https://github.com/MurphyHoops/UEOT/issues/146) and its linked
   task trackers. The issue is a recovery index, not authority to promote a
   theorem or override source, ledger or CI evidence.

[PID_STATUS.yaml](docs/PID_STATUS.yaml) and
[FORMALIZATION_STATE.md](docs/FORMALIZATION_STATE.md) are lower-frequency
lifecycle records and historical checkpoints. Their old active-lane fields are
not the current task queue, and the latter's historical “Live” title does not
make it a live PR/CI feed. Consult them for provenance after reconciling the
authorities above.

## Read the integrated theory

- [UEOT.lean](UEOT.lean) and [UEOT/V3.lean](UEOT/V3.lean) expose the official
  imported library; [TheoryCompletion.lean](UEOT/V3/Compression/TheoryCompletion.lean)
  is the integrated entry for its conditional theory and scientific-closure modules.
- [TheoryCompletion mission](docs/compression/theory_completion/THEORY_COMPLETION_MISSION.md)
  and [Unified Closure mission](docs/compression/theory_completion/unified_closure/UNIFIED_CLOSURE_MISSION_V1.md)
  explain the scientific interfaces and their remaining assumptions.
- [FKRG reading/search entry](docs/compression/theory_completion/knowledge/README.md)
  and [proof-reuse evidence](docs/compression/theory_completion/knowledge/reuse/README.md)
  locate existing declarations and compiled reuse evidence before new proof work.
- [ScientificClosure status](docs/compression/theory_completion/scientific_closure/SCIENTIFIC_CLOSURE_STATUS.json)
  distinguishes method-package completion, independent review and external
  scientific support. A Lean build or merged PR does not collapse these gates.

## Recovered historical checkpoints

Before public-repository synchronization, the verified v3 package baseline was:

- source baseline commit: `fa0106e67d4c4b09fe3cc193019c8eec8c6e05d3`
- 106 source P-IDs: 9 `proved`, 7 `partial`, 90 `pending`
- 81 named Lean theorems
- no `sorry`, no `sorryAx`, no UEOT-specific proof axioms

The later 2026-09-12 checkpoint had 50 counted proved and 56 pending, with
P-INFO-02 recorded as the active proof lane. Both checkpoints are historical;
neither describes the current 106/106 baseline or current research assignment.
Historical `pending` means “not yet counted proved” at that checkpoint, not a
present-day missing-proof obligation.

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

1. reconcile the current task, branch and evidence using the recovery order above;
2. audit the relevant frozen source statement and current research contract;
3. inspect the existing integrated theorem stack and reuse candidates;
4. prove only the identified missing obligation within the task's registered scope.

Do not reopen a counted P-ID or add another helper/wrapper because a historical
snapshot says `pending`. For post-106 work, use the existing
[minimal preflight](docs/compression/COMPRESSION_OPERATIONS.md#4-minimal-preflight)
and reuse the active branch when it already owns the objective.

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
documented in [docs/PROJECT_ARCHITECTURE.md](../../docs/PROJECT_ARCHITECTURE.md).

## Branch policy

`main` is the serialized integration branch and the only merged state that
contributes to the source-level coverage ledger.

Core proof packet procedures are recorded in
[UEOT_CORE3_LEAN_OPERATIONS.md](docs/UEOT_CORE3_LEAN_OPERATIONS.md). Post-106
research uses the registered branches in the
[Compression branch model](docs/compression/COMPRESSION_OPERATIONS.md#3-branch-model).
A green feature branch is candidate evidence; source/count promotions and
scientific claims still require their respective audited gates.
