# UEOT Core Lean Formalization

This directory is the machine-checked Lean 4 track for the active
UEOT Core Mathematics v3.0 source specification.

The canonical source identity is registered in
[core/specifications/manifest.yaml](../../core/specifications/manifest.yaml).
The exact [v3.0 source](../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md)
is synchronized byte for byte with the registered SHA-256. The current-main
bytes were rechecked on 2026-11-11; the earlier pending-synchronization notes
remain historical checkpoints. A regenerated substitute, chat summary or stale
roadmap is never a source replacement. The 106 P-ID proof contracts are unchanged.

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

Read [current Core status](../../core/status/CURRENT.md) first. It separates the
frozen 106 contracts, whole conditional mathematical closure, the same-source
definitive theory, PR #446's written supplements and PR #447's completed growth
extension. Content remains **CLASSIFIED_CORE_CLOSED** and empirical support
**UNVERIFIED**. A completed contract is not reopened by an old roadmap.

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
   source-bound local validation receipts. Historical [Actions/CI](https://github.com/MurphyHoops/UEOT/actions)
   remain evidence for their own commits. Match evidence to actual source bytes
   before treating a branch or theorem as integrated; current Core verification
   follows the repository's local-validation policy.
5. **Path and track policy:**
   [COMPRESSION_RESEARCH_TRACKS.json](docs/compression/COMPRESSION_RESEARCH_TRACKS.json)
   and [COMPRESSION_OPERATIONS.md](docs/compression/COMPRESSION_OPERATIONS.md).
6. **Current intent and task recovery:** begin with the current user task,
   [Core state](../../core/status/CURRENT.md), actual main and open branches/PRs.
   [Issue #146](https://github.com/MurphyHoops/UEOT/issues/146) and its linked
   trackers are recovery indexes; reconcile their dates with later adopted
   contracts. An issue cannot promote a theorem or override source and evidence.

[FORMALIZATION_STATE.md](docs/FORMALIZATION_STATE.md) identifies the current
layers and preserves its earlier checkpoint. [PID_STATUS.yaml](docs/PID_STATUS.yaml)
is the frozen source-lifecycle record; old active-lane fields are historical,
not a current queue. Consult them for provenance after reconciling the
authorities above.

## Read the integrated theory

- [UEOT.lean](UEOT.lean) imports [Compression](UEOT/V3/Compression.lean), then
  [TheoryCompletion](UEOT/V3/Compression/TheoryCompletion.lean) and
  [CoreTheoryClosure](UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreTheoryClosure.lean).
  This route exports the original 13 definitive-theory modules and the three
  PR #447 growth modules. [UEOT/V3.lean](UEOT/V3.lean) remains an older subset;
  it does not alone export that family.
- [Same-source definitive theory](docs/compression/theory_completion/unified_closure/core_theory_closure_v1/README.md)
  and [growth/attainment classification](docs/compression/theory_completion/unified_closure/core_growth_classification_v1/README.md)
  provide current claims, actual consumers and their distinct validation receipts.
- [TheoryCompletion mission](docs/compression/theory_completion/THEORY_COMPLETION_MISSION.md)
  and [Unified Closure mission](docs/compression/theory_completion/unified_closure/UNIFIED_CLOSURE_MISSION_V1.md)
  preserve the original scientific contracts and assumptions. Their initial
  stage statuses and immediate-objective paragraphs are historical; use the
  current contract map before scheduling work.
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

## Proof-status and validation scope

The original 106 source P-IDs are already frozen FULL-GREEN. Their historical
promotion gates and no-proof-bypass requirements remain in the
[coverage ledger](docs/V3_COVERAGE_STATUS.md) and
[original source operations](docs/UEOT_CORE3_LEAN_OPERATIONS.md). This status
refresh does not promote a P-ID, change counted semantics or recreate old CI events.

For a current change:

1. identify its exact source statement, assumptions, reused endpoints and actual
   missing obligation;
2. expose new production results through the appropriate public target and
   check semantic correspondence, proof trust and the affected consumer;
3. record actual local commands, source identity, toolchain, exit status and
   necessary axiom checks, following the applicable task and governance scope;
4. review and merge one coherent candidate, then verify resulting-main adoption;
5. reuse still-applicable evidence for unchanged sources; documentation-only
   changes verify content, references and protected-byte preservation.

The [current local-validation policy](../../docs/REPOSITORY_BRANCH_GOVERNANCE.md#11-ci-efficiency-rules)
does not require repeated cloud builds for ordinary maintenance. No absent run
is recorded as a successful run. Frozen/counting changes still require their
own original promotion lifecycle; this paragraph does not weaken those gates.
Helpers and isolated green files do not increment source coverage.

Trust is attached to exact endpoints: PR #447's 15 audited endpoints use the
standard three axioms; this does not erase PR #443's disclosed numerical trust.
The PR #446 2/3/4 classification and concrete rank-three supplement remain
written proof plus exact checks, rather than new complete dedicated Lean endpoints.

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

Use commits for meaningful, reviewable stages and one PR for a coherent objective.
Theorem, repair and integration changes do not each require a new branch or
duplicated full regression. Publish status only after the corresponding checks;
retain failed attempts and original receipts as historical evidence. See the
[current workstream guidance](../../docs/FORMALIZATION_WORKSTREAMS.md).

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

## Licensing note

The present repository policy update does **not** by itself relicense
this Lean code to Apache-2.0. Existing historical grants, any imported
code notices and contributor rights require review before a new code license
is issued. See [license scope](../../LICENSE_SCOPE.md).
