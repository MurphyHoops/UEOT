# Path-realization actual execution protocol

Status: **PROTOCOL_SOURCE_PREPARED; ACTUAL_FULL_BUILD_NATIVE_AND_REGISTRATION_PENDING**.
This directory contains an execution protocol, not executed evidence. Preparation
does not create a successful build, native export, registration, or canonical
receipt. The coordinator runs the actual gates after source review and exact-base
authorization; every attempt retains its own original status and bytes.

The seven-module increment follows the accepted `finite_memory_v1` adapter
pattern. It continues to use the immutable drivers under
`longterm_control_statistics_v1/native_protocol/`. Those old files remain
unchanged. The new adapter checks their bytes against the exact Git base and
applies explicitly counted literal substitutions for this increment's names,
census, source identity, archive directory, and metadata provenance.

The scientific role is `UNCOUNTED_SAME_SOURCE_PATH_REALIZATION`. The execution
name is `PATH_REALIZATION`. No proof test, identity check, compiler ownership
check, axiom check, stored-type comparison, compiled dependency check, or
fixed-edge replay is removed or replaced.

Each actual execution archives the complete immutable predecessor script and
the complete adapted Python source actually executed, together with its wrapper,
adapter, frozen inputs, and literal substitution list. The receipt's driver hash
binds the wrapper; the additional protocol archive binds the delegated code.
Registration verifies the exact build and native protocol archives before
planning metadata writes.

## Frozen scope

The predecessor census is **684 modules, 4,272 registered public declarations,
and 10 overlays**. The seven fixed new modules are:

- `C3ExecutableSearch`
- `FiniteMemoryRealization`
- `FiniteMemoryPhysicalSafety`
- `FiniteMemorySafetyWitness`
- `SameSourceFiniteWindow`
- `FiniteWindowDoob`
- `FiniteWindowDoobWitness`

All have prefix `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.`. The
complete source census must be **691 modules**. Public source declaration counts,
the exact public-name set, lexical-hint counts, and the complete source fingerprint
are computed by the unchanged declaration parser and frozen dynamically. They are
not populated from an anticipated result.

Before freezing:

1. Finish and review all seven Lean sources and add their imports to
   `TheoryCompletion.lean`.
2. Integrate the exact accepted operations authorization base; use its commit ID.
3. Preserve every other old Lean source and all prior overlays unchanged.
4. Use a new output location outside the repository for every attempt.

The five executable protocol source files are all included in the manifest. Any
subsequent Lean source or protocol source change invalidates that manifest. Keep
the earlier manifest and execution attempts, then use a new manifest and new
execution directories.

The following path values are examples for the coordinator's isolated Mac
worktree. `UEOT_BASE` must be an exact accepted commit, never a moving branch.

```bash
UEOT_REPO=/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/path-realization-20261022
UEOT_EVIDENCE=/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/path-realization-evidence-20261022
UEOT_BASE=<exact-accepted-operations-base>
UEOT_PROTOCOL=$UEOT_REPO/formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1/native_protocol
UEOT_LAKE=/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake
UEOT_LEAN=/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean
python3 -B "$UEOT_PROTOCOL/freeze_inputs.py" --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" --output "$UEOT_EVIDENCE/FROZEN_INPUTS_FINAL_01.json"
```

The manifest state is explicitly
`FROZEN_SOURCE_ONLY_ACTUAL_BUILD_AND_NATIVE_PENDING`.

## Actual full build and native two-pass execution

```bash
python3 -B "$UEOT_PROTOCOL/full_build.py" --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" --frozen-inputs "$UEOT_EVIDENCE/FROZEN_INPUTS_FINAL_01.json" --output "$UEOT_EVIDENCE/full-build-01" --lake "$UEOT_LAKE" --lean "$UEOT_LEAN"
python3 -B "$UEOT_PROTOCOL/integration_native.py" run --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" --frozen-inputs "$UEOT_EVIDENCE/FROZEN_INPUTS_FINAL_01.json" --output "$UEOT_EVIDENCE/native-01" --build-receipt "$UEOT_EVIDENCE/full-build-01/FULL_BUILD_RECEIPT.json"
```

The complete build is actual `lake build UEOT`. Its receipt binds the exact
691-module source corpus, runtime binaries, environment files, and pinned clean
dependencies before execution, and verifies the same identity afterward.

The native run requires that exact successful build receipt and log. It checks
the full identity before and after each Lean execution. The exporter enumerates
every compiler-owned theorem constant of all seven modules, including private
and generated constants, and rejects nonstandard axioms. Confirmed public source
declarations are compared with all 4,272 previously registered declarations and
pairwise with each other through the established raw stored-type `Meta.isDefEq`
protocol.

The first actual proof-value scan supplies registered direct dependencies. A
second actual Lean execution checks those fixed edges and the complete native
census. The complete JSON exports must agree. Both Lean sources, raw logs, and
complete native exports are preserved. The resulting candidate remains
`PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`.

Raw stored-type comparison is a reuse screen. It does not decide general logical
equivalence or establish semantic novelty. Lexical hints also require independent
mathematical review.

The `prepare` mode may generate an exporter and source preflight in its own new
output directory without running Lean. Its output remains
`PENDING_ACTUAL_NATIVE_EXECUTION` and cannot substitute for an execution receipt.

## Metadata registration

After independent review of source and execution, first run read-only planning
with `--check-only`, then invoke the same command without that option to register
the concrete checked result:

```bash
python3 -B "$UEOT_PROTOCOL/register_overlay.py" --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" --frozen-inputs "$UEOT_EVIDENCE/FROZEN_INPUTS_FINAL_01.json" --native-output "$UEOT_EVIDENCE/native-01" --build-receipt "$UEOT_EVIDENCE/full-build-01/FULL_BUILD_RECEIPT.json" --archive-relative formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1/actual-execution/native-01 --check-only
```

Registration preserves actual input bytes. It adds only `lexical_pr_preflight`
and `registration_provenance` to the raw overlay, creates the eleventh overlay's
new artifacts, and archives the actual full-build/native/registration protocol
sources. It does not edit the live consumer or source DAG. Source, public-name,
count, raw-log, full-native-JSON, protocol-archive, and existing-destination
identity checks precede every write. Existing destinations must be identical.

## Canonical and publication gates

After the separately authorized live consumer and DAG refresh, the existing
canonical command remains:

```bash
python3 -B formalization/ueot-core/docs/compression/theory_completion/unified_closure/audit_umc_local.py --full --output "$UEOT_EVIDENCE/umc-full-01/UMC_FULL_AUDIT.json"
```

Preserve its exact command, raw output, exit status, and elapsed time. This
unchanged audit rebuilds before inspecting all compiler-owned UMC theorem
constants and emits an aggregate census. It does not export its complete internal
per-constant JSON; the seven-module native execution does preserve complete
per-constant records for this increment.

Exact-base authorization, parser tests, live reuse/FKRG checks, Git-object PR
preflight, PR CI, resulting-main verification, and owned-branch retirement remain
separate publication gates. This protocol does not change the frozen 106 P-ID
disposition, four counted generators, or `NOT_ESTABLISHED` global closure status.
