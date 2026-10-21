# Finite-memory actual execution protocol

Status: **ACTUAL_FULL_BUILD_AND_NATIVE_VERIFIED; METADATA_REGISTERED**. The
[full build](../actual-execution/full-build-01/FULL_BUILD_RECEIPT.json),
[native execution](../actual-execution/native-01/STATUS.json),
[independent execution review](../independent/ACTUAL_BUILD_NATIVE_REVIEW.md), and
[metadata registration](../actual-execution/native-01/REGISTRATION_RECEIPT.json)
record the actual outcomes. Each raw receipt retains its original state;
this protocol note does not rewrite it. Canonical publication is a separate gate.

The six-module increment reuses the accepted predecessor execution machinery.
The old files remain unchanged. `protocol_adapter.py` checks their current
bytes against the exact Git base and executes a recorded version with explicitly
counted literal substitutions for this increment's name, census, frozen source,
archive location and metadata provenance. It does not replace any proof,
source/runtime identity check, native ownership check, axiom test, raw-type
comparison, compiled dependency check, or fixed-edge replay.

Each execution archives the complete immutable predecessor script and the
complete adapted Python source actually executed, together with its wrapper,
adapter, frozen inputs and substitution list. The receipt's driver hash binds
the wrapper; the additional protocol archive binds the code it delegates to.
Registration verifies those exact protocol archives before planning writes.

## Frozen inputs

Before running this protocol:

- Finish the six Lean sources and add their imports to `TheoryCompletion.lean`.
- Rebase or merge onto the exact accepted operations authorization base.
- Preserve all other old Lean sources and all previous overlays unchanged.
- Use a new output location outside the repository for every attempt.

The fixed predecessor is 678 modules, 4,237 registered public declarations,
and nine overlays. The new six module names are fixed in the adapter. Public
declaration and lexical-hint counts are computed from the immutable declaration
parser and frozen together with the entire 684-module source fingerprint.
The manifest is explicitly source-only and pending actual execution.

The following commands use shell variables only to keep the paths readable.
`UEOT_BASE` must be an exact commit, not a moving branch name.

```bash
UEOT_REPO=/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/finite-memory-20261022
UEOT_EVIDENCE=/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/finite-memory-evidence-20261022
UEOT_BASE=<exact-accepted-operations-base>
UEOT_PROTOCOL=$UEOT_REPO/formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/native_protocol
UEOT_LAKE=/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake
UEOT_LEAN=/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean
python3 -B "$UEOT_PROTOCOL/freeze_inputs.py" --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" --output "$UEOT_EVIDENCE/FROZEN_INPUTS_FINAL_01.json"
```

Any later source or execution-protocol change invalidates this manifest. Use a
new manifest and new execution directories; retain the old attempts verbatim.

## Actual complete build and native export

```bash
python3 -B "$UEOT_PROTOCOL/full_build.py" --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" --frozen-inputs "$UEOT_EVIDENCE/FROZEN_INPUTS_FINAL_01.json" --output "$UEOT_EVIDENCE/full-build-01" --lake "$UEOT_LAKE" --lean "$UEOT_LEAN"
python3 -B "$UEOT_PROTOCOL/integration_native.py" run --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" --frozen-inputs "$UEOT_EVIDENCE/FROZEN_INPUTS_FINAL_01.json" --output "$UEOT_EVIDENCE/native-01" --build-receipt "$UEOT_EVIDENCE/full-build-01/FULL_BUILD_RECEIPT.json"
```

The full build is actual `lake build UEOT`. Its receipt captures every source
file, runtime binaries, environment files and pinned clean dependencies before
the build and verifies the identity again afterward.

The native run requires that exact successful full-build receipt and log. It
checks the same identity before and after each Lean execution. Its exporter
enumerates every compiler-owned theorem constant in the six new modules,
including private and generated constants, and rejects nonstandard axioms.
Confirmed public source declarations are compared against all 4,237 previously
registered declarations and pairwise against each other using the established
raw stored-type `Meta.isDefEq` protocol.

The first actual proof-value scan supplies direct registered dependencies. A
second actual Lean execution checks those fixed edges and complete native
census. The complete JSON exports must agree. Both source files, raw logs and
exports are preserved. The resulting candidate status intentionally remains
`PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`.

The raw stored-type comparison is a reuse screening tool. It does not decide
general logical equivalence or establish semantic novelty. Lexical hints still
require independent mathematical review.

`integration_native.py prepare` can generate an exporter and source preflight
without running Lean, using a separate new output directory. Its output remains
`PENDING_ACTUAL_NATIVE_EXECUTION` and cannot serve as a native receipt.

## Metadata registration

Run the read-only planning mode first, then the same command without
`--check-only` after source/execution review. Registration consumes actual
outputs and preserves their bytes. It adds only `lexical_pr_preflight` and
`registration_provenance` to the raw overlay and creates the tenth overlay's
new files. It does not edit the live consumer or the source DAG.

```bash
python3 -B "$UEOT_PROTOCOL/register_overlay.py" --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" --frozen-inputs "$UEOT_EVIDENCE/FROZEN_INPUTS_FINAL_01.json" --native-output "$UEOT_EVIDENCE/native-01" --build-receipt "$UEOT_EVIDENCE/full-build-01/FULL_BUILD_RECEIPT.json" --archive-relative formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/actual-execution/native-01 --check-only
```

All current source bytes, source/public/count identities, actual logs, complete
native JSON, protocol archives and existing destination bytes are checked
before any registration write. Existing destinations must be identical.

## Whole-UMC audit and publication

After the separately authorized live consumer and DAG refresh, use the existing
canonical command from the repository root:

```bash
python3 -B formalization/ueot-core/docs/compression/theory_completion/unified_closure/audit_umc_local.py --full --output "$UEOT_EVIDENCE/umc-full-01/UMC_FULL_AUDIT.json"
```

Preserve its exact command, raw output, actual exit status and elapsed time.
This unchanged audit rebuilds before inspecting all compiler-owned UMC theorem
constants and emits an aggregate census. It does not export its full internal
per-constant JSON; the six-module native export above does preserve complete
per-constant records for the added increment.

Immutable-base authorization, parser tests, live reuse/FKRG checks, Git-object
PR preflight, PR CI, resulting-main verification and owned-branch retirement
remain separate publication gates. No protocol action changes the frozen
106 P-ID disposition, the four counted generators, or global closure status.
