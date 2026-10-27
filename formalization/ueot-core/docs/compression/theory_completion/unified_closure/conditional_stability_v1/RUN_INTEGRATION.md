# Conditional stability: production integration

The five files under `native_protocol/` implement the frozen production
protocol. The accompanying `prepare_consumers.py` prepares and applies the
six authorized evidence consumers. Actual execution receipts are under
`actual-execution/`; the commands below describe a fresh reproduction.
Use new output directories and preserve all earlier execution records.

The immutable execution implementation remains
`longterm_control_statistics_v1/native_protocol/{full_build,integration_native,register_overlay}.py`.
The adapter retains the full source/runtime identity checks, real full build,
complete native ownership and axiom census, cross-registry and internal raw-type
comparisons, initial/fixed export equality, exact proof-edge replay, and raw-byte
registration checks. Its scope substitutions are archived beside both original
and executed driver bytes. It changes the layer name, the known predecessor
census `701 / 4463 / 15`, the two-module scope, and the new census `703`.
The public declaration count, lexical hints and source fingerprint come from
the actual freeze. No public count is preset.

## Parameters

Run from the existing Mac worktree using Python 3.11 or later. Set these once:

```bash
UEOT_REPO='/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/total-kernel-memory-20261023'
UEOT_CORE="$UEOT_REPO/formalization/ueot-core"
UEOT_PACKET='formalization/ueot-core/docs/compression/theory_completion/unified_closure'
UEOT_PROTOCOL="$UEOT_REPO/$UEOT_PACKET/conditional_stability_v1/native_protocol"
UEOT_REUSE="$UEOT_CORE/docs/compression/theory_completion/knowledge/reuse"
UEOT_RUN='/tmp/ueot-conditional-stability-reproduction-20261028'
UEOT_ARCHIVE="$UEOT_PACKET/conditional_stability_v1/reproduction/native-final"
UEOT_PREPARER="$UEOT_REPO/$UEOT_PACKET/conditional_stability_v1/prepare_consumers.py"
```

The original execution used base `7708a3a1289b1a009c269d81edceef06a4c347dc`,
actual Lake and Lean executables under
`/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin`,
and the external evidence directory
`/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/conditional-stability-evidence-20261028`.
It registered `actual-execution/native-01` and `actual-execution/full-build-01`.
A fresh reproduction starts from that predecessor and the frozen new source/protocol;
it must not apply the append-only consumer update a second time to an already integrated tree.

Supply three additional exact parameters:

| Parameter | Required value |
| --- | --- |
| `UEOT_BASE` | The exact authorized predecessor commit, with 701 modules, 4,463 public registrations and 15 overlays. Set it after the independent L2 authorization is settled and before committing this production change. A later documentation-only base is allowed if these immutable predecessor inputs are unchanged. |
| `UEOT_LAKE` | Absolute path to the existing **actual** pinned Lake executable, not an elan proxy. |
| `UEOT_LEAN` | Absolute path to the matching actual Lean executable in the same directory. The unchanged identity helper requires Lean `4.33.1` and the exact existing nine dependency revisions. |

For example, obtain the exact base with `git -C "$UEOT_REPO" rev-parse HEAD`
at the predecessor point, and take the two executable paths from the existing
successful build identity. Do not infer a new dependency/toolchain version.

The production source files must already be installed as
`UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteConditionalStability.lean`
and `FiniteConditionalStabilityWitness.lean`. Add their two root imports in the
existing import block of `TheoryCompletion.lean`. Keep all previous imports in
order. The native driver independently rejects any other prior Lean source
change. Install the five new protocol files before freezing. Keep all six
existing consumer files at their predecessor bytes until the consumer apply
step below.

## 1. Freeze the final source and protocol

```bash
python3 "$UEOT_PROTOCOL/freeze_inputs.py" \
  --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" \
  --output "$UEOT_RUN/FROZEN_INPUTS.json"
```

The manifest file must be new and outside the repository. Check its reported
`complete_modules = 703`; its actual `new_public` and `lexical_hinted` values
drive all later counts. A source/protocol edit after freezing requires a new
freeze and a new real execution directory. Earlier failures remain evidence of
their own input version.

## 2. Run the real complete UEOT build

```bash
python3 "$UEOT_PROTOCOL/full_build.py" \
  --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" \
  --frozen-inputs "$UEOT_RUN/FROZEN_INPUTS.json" \
  --output "$UEOT_RUN/full-build-final" \
  --lake "$UEOT_LAKE" --lean "$UEOT_LEAN"
```

The full-build directory must not already exist. Its basename must begin with
`full-build-`, as required by the unchanged registration driver. The receipt
must report `PASS` for the actual `lake build UEOT`; an old build receipt or a
source-only scan cannot substitute for it.

## 3. Export and replay the native proof evidence

```bash
python3 "$UEOT_PROTOCOL/integration_native.py" run \
  --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" \
  --frozen-inputs "$UEOT_RUN/FROZEN_INPUTS.json" \
  --build-receipt "$UEOT_RUN/full-build-final/FULL_BUILD_RECEIPT.json" \
  --output "$UEOT_RUN/native-final"
```

This command performs its own preparation, actual export, fixed verifier and
all existing comparisons. Its output directory must be new. The optional
`prepare` mode is available for a source-only review in a **different** new
directory; its `PENDING_ACTUAL_NATIVE_EXECUTION` state is never rewritten as
execution success.

## 4. Check, then register the exact evidence

```bash
python3 "$UEOT_PROTOCOL/register_overlay.py" \
  --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" \
  --frozen-inputs "$UEOT_RUN/FROZEN_INPUTS.json" \
  --native-output "$UEOT_RUN/native-final" \
  --build-receipt "$UEOT_RUN/full-build-final/FULL_BUILD_RECEIPT.json" \
  --archive-relative "$UEOT_ARCHIVE" --check-only

python3 "$UEOT_PROTOCOL/register_overlay.py" \
  --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" \
  --frozen-inputs "$UEOT_RUN/FROZEN_INPUTS.json" \
  --native-output "$UEOT_RUN/native-final" \
  --build-receipt "$UEOT_RUN/full-build-final/FULL_BUILD_RECEIPT.json" \
  --archive-relative "$UEOT_ARCHIVE"
```

Registration adds only lexical preflight and provenance around the raw overlay;
it writes the new native, verifier, registered overlay and their exact archived
inputs. The old consumers remain unchanged. The consumer helper requires this
completed registration and checks its source identity, full native ownership,
raw/registered equality, provenance hashes, edge counts and type-comparison
census before deriving any new statistics.

## 5. Prepare and review six existing consumers

```bash
python3 "$UEOT_PREPARER" prepare \
  --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" \
  --frozen-inputs "$UEOT_RUN/FROZEN_INPUTS.json" \
  --output "$UEOT_RUN/consumer-candidates"
```

The new candidate directory contains `MANIFEST.json` and exactly these six
repository-relative replacement files:

1. `formalization/ueot-core/docs/compression/theory_completion/knowledge/README.md`
2. `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/fkrg_reuse.py`
3. `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py`
4. `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/REBUILD_CLONE_CANDIDATES.py`
5. `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/README.md`
6. `formalization/ueot-core/docs/compression/theory_completion/unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json`

The first five are deterministic narrow updates. Four registry lists each gain
exactly one final entry; their first 15 entries and all existing evidence pins
are checked unchanged. All 70 historical regression methods remain, with only
three existing live-census methods updated, and four new methods are added
(`74` total). The clone scanner changes only its module-census docstring;
its executable AST and the 68-row immutable clone asset remain unchanged.
Historical layer descriptions keep their original numbers.

The sixth file is generated by the exact predecessor
`build_umc_global_map.py`, with only its output destination redirected in memory
to the external candidate directory. It reads the real source tree. The source
fingerprint, 703 modules, root reachability and absence of import defects are
checked before the candidate is accepted. The generator itself is not modified.

Review the six diffs against the current worktree. The manifest records their
old/new hashes, every derived census, all registration input hashes, and hashes
of the prior tracked reuse assets. Preparation does not modify the repository.

## 6. Apply the reviewed candidates, then run the existing consumers

```bash
python3 "$UEOT_PREPARER" apply \
  --repo "$UEOT_REPO" \
  --candidates "$UEOT_RUN/consumer-candidates"

python3 "$UEOT_REUSE/fkrg_reuse.py" --json status
python3 "$UEOT_REUSE/test_fkrg_reuse.py"
python3 "$UEOT_REUSE/REBUILD_CLONE_CANDIDATES.py"
```

Application revalidates the frozen source/protocol and registration evidence,
re-renders all five consumers, verifies exact candidates and six-file scope,
then writes the replacements sequentially. It immediately loads the live
source-verified registry, checks the complete new census and checks all prior
reuse assets byte-for-byte. If those checks fail, it restores files it wrote,
without overwriting any concurrent edit. `APPLICATION_RECEIPT.json` records the
actual result outside the repository; it does not claim the subsequent test or
clone commands have run.

Keep actual command logs. A clone mismatch is a source/evidence mismatch to
resolve; this helper never changes the historical clone table. The existing
Git-object PR preflight, independent mathematical review, release checks and
resulting-main verification remain separate steps owned by the root agent.

## Cloud verification already completed

All six new Python files parse. Each of the three protocol adaptation branches
was instantiated against the current immutable driver text with three synthetic
public/hint inputs. Every replacement anchor occurred exactly once, and the
integration driver's 44 `assert` gates and registration driver's 61 `require`
gates were retained. The original full-build control flow is unchanged apart
from its receipt schema. The five consumer renders were checked against the
actual current consumer text using two different synthetic sets of counts;
both retained the old tests/pins and produced 74 tests.

Those checks verify preparation code only. These preparation checks were performed by the integration helper author.
The root operator subsequently ran the real Mac protocol. Those later results
are recorded separately in `actual-execution/` and `RELEASE_ACCEPTANCE.json`;
this paragraph does not replace their actual receipts.
