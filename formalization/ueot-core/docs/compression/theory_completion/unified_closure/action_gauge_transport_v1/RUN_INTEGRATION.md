# Action realizability, gauge classification and conditioned transport: integration

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
census `703 / 4474 / 16`, the five-module scope, and the new census `708`.
The public declaration count, lexical hints and source fingerprint come from
the actual freeze. No public count is preset.

## Parameters

Run from the existing Mac worktree using Python 3.11 or later. Set these once:

```bash
UEOT_REPO='/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/total-kernel-memory-20261023'
UEOT_CORE="$UEOT_REPO/formalization/ueot-core"
UEOT_PACKET='formalization/ueot-core/docs/compression/theory_completion/unified_closure'
UEOT_PROTOCOL="$UEOT_REPO/$UEOT_PACKET/action_gauge_transport_v1/native_protocol"
UEOT_REUSE="$UEOT_CORE/docs/compression/theory_completion/knowledge/reuse"
UEOT_RUN='/tmp/ueot-action-gauge-transport-reproduction-20261028'
UEOT_ARCHIVE="$UEOT_PACKET/action_gauge_transport_v1/reproduction/native-final"
UEOT_PREPARER="$UEOT_REPO/$UEOT_PACKET/action_gauge_transport_v1/prepare_consumers.py"
```

The continuation starts from main `1932c6794e001510deca7c8f0a0f2bae18dc6c4c`,
whose mathematical/source census is the declared predecessor. A separate
scope-authorization commit may become the exact parent; its source, environment,
old registry and immutable evidence must remain unchanged. Read the actual
frozen manifest for the execution's exact base. The existing pinned executables
are under `/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin`.
Set `UEOT_RUN` to a new evidence directory outside the repository. The actual
execution receipt records the production directory; the path above is a fresh
reproduction example, not a claim about an already executed run.
A fresh reproduction starts from that predecessor with the frozen new source/protocol;
it must not apply the append-only consumer update a second time to an already
integrated tree. Core Lean, Guard and Base Policy cloud workflows remain
user-disabled; their absence is not a passed build.

Supply three additional exact parameters:

| Parameter | Required value |
| --- | --- |
| `UEOT_BASE` | The exact authorized predecessor commit, with 703 modules, 4,474 public registrations and 16 overlays. Set it after the independent L2 authorization is settled and before committing this production change. A later documentation-only base is allowed if these immutable predecessor inputs are unchanged. |
| `UEOT_LAKE` | Absolute path to the existing **actual** pinned Lake executable, not an elan proxy. |
| `UEOT_LEAN` | Absolute path to the matching actual Lean executable in the same directory. The unchanged identity helper requires Lean `4.33.1` and the exact existing nine dependency revisions. |

For example, obtain the exact base with `git -C "$UEOT_REPO" rev-parse HEAD`
at the predecessor point, and take the two executable paths from the existing
successful build identity. Do not infer a new dependency/toolchain version.

The five production source files must already be installed under
`UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`:

- `FiniteActionRealizability.lean`
- `FiniteActionRealizabilityWitness.lean`
- `DualDriveLinearGaugeClassification.lean`
- `DualDriveOperationalAnchors.lean`
- `ConditionedActionTransport.lean`

Append their five imports within the existing root import block in
`TheoryCompletion.lean`. Keep every previous import and its order. The native
driver independently rejects any other prior Lean source change. Install the
five new protocol files before freezing. Keep all six existing consumers at
their predecessor bytes until the consumer apply step below.

## 1. Freeze the final source and protocol

```bash
python3 "$UEOT_PROTOCOL/freeze_inputs.py" \
  --repo "$UEOT_REPO" --base-ref "$UEOT_BASE" \
  --output "$UEOT_RUN/FROZEN_INPUTS.json"
```

The manifest file must be new and outside the repository. Check its reported
`complete_modules = 708`; its actual `new_public` and `lexical_hinted` values
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
exactly one final entry; their first 16 entries and all existing evidence pins
are checked unchanged. All 74 historical regression methods remain, with only
three existing live-census methods updated, and four new methods are added
(`78` total). The clone scanner changes only its module-census docstring;
its executable AST and the 68-row immutable clone asset remain unchanged.
Historical layer descriptions keep their original numbers.

The sixth file is generated by the exact predecessor
`build_umc_global_map.py`, with only its output destination redirected in memory
to the external candidate directory. It reads the real source tree. The source
fingerprint, 708 modules, root reachability and absence of import defects are
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

## Preparation-code check and independent review

`check_preparation_code.py` and `PREPARATION_SELF_CHECK.json` record the helper
author's narrow cloud preparation check. All six new Python files parse. Each
of the three adaptation branches was instantiated against the immutable driver
text with three synthetic public/hint inputs. Every replacement anchor occurred
once, and the integration driver's 44 `assert` gates and registration driver's
61 `require` gates were retained. Two different synthetic consumer censuses
both rendered 78 tests. The four registry lists append to the exact previous
16 entries; all immutable pins and the clone scanner executable AST remain
checked. The sixteen historical layer descriptions are byte-preserved.

These synthetic values are not execution results. The checker never runs Lean,
never emits an accepted production freeze, and does not establish any native,
registration, consumer-regression or mathematical result. The actual production
protocol below the freeze validator still requires full source/runtime identity
and real successful executions. Independent review must inspect the new helper
code and actual receipts separately from this author check.

`TYPED_REUSE_REVIEW_REQUEST.json` is a list of comparisons for the independent
reviewer, not a completed verdict. The reviewer must inspect actual stored types
and source premises for all new source declarations and all actual lexical
hints. Native zero collisions are not mathematical independence. The generic
barycenter conversion, its row/fiber consumers, stationary/time-dependent path
identity, conditional source identity, the initial-law obstruction, inverse
factorization classification and operational anchors have different reuse roles.

## Compiler ownership and final release boundaries

The previous layer's eight compiler-owner changes were import-order effects on
already existing generated names; its actual historical record remains unchanged.
This adapter does not extrapolate a whole-UMC native total from that number and
does not preset the new owned-constant count. It records the actual compiler
owners of every new module, classifies private/public-source/other-public names,
then requires the fixed exporter to reproduce the exact observed native census.
If whole-UMC ownership totals move again, explain them using actual name/owner
sets; do not relabel the difference as new source theorems.

Root owns the final typed and semantic review, actual consumer and governance
commands, exact-Git-head preflight, authorized PR/merge, resulting-main identity,
Issue/continuity updates and temporary scope-exception retirement. Reuse heavy
receipts only after proving their complete source/environment/tool/dependency
identity still matches. Preserve every actual failed attempt and its inputs.
No counted-Core mapping, frozen 106/106 ledger, QM scope or empirical status is
changed by this layer. Strong global closure remains `NOT_ESTABLISHED` and
external scientific evidence remains `UNVERIFIED`.
