# Reproduce the certificate package

The accepted source checkpoint is
`a499c2264c1b0b6b770d4023042187baa0b824de833f1ddf6046bffd22393d82`.
The immutable predecessor is `61fc3caead1945f72b919973217d573957a1b8d0`:
the planning mathematical main plus the separately merged six-consumer
authorization, with unchanged prior mathematical sources.

For a fresh integration reproduction, install this package's four new Lean
modules, four additive root imports and its protocol at that predecessor.
Keep its original six consumers until the reviewed application step. Running
append-only application again on an already integrated tree is intentionally
rejected. Use new external directories; never overwrite an execution receipt.

From the repository root, set `R` to that checkout and `E` to a new external
evidence directory. Use the pinned Lean 4.33.1 executables and unchanged nine
dependency revisions recorded in `actual-execution/full-build-01`.

```sh
R="$PWD"
B=61fc3caead1945f72b919973217d573957a1b8d0
P="$R/formalization/ueot-core/docs/compression/theory_completion/unified_closure/action_certificates_v1"
E=/tmp/ueot-new-action-certificates-run
LAKE=/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake
LEAN=/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean

python3 -B "$P/prepare_consumers.py" self-check --repo "$R"
python3 -B "$P/native_protocol/freeze_inputs.py" --repo "$R" --base-ref "$B" --output "$E/FROZEN_INPUTS.json"
python3 -B "$P/native_protocol/full_build.py" --repo "$R" --base-ref "$B" --frozen-inputs "$E/FROZEN_INPUTS.json" --output "$E/full-build-final" --lake "$LAKE" --lean "$LEAN"
python3 -B "$P/native_protocol/integration_native.py" run --repo "$R" --base-ref "$B" --frozen-inputs "$E/FROZEN_INPUTS.json" --build-receipt "$E/full-build-final/FULL_BUILD_RECEIPT.json" --output "$E/native-final"
```

Review the actual native output and source semantics. Then check and register
the exact evidence, using a new repository-relative archive path:

```sh
A=formalization/ueot-core/docs/compression/theory_completion/unified_closure/action_certificates_v1/reproduction/native-final
python3 -B "$P/native_protocol/register_overlay.py" --repo "$R" --base-ref "$B" --frozen-inputs "$E/FROZEN_INPUTS.json" --native-output "$E/native-final" --build-receipt "$E/full-build-final/FULL_BUILD_RECEIPT.json" --archive-relative "$A" --check-only
python3 -B "$P/native_protocol/register_overlay.py" --repo "$R" --base-ref "$B" --frozen-inputs "$E/FROZEN_INPUTS.json" --native-output "$E/native-final" --build-receipt "$E/full-build-final/FULL_BUILD_RECEIPT.json" --archive-relative "$A"
python3 -B "$P/prepare_consumers.py" prepare --repo "$R" --base-ref "$B" --frozen-inputs "$E/FROZEN_INPUTS.json" --output "$E/consumer-candidates"
```

Independently review all six exact candidates before applying:

```sh
python3 -B "$P/prepare_consumers.py" apply --repo "$R" --candidates "$E/consumer-candidates"
python3 -B "$R/formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py"
python3 -B "$R/formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/REBUILD_CLONE_CANDIDATES.py"
```

Run the remaining existing parser, FKRG, governance, mission and full UMC
checks listed in `RELEASE_ACCEPTANCE.json`. Run mutable-ledger compression
negative controls serially with governance checks. They restore original
bytes and must not race with other ledger readers. Preserve any failure.

For the trusted scientific consumer on an already integrated checkout, use
`certify.py --registered --output NEW_EXTERNAL_DIRECTORY` as described in
`RESULTS_AND_BOUNDARIES.md`. Its final receipt is independent of candidate
search success and requires an actual Lean kernel check.

Core Lean, Compression Guard and Research Base Policy cloud workflows remain
disabled by the user. Their absence is not a passed proof check. Publication
uses exact-commit preflight, independent head/tree review, normal PR merge,
local resulting-main validation and retirement of the temporary exception.
