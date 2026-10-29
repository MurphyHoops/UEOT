# Reproduce the finite-data consumer

The immutable source/reuse baseline is `f4c23ac61b440df9d88ca1e79a4684d589066489`.
The accepted complete Core source fingerprint is
`98734d8a4ae150a66e5bbdac18008897d98f9cc97f7e68f45fa7eb5d813c92f2`.
Local source, toolchain, nine dependencies and commands are bound in the actual
full/native receipts. No cloud Lean success is claimed; the three Core workflows
remain manually disabled.

From the integrated checkout, replay SAVED DATA without drawing again:

```sh
python3 -B formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_data_loop_v1/certify_data.py \
  formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_data_loop_v1/actual-execution/registered-batch-01/records/A \
  --horizon 10 --output /absolute/new-certificate-output
python3 -B formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_data_loop_v1/independent_evaluate.py \
  formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_data_loop_v1/actual-execution/registered-batch-01 \
  --output /absolute/new-independent-evaluation.json
```

The first command re-counts all bound bits and checks the same saved decision
and deployment provenance before actual Lean. Good and true parameters are never
selector inputs. The second command is a separate truth-owning exact evaluator;
it is not part of policy selection. A replay is not a new independent sample.

`actual-execution/registered-batch-01` is the complete frozen registration,
including every packed probe result, rejected decision and unfiltered accepted
trace. `SAMPLE_STARTED.json` is exclusive: do not run `--sample` again. The private
file contains only simulation truth and frozen replay seeds, not credentials.
The source program's `--freeze`/`--sample` interface belongs to a new separately
authorized experiment, not to repairing or repeating this registered draw.

For integration reproduction, start at the stated baseline, install this
package's twelve new modules, additive root imports and pinned reused protocol,
and retain the baseline's six consumers until the reviewed candidate application.
Use `native_protocol/freeze_inputs.py`, `full_build.py`, `integration_native.py`
and `register_overlay.py` with explicit fresh external output paths, the stated
base, and the actual pinned Lean/lake binaries. The frozen inputs and archived
actual commands provide their full arguments. Source/owner/type/axiom/collision,
fixed replay, old-byte preservation and deterministic six-consumer application
checks remain unchanged. Do not apply the append-only consumer update twice.

Focused Python tests are `test_runtime.py`, `test_certify_data.py` and the repaired
old `action_certificates_v1/test_certify.py`. The actual registered five proofs,
normal eight-case exact replay, artifact substitution negatives, full build,
native replay, reuse/parser/FKRG/clones/UMC and governance/compression/finalization
checks are retained under `actual-execution`. Ledger-mutating negative controls
must run serially with governance/ledger readers. A first full-build root-import
placement failure and the missing live-reference flag failure are preserved with
the corrected successful runs.
