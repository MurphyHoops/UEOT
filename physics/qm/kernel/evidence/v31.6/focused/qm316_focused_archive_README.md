# v31.6 focused author evidence archive

This directory preserves byte-identical copies of final author reports, actual focused build and witness logs, explicit target inputs, source reviews, chapter reviews, and the serial Core dependency build records.

`files-manifest.json` records each archived file's original absolute path, byte count, SHA256, category and evidence status. The manifest excludes its own hash to avoid self-reference. Final source hashes are bound separately in that manifest; source modules are not duplicated here.

## Interpretation of statuses

- `PASS_RECORDED`: an actual successful author-run build or axiom/witness log, or its final report. The underlying report states the exact scope.
- `FAILED_RECORDED`: an actual intermediate failed log, retained unchanged. Any elaborator-generated `sorryAx` in such a failed run is historical failure evidence and is never an accepted certificate.
- `ABORTED_RECORDED`: explicit records of owned superseded/parallel compiler termination after resource diagnosis. These are not successful runs.
- `NOT_RUN_PREPARED_INPUT`: a prepared main-module audit input that was not separately run because the root scheduled one unified public audit. This applies to the real and Doob main audit inputs.
- `TARGETS` / `HISTORICAL_CANDIDATE` / `SOURCE_REVIEW_PASS` / `BOOK_REVIEW_PASS`: target inventories, earlier candidate records, or source/prose reviews, with no implied independent compilation beyond their explicit reports.
- `SERIAL_CORE_RESULT`: the preserved 51-module direct-closure inventory distinguishes 21 newly built PASS targets from 30 already present artifacts; the final focused Lake run validates that dependency closure.

All five saved failed author logs and both recorded owned-process aborts remain explicit. B confirmed there is no separately saved failed real-tomography log; its prototype files are not acceptance evidence. The initial aborted scalar/Core process streams have no separate retained raw log in the author archive inventory; their explicit termination records are retained.

A's and C's public-module audit schedules differ: A ran its own 87-target focused audit; B and C delegated their main-module targets to root's unified audit while independently checking their witness scripts. A source review that says global compilation is pending remains unchanged here and does not claim a result of the root's later acceptance run.

No Lean command was run during this archive operation. No Python source, prototype source, build artifact, full book/PDF, or planning-only v31.7 contract is included. All files outside this focused subdirectory are owned by other integration steps and were left untouched.
