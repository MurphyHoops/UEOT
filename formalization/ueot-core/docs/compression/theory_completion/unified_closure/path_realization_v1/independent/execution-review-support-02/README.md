# Exact support for the independent execution review

These eleven files are byte-for-byte copies of the temporary originals used or
retained by the independent execution reviewer. `MANIFEST.json` records their
original locations, repository destinations, lengths and hashes, and binds the
already signed `../ACTUAL_EXECUTION_REVIEW.{md,json}`. This archival step does
not rerun any build, native comparison, source analysis or completed audit.

`independent_execution_audit_02.py` is the actual read-only reviewer program.
Its existing attempt receipt and raw log record exit 0 and 19.805800499 seconds.
The four supporting byte-audit records retain their original preparation/report
status strings; the signed parent review supplies the final bounded CLEAR.
The earlier `independent_execution_audit.py` was prepared for frozen01 and was
never executed. Both preparation records are preserved without status changes.
The canonical-wrapper record is static approval only, not actual canonical
execution evidence.

The historical native01 failure has two distinct recorded exit codes: the
outer Python integration driver exited **1**, while its inner `lake env lean`
execution returned **130** after SIGINT. The original status file records the
inner result; the original tool observation records the outer result. Those
original bytes and the pending source-preflight state remain unchanged under
`../../actual-execution/`. The separate partial progress and reversed-pair
runs are diagnostics, not successful acceptance of the former 77-public scope.

This directory adds exact archival provenance to the already completed review.
Actual metadata registration, consumer integration, canonical execution and
publication retain their own receipts and independent scope.
