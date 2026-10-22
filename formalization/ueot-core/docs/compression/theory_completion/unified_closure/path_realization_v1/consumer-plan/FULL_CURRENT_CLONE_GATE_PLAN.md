# Full current-source clone gate: prepared invocation

Status: **INVOCATION_PREPARED; NOT_EXECUTED_FOR_THE_NEW_OVERLAY**.

The earlier targeted diagnostics only examined pairs involving the seven new
modules. Their zero-match result does not replace the canonical full scan.
This gate runs after the actual eleventh overlay and its fixed certificates
have been registered and the live consumer has been updated with their exact
digests. The immutable operations baseline is
`d503586107974c56e0773b4ea106b41a7d144b43`; accepting that baseline does not by
itself satisfy the new compiled-source freshness gate.

## Exact invocation

From the repository root, execute:

```sh
python3 formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/REBUILD_CLONE_CANDIDATES.py
```

The existing entry point calls the live consumer's default `load()` and hence
requires current-source verification. It then computes the complete normalized
eight-line-window scan and compares the full resulting row list, including
ordering, paths, line positions and excerpts, to `CLONE_CANDIDATES_68.json`.
There is no `verify_source=False` argument, targeted-pair filter, modified
threshold, accepted-extra-row rule, or alternative clone baseline in this
invocation. The implementation of `scan()` and the immutable equality check
remain unchanged; only the existing scanner's census docstring may be updated
within the separately authorized six-path integration.

## Required preconditions and recorded outcome

Before invoking the gate, the coordinator checks that the registered live
consumer loads all eleven layers against the final 691-module source corpus
and that the same corpus is bound to the actual native and full-build receipts.
The old ten overlay/verifier pins and all old evidence remain preserved. The
archived clone table must retain SHA-256
`e369d3eee8fe5383532bf68c18ed08ec961d9710b4d600da3edc11a243ebc064`.

Preserve the exact command, working directory, exit code, unmodified stdout and
stderr, executed scanner hash, executed consumer hash, clone-table hash, final
source fingerprint, and the final overlay/native/certificate digests in the
new execution archive. On success, the unchanged scanner reports the actual
pair count, count of pairs at least fifteen lines long, and maximum match
length. Do not prepopulate these values or label this planned invocation PASS.

If the resulting list differs, preserve the failure and inspect its exact new
or changed rows. A mathematical reason for a repeated proof fragment does not
turn a mismatching scan into a successful immutable-table check. Any resolution
must respect the governed source and evidence scope; editing syntax solely to
avoid a clone count is not a reuse improvement.

This gate establishes exact normalized source-snippet matching for the current
corpus. It establishes neither logical theorem equivalence nor absence of
semantic redundancy; source/type review and actual Lean stored-type and proof
dependency export have separate responsibilities.
