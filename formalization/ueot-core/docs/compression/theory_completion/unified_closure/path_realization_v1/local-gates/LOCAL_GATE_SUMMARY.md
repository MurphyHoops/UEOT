# Actual local gates for the eleven-layer path-realization integration

**Status: `REQUIRED_LOCAL_GATES_PASS`.**

All results below are actual recorded executions. The unchanged 89-test
parser result is reused from its earlier required run. The other four rows
belong to the installed eleven-layer consumer and unchanged final Lean source.

| Gate | Actual result | Elapsed wall seconds | Receipt |
|---|---|---:|---|
| Immutable-base parser | 89 tests, 89 success lines, zero skips | 3.479902313 | [parser-01](parser-01/RECEIPT.json) |
| Unchanged DAG builder | 691 modules, all reachable from `UEOT`, no cycles or missing imports | 0.275660907 | [dag-01](dag-01/RECEIPT.json) |
| Complete live reuse regression | 54 tests, zero skips | 2.345196625 | [reuse-01](reuse-01/RECEIPT.json) |
| Complete FKRG regression | 30 tests, including the real fast-audit integration, zero skips | 3.456621410 | [fkrg-01](fkrg-01/RECEIPT.json) |
| Standalone complete clone scan | All 691 source modules; exact equality with all 68 immutable rows | 1.739884659 | [clone-01](clone-01/RECEIPT.json) |

Every process returned exit code `0`. Each gate directory preserves its
original stdout and stderr. The parser and normal current-source gates also
preserve their full command, working directory, tested input hashes and
execution timing. No test selection or skip was added. The complete clone
scan includes row ordering, file paths, source lines and excerpts; it did not
merely compare a row count. Its result still has 12 spans of at least 15 lines
and a longest span of 31 lines. Source-text equality is not theorem equivalence.

The final complete Lean source fingerprint is
`de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379`.
The six installed consumer/DAG hashes are recorded in
[APPLIED_SIX_PATHS_01.json](../consumer-plan/APPLIED_SIX_PATHS_01.json),
SHA-256 `fb8546ac7f6005e3b683986028f568d774294acbc89cd460f3a87693bbedfe03`.
All those inputs and the complete source fingerprint were unchanged across
each of the three current-source gate executions. The standalone commands
use normal live freshness verification.

The [author's structural preservation check](../consumer-plan/PRESERVATION_01.json)
confirms that the reuse consumer changes only by appending one entry to each
of its four registry arrays. The original ten overlay/certificate pairs
retain their exact pinned bytes. The clone scanner differs only in its
module docstring; its complete executable AST is unchanged. All 50 previous
reuse tests remain, with only current-census constants updated in three
methods. Four new tests cover complete native ownership and public edges,
canonical same-source reuse, actual use of the five private mass facts, and
metadata-only registration with archived input binding.

The [machine-readable index](LOCAL_GATE_SUMMARY.json), SHA-256
`3e4cb2e284f2bf01d77520ae7a998013a93fc86f2735044195d7a17080b5deb1`,
binds the individual receipts and the preservation check. Those checks are
separate from the independently authored consumer review. Actual native,
registration, canonical audit, Git-object preflight, PR and resulting-main
acceptance retain their own evidence; no local result is used to predeclare
publication. Frozen P-ID classifications, counted results and strong global
closure `NOT_ESTABLISHED` remain unchanged.
