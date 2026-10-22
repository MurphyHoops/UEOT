# Independent static review of candidate alignment and push drivers

**Result: STATIC_CLEAR_EXACT_CANDIDATE_MANIFEST_AND_EXECUTION_PENDING.**

Reviewer: `/root/finite_window_source`, 2026-10-22. This review read both complete
new scripts and the exact predecessor scripts identified in preparation. It
parsed Python syntax and compared source bytes; it did not run alignment, push,
Mac tools or create a candidate manifest. The companion JSON retains the exact
unified source diffs and all reviewed hashes.

| Script | Reviewed SHA-256 |
|---|---|
| `publication/align_mac_candidate.py` | `22eba5b3dec07f516cf508513f56d86af3428c04c2070e0914abfa08bc747f77` |
| `publication/push_candidate.py` | `bb4a12e6302b0edc98e28fe7d313410d48c7bbb3d1d236db59d2681562c6bb79` |

The predecessor hashes match `PUBLICATION_DRIVER_PREPARATION.json`: alignment
`db6af8afdfb7df1fda50df935f8ee82e466a8e1d5fe219d059216ea4379aebca`
and push `bb962d8a76024c06d9d803590eaf44b6d5a7a7b5a601780982f6c8b2728e0750`.
Those predecessors were read from the preserved publication checkpoint paths
specified in that preparation record; this is not a claim that these Python
files themselves were found at repository Git paths.

## Alignment

The script requires the exact accepted baseline and owned research branch,
resolves the candidate tree through Git, and compares the complete sorted
changed-path list with the concrete reviewed manifest. This replaces the old
fixed-head/tree values and count-only `202` assertion with an exact manifest
binding. The manifest must itself receive the separate immutable-candidate
review; its status string is not a new authorization mechanism.

The entire block that collects worktree changes, isolates the existing `.lake`
cache exception, refuses unexpected paths, saves the gzip checkpoint, performs
the scoped restore and soft reset, and checks final tracked cleanliness is
byte-identical to the predecessor. Every existing changed-path file is backed
up with its original bytes/hash before mutation. The only restored paths are
the exact candidate changed paths. The cache exception neither expands the
restored scope nor changes the expected candidate tree.

After alignment, the script compares the complete actual source/runtime/nine-
dependency identity with the accepted full-build02 identity, requires 691
modules and frozen source `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379`,
and writes the actual alignment record. This execution must still occur on
the concrete reviewed candidate; static approval supplies no alignment PASS.

## Push

The new preconditions require the actual local candidate HEAD and tree, and
the actual successful alignment record for the same candidate, tree and frozen
source. The core push block is byte-identical to the predecessor except for
its receipt schema name.

That block requires observed remote main to equal the exact accepted baseline
and the owned destination ref to be absent. It issues one explicit
`candidate-SHA:refs/heads/compression/theory-completion-path-realization`
refspec with an absent-ref lease. It does not request a main or unrelated-ref
update. The recorded return code and raw log precede separate after-push
verification: the owned ref must equal the exact candidate and every other
observed remote head must equal the before snapshot. An existing destination
or changed observed main is a refusal, with no automatic overwrite fallback.

## Scope of clearance

I found no removed backup, broadened restore scope, weakened preserved-cache
condition, relaxed remote lease, or loss of after-push other-head comparison.
The changed elements are the current paths/baseline/ref/schema/census, the
explicit reviewed candidate manifest, and additional source/alignment binding.

The required concrete candidate manifest and actual execution receipts remain
separate. This source review does not publish anything, alter the five frozen
native protocol scripts, change a Lean source, or change `NOT_ESTABLISHED`.
