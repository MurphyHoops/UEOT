# Independent review of the path-realization native protocol

**Result: STATIC_PROTOCOL_CLEAR_ACTUAL_EXECUTION_PENDING.**

Reviewer: `/root/c3_executable_search`. Protocol author:
`/root/finite_memory_realization`. Review date: 2026-10-22.
The companion `NATIVE_PROTOCOL_REVIEW.json` binds every reviewed source to its
complete SHA-256, records the delegated immutable drivers and helpers, and
separates static review from future execution.

I read the entire new adapter, all four wrappers, its README and source-only
preparation record; compared the adapter and wrappers with the accepted
`finite_memory_v1` pattern; read the delegated `full_build.py`,
`integration_native.py`, and `register_overlay.py` in
`longterm_control_statistics_v1/native_protocol/`; and checked the build identity
helper and generated native-export logic those drivers consume. The three
delegated drivers and the two inspected helpers are byte-identical to accepted
base `50a91fb9c81e0f5e698ce2cc02ec1a44c9583b04`.

The reviewed new adapter has SHA-256
`8afada91c504c3f97f18cf20b519ac2f701b13fa2211e748bbbc4ddca6bead4f`.
The four wrapper bodies are identical Python ASTs to their accepted
predecessors after removing docstrings. The integration wrapper's textual
change describes seven modules in place of six. The adapter's source diff
changes only the increment namespace, fixed module list, prior and complete
censuses, scientific role, schema names, and archive metadata.

## Fixed and dynamic scope

The fixed predecessor scope is 684 source modules, 4,272 registered public
declarations, and ten overlays. The new source module set is exactly
`C3ExecutableSearch`, `FiniteMemoryRealization`, `FiniteMemoryPhysicalSafety`,
`FiniteMemorySafetyWitness`, `SameSourceFiniteWindow`, `FiniteWindowDoob`, and
`FiniteWindowDoobWitness`, all under the physical UnifiedClosure namespace.
The frozen complete module count must be 691.

The actual source parser computes the new public names, new public count, and
baseline lexical-hint count. The adapter stores these results with the complete
module-name/source-byte fingerprint and exact protocol-source hashes. It does
not substitute anticipated theorem, edge, hint, or native-constant counts.
Registration receives the recorded public and hint counts and independently
checks them against the source-preflight/native artifacts from that same run.

I independently checked the literal substitution lists against the immutable
driver sources:

| Delegated driver | Substitutions | Actual occurrence count per anchor |
|---|---:|---:|
| Full build | 1 | 1 |
| Native integration | 4 | 1 |
| Metadata registration | 11 | 1 |

The adapter rejects any anchor-count change. Its source and inherited driver
guards reject optimized Python that would disable assertions. No assertion or
proof gate is removed by these substitutions. The registration hint check is
retained with the dynamically frozen count replacing a prior increment's
constant. Complete schema/source/owner/edge checks remain in the executed
predecessor code.

## Build and source identity

The full-build wrapper requires a new output directory. Its delegated driver
checks the immutable build-identity helper, captures the complete actual
source corpus and pinned environment, executes actual `lake build UEOT`, and
requires both a zero exit and the build-success marker in the retained raw
log. It compares the full input identity again after the build.

The identity helper retains the pinned Lean/Lake version, same binary directory,
binary hashes, exact toolchain/configuration/manifest hashes, all nine actual
dependency revisions and clean dependency checkouts, and relevant import
environment. Its source digest includes the public root and every recursively
present production Lean module. It detects source/environment changes during
identity capture and compares complete identity objects around execution.

The native preparation reconstructs the actual immutable base consumer, whose
evidence pins remain intact. Its `verify_source=False` use is specifically for
that historical base registry while new sources exist in the worktree; it is
not presented as a current live freshness certificate. Preparation independently
requires every old source to match the base except the import-only
`TheoryCompletion.lean` extension, verifies the exact old public-name set, and
derives new source candidates from the unchanged parser.

## Native evidence and fixed replay

The generated Lean exporter requires each new physical source module to be
imported, enumerates all compiler-owned theorem constants in those modules, and
retains private and generated constants. Every theorem's transitive axiom set
must be contained in `propext`, `Classical.choice`, and `Quot.sound`.

Public candidates must be actual nonprivate theorems owned by their declared
physical modules. The exporter retains complete proof-body constants, theorem
constants, stored universe parameters and displayed types. The established
raw stored-type `Meta.isDefEq` comparisons cover all 4,272 prior registered
types and all distinct new pairs; every observed collision is a failure.
These are raw-type reuse checks, not a general logical-equivalence decision.

The native driver validates its exact successful full-build receipt and log,
then checks the complete identity before and after each Lean process. Its
first actual proof-value export determines the registered direct-edge lists.
The second actual execution verifies those fixed lists and the complete native
census. The full initial and fixed JSON objects must be equal, including
owners, universes, types, proof constants and axioms. Public dependencies are
also checked against the actual proof constants intersected with the whole
registered public-name set. No dependency is inferred merely from a source
theorem name or tactic token.

## Archive and registration binding

The adapter archives the immutable predecessor bytes and the complete adapted
Python source actually executed, together with the wrapper, adapter, literal
substitutions and frozen manifest. The wrapper's `finally` block preserves
these whenever the execution creates its output directory. Registration first
reconstructs and verifies the expected build and native protocol archives from
the same manifest and exact base.

The inherited registration checks preserve the source preflight's original
PENDING status and require separate successful execution records. They bind
the original commands, return codes, raw logs, full native objects, source
fingerprint, public-name set, artifact hashes and predecessor overlay. They
verify source identity before and after planning writes and reject changed
input bytes or an existing destination with different contents.

Registration adds only `lexical_pr_preflight` and `registration_provenance` to
the raw overlay. Its stripped JSON must equal the raw candidate. It copies
the exact native/verifier bytes, retains all actual protocol sources, and does
not edit the existing live consumer or source DAG. The archive path is confined
to the new increment; path traversal and conflicting destinations remain
errors. Check-only mode performs the same checks without writes.

## Decision and remaining execution gates

The reviewed protocol is a bounded reuse of the accepted execution machinery.
I found no disabled assertion, omitted source/runtime identity check, narrowed
compiler ownership census, weakened axiom/type/edge gate, or loss of archival
binding in the new adapter.

This review executed only read-only source/hash/AST/literal checks. It did not
invoke any protocol entrypoint, freeze a manifest, run Lean/Lake/native code,
or perform metadata registration. The next steps remain the coordinator's
exact accepted operations baseline, final seven-module focused/source review,
public imports, source freeze, actual full build and two native passes, and
independent review of those resulting exact-byte records. The protocol does
not supply canonical authorization for shared-file mutation and does not
change frozen counting or global `NOT_ESTABLISHED` status.
