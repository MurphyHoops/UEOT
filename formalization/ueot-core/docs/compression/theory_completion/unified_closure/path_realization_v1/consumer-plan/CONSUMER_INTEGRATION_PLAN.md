# Path-realization live consumers: minimal integration plan

Status: **PLAN_ONLY; NO EXISTING CONSUMER EDITS; ACTUAL NATIVE EVIDENCE PENDING**.

This plan was prepared against accepted source base
`50a91fb9c81e0f5e698ce2cc02ec1a44c9583b04`. The separate operations candidate
`91366e9cf38815788978aeaf010f3016942d31dd` has the reviewed policy-only tree
`08e1f9869bdad2c8b1d2a95a602711ffaa1eb92b`. Its proposed exception is
`TC-PATH-REALIZATION-EVIDENCE-2026-10-22`, bound to exactly
`^compression/theory-completion-path-realization$` and the existing six paths.
That candidate is not itself a canonical scientific baseline. The coordinator
must first accept the operations merge and use its exact resulting baseline.

`BASELINE_PRESERVATION_MANIFEST.json` records the existing six files, all ten
overlay/verifier pins, their retained native evidence where present, and the
immutable 68-row clone index. Preparation checked those file hashes and the
six files' exact equality to the accepted base; it did not run the proof
navigator with a freshness bypass or change any existing file.

## Existing evidence that remains fixed

| Existing layer | Accepted value |
|---|---|
| Complete source census | 684 modules: 673 maintained, 11 adapted upstream |
| Existing overlays | 10 |
| Registered public proof graph | 4,272 nodes; 5,614 direct registered edges |
| Overlay contribution | 479 registered nodes; 727 outgoing edges |
| Retained historical repairs | One public registration and one old-node incoming edge |
| Lexical reuse hints | 108 groups; not proof dependencies |
| Historical type evidence | 37 equal-type groups, 77 names, 15 near-type pairs |
| Clone index | 68 rows, SHA-256 `e369d3eee8fe5383532bf68c18ed08ec961d9710b4d600da3edc11a243ebc064` |
| Current complete-source fingerprint | `179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6` |

The eleventh overlay's predecessor is exactly
`FINITE_MEMORY_REUSE_OVERLAY_V1.json`, SHA-256
`cd697c44f7a5d7e4b73a0b53d7477b2e1e8aee43ab55e105b515cd531fd63d38`.
None of the ten old overlays, old fixed certificates, old native exports,
old receipts, immutable audit tables, clone rows, frozen theorem files, or
counted ledgers is rewritten by this plan.

## New artifact scope and dynamic values

The prepared protocol fixes seven new physical source modules:
`C3ExecutableSearch`, `FiniteMemoryRealization`, `FiniteMemoryPhysicalSafety`,
`FiniteMemorySafetyWitness`, `SameSourceFiniteWindow`, `FiniteWindowDoob`, and
`FiniteWindowDoobWitness`, each under
`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure`.
The intended complete census is therefore 691 modules, with 680 maintained
and the same 11 adapted upstream modules. The actual final source census
must verify this; it is not inferred from filenames alone.

The new three reuse artifacts are:

- `PATH_REALIZATION_NATIVE_V1.json`: the full actual compiler-owned theorem
  census, retaining private and generated constants as well as confirmed
  public source candidates.
- `VERIFY_PATH_REALIZATION_OVERLAY_TYPES.lean`: the actual fixed certificate
  replaying raw stored-type comparisons, proof edges, owners, and axiom scope.
- `PATH_REALIZATION_REUSE_OVERLAY_V1.json`: the registered overlay, extending
  the preserved predecessor chain with the new source modules and actual
  public proof dependencies.

All three are additive files under `knowledge/reuse/`. Their final digests
are installed only after actual native execution and independent review.
The corresponding raw outputs and complete executed protocols remain in
the new `path_realization_v1/actual-execution/` archive.

Let `p`, `e`, and `h` be the actually recorded new public registration count,
new registered direct-edge count, and new lexical-hint count. The final
aggregate assertions are `4272 + p` graph nodes, `5614 + e` graph edges,
`479 + p` overlay nodes, `727 + e` overlay edges, and `108 + h` lexical-hint
groups. Raw stored-type comparisons are `4272 * p` cross-layer comparisons
and `p * (p - 1) / 2` internal comparisons. The native census independently
provides its private/generated totals. None of these values is guessed or
copied from a source theorem-token count.

The new source fingerprint must match the same frozen corpus across the
full build, both native executions, fixed certificate, registration, and
later source-derived DAG. The only expected source-hash override for an
existing Lean file is the exact import-only `TheoryCompletion.lean` change.
Any additional old Lean mutation is a scope error requiring separate action.

## Minimal changes to the six authorized existing files

Paths below are relative to `docs/compression/theory_completion/`.

| Existing file | Minimal intended change |
|---|---|
| `unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json` | Regenerate from the final public-root-reachable source using the unchanged `build_umc_global_map.py`. Verify 691 entries, complete reachability, no missing internal imports or cycles, and the exact frozen source fingerprint. This file remains an import/declaration metadata DAG, not a compiled theorem graph. |
| `knowledge/reuse/fkrg_reuse.py` | Append one entry to each of `OVERLAY_PATHS`, `OVERLAY_TYPE_CHECKS`, `OVERLAY_SHA256S`, and `OVERLAY_TYPE_CHECK_SHA256S`; add path-realization to the descriptive source-of-truth text. Preserve the existing generic schema, source-set, source-hash, prior-chain, native-hash, build-environment, ledger, and clone checks. |
| `knowledge/reuse/test_fkrg_reuse.py` | Update only aggregate current-census totals and the total layer count; retain every historical layer's assertions. Add source/native ownership, actual direct-edge, axiom, fixed-export equality, byte-preserving registration, and native-drift rejection checks for index 10. |
| `knowledge/reuse/REBUILD_CLONE_CANDIDATES.py` | Update the descriptive current-census text to 691 and eleven layers once verified. Keep the actual scanner and immutable-table equality check unchanged. |
| `knowledge/reuse/README.md` | Refresh the current summary from actual receipts; append Layer 11 with artifact hashes, exact source/type/native scope, substantive reuse, and mathematical boundaries. Retain Layer 10 and all earlier historical records as history. |
| `knowledge/README.md` | Update the live census and newest-science summary with the actual final fingerprint and graph counts; preserve the distinction between imports, compiled dependencies, lexical hints, and frozen counted authority. |

The authorized scope permits an existing-file update; it does not require
rewriting unaffected implementation. No change to the generic navigator
schema or proof parser is currently needed. All existing ten-layer pins,
including `OVERLAY_PATHS[9]`, remain at the same indices and values.

## New-layer consumer assertions

The source ownership test should compare the exact seven-module set with
both `added_modules` and the complete native ownership scope. Every native
record retains `name`, physical `source_module`, privacy, stored universe
parameters, displayed type, full direct constants, direct theorem constants,
and transitive axioms. The axiom list must stay within `propext`,
`Classical.choice`, and `Quot.sound`.

The public records must be the exact declared public source-name set and a
subset of the complete native records. Their registered dependencies must
equal the actual proof-body constants intersected with the complete current
registered graph, excluding the declaration itself. Private helpers and
generated constants remain in the full native artifact without being
silently counted as public graph nodes.

The principal semantic routes to inspect are the finite-memory law to
actual augmented prefixes and projected state events; physical safety to
the existing zero-occupancy/support and countable-intersection results; the
support controller to its own existing occupancy proof; C3's executed
output to the old `firstGoodIndex_chainMinimal`; and the conditioned-path /
Doob witness to the actual finite-window identities. Exact edge assertions
must be selected from the resulting proof-value export. A source-level
`rw` or theorem name is not evidence that the compiled proof contains an
edge.

Registration checks must retain the raw PENDING preflight and all actual
attempt states. The registered object may add only the declared
`lexical_pr_preflight` and `registration_provenance` metadata to the raw
overlay; removing those additions must recover the raw JSON exactly. All
archived input bytes, full-build/native/registration driver sources, literal
substitutions, wrapper files, frozen manifest, raw logs, fixed verifier, and
initial/fixed full native exports must bind to the same actual run.

## Clone and freshness gates

The old clone index is a source-snippet candidate table, not a theorem
equivalence certificate. Its immutable bytes remain fixed. The existing
scanner compares a fresh scan of the complete registered current source
census with all 68 rows. The new source may create additional eight-line
normalized matches, so preserving the old JSON alone does not establish
that this gate passes. A concrete new match must be inspected before the
final native freeze; it must not be hidden by weakening the scanner or
rewriting historical rows.

Before the new overlay is accepted, the live navigator is expected to reject
the newly added source set as stale. This is the correct behavior. It must
not be bypassed to present an old graph as proof evidence for new code.
Reconstructing the immutable baseline graph inside the dedicated build
protocol is a separately bound historical-input operation, not a live
freshness certificate.

## Execution order and acceptance

1. Finish focused compilation and source review of all seven modules;
   resolve any concrete clone or type-collision issue before final freezing.
2. Accept the operations merge, take its exact canonical baseline, and add
   the seven public imports. Freeze complete source/protocol input bytes.
3. Run the actual full build and initial/fixed native passes under the same
   pinned toolchain. Retain every attempt's own receipts and logs.
4. Independently review the exact native exports and protocol archives;
   register the additive artifacts with metadata-only provenance.
5. Apply the six-path updates described above, using only the final artifact
   hashes and actual aggregate values. Regenerate the DAG from the unchanged
   frozen source corpus.
6. Run the necessary live FKRG/consumer/clone and canonical integration
   gates, then committed-object preflight and the separate publication /
   resulting-main checks. The unchanged canonical audit's actual rebuild
   retains its own command and receipt.

Any later Lean change requires a new source freeze and affected actual
execution; it cannot be absorbed by changing a reported hash. Consumer
documentation cannot upgrade focused compilation to a full build, upgrade
an import edge to a proof dependency, or upgrade a local theorem to global
closure. The frozen 106 P-ID classification and four counted generators
remain unchanged; strong global closure remains `NOT_ESTABLISHED`.
