# Actual full-build and native execution review

**Status: CLEAR for the reviewed metadata registration.** No raw execution state was rewritten.

Baseline: `299a4e3a71914af064ccd7916bb285bac201f62a`. Complete source identity: `179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6`.

| Gate | Independently checked result |
|---|---|
| Complete source | All 684 path, size and SHA-256 records match; fingerprint recomputed. |
| Actual full build | `lake build UEOT`, exit 0, 38.402 s; six explicit new-module builds; 9,390-job success marker. |
| Runtime and dependencies | Lean 4.33.1 / Lake runtime hashes recorded; three pinned environment files and nine exact clean dependency revisions; immutable before/after identity gates preserved. |
| Actual native executions | First export 59.387 s, fixed verifier 57.914 s; both exit 0; raw JSON objects equal in full. |
| Compiler census | 82 theorem constants: 35 registered public, 22 private, 25 other generated/public. |
| Axiom closure | Every owned theorem is within `propext`, `Classical.choice`, `Quot.sound`. |
| Raw type comparisons | 148,295 against 4,237 prior declarations; 595 new-new pairs; zero collisions. |
| Direct registered proof edges | All 47 reconstructed from actual proof-value constants; fixed-edge second execution agrees. |
| Protocol provenance | Exact immutable originals, counted substitutions, actual executed bytes, wrappers, adapter and frozen inputs all match. |

## Source and execution identity

The complete 684-module local source record exactly matches the full-build receipt and final frozen manifest; each path, byte count and SHA-256 was checked individually and the source fingerprint was independently recomputed.

Pinned toolchain/environment files match the immutable baseline. The actual receipt records all nine dependency HEADs at their exact manifest revisions with clean worktrees, runtime binary hashes/versions, and empty import overrides.

The immutable build identity implementation and actual executed drivers preserve before/after source, runtime, environment and dependency equality checks. PASS is reachable only after those checks; no Mac command or rerun was performed by this reviewer.

The complete build log retains earlier replayed diagnostics; the evidence above relies on the actual exit status, explicit successful builds and preserved log bytes. The separate focused review already checks clean successful records for all six final source hashes and preserves the three earlier failed attempts.

## Native scope

| Module | All theorem constants | Private | Registered public | Other native public |
|---|---:|---:|---:|---:|
| `FiniteMemoryCheckWitness` | 9 | 4 | 4 | 1 |
| `FiniteMemoryPolicy` | 3 | 0 | 0 | 3 |
| `FiniteMemorySeparation` | 22 | 4 | 6 | 12 |
| `FiniteSupportFixedPoint` | 31 | 12 | 15 | 4 |
| `SupportMemoryCheck` | 5 | 1 | 3 | 1 |
| `SupportMemoryController` | 12 | 1 | 7 | 4 |

Every declared new type underwent the actual complete 4237-entry prior-registry comparison and all 595 new-new comparisons; no raw stored-type definitional collision was reported.

All 47 registered direct proof dependencies were independently reconstructed as actual proof-value constants intersected with the immutable prior and new public registries.

The actual exporter was reconstructed byte-for-byte from the immutable renderer and registry. The second executed verifier was reconstructed byte-for-byte by freezing exactly the first-pass edges and 82-constant census.

## Registration boundary

The unchanged raw candidate is acceptable as the input to the reviewed metadata-registration procedure. Raw status remains PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION; this separate review supplies the independent acceptance.

Proceed with the reviewed check-only registration and exact metadata registration for this raw overlay and frozen source. Registration must preserve native artifacts and add only the reviewed metadata/provenance fields. This receipt does not itself perform registration.

The original native `STATUS.json` remains `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`; its hash and all 25 transferred proof/protocol files are recorded in the JSON review. The native source preflight also retains its original preparation-time `PENDING_ACTUAL_NATIVE_EXECUTION` value.

## Limits

- The raw stored-type comparison uses fresh elaboration for each Meta.isDefEq check while retaining stored universe names; it is not a decision procedure for all logical equivalence or mathematical novelty.
- The 47 edges are the specified direct registered theorem constants of proof values; they are not a claim that all mathematical assumptions or all transitive dependencies have been compressed into generators.
- This is a review of transferred actual compiler evidence and hash-bound checking code, not a second independent execution of the Mac toolchain.
- Live consumer/DAG registration, final FKRG/parser/base-policy checks, Git-object publication and resulting-main acceptance remain later gates.
- The new controller/checker retains exact-source hypotheses and noncomputable action choice; no physical-safety theorem, general-memory infinite-path identity, complexity bound, or stronger global closure is asserted.
