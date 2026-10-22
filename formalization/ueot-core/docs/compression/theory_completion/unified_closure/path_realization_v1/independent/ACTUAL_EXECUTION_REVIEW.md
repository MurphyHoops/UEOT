# Independent review of actual path-realization execution

**Decision: CLEAR for frozen02 full-build02, the complete native02 two-pass execution,
and exact preservation of its execution/archive bytes.** Metadata registration,
live consumer integration, canonical audit and publication are separate gates.

Reviewer: `/root/finite_window_source`. Review date: 2026-10-22.
The [companion JSON](ACTUAL_EXECUTION_REVIEW.json), SHA-256
`89697625b9aa110791da53332ba02714191c30b5accf239f5380242076529fbf`, records exact source, protocol, artifact and review identities.

## Independence and exact reviewed scope

The reviewer did not run a Mac command, Lean, Lake, the native protocol, or
registration. The actual execution coordinator was `/root`; the new protocol
was authored by `/root/finite_memory_realization` and independently reviewed
by `/root/c3_executable_search`. This reviewer authored `SameSourceFiniteWindow`
and `FiniteWindowDoob`. Consequently this is an independent execution/evidence
review, not a claim of independent mathematical authorship review of those two
modules. Their separate [source review](FINITE_WINDOW_SOURCE_REVIEW.md) remains
part of the evidence, together with the independently reviewed memory, C3,
Doob witness, public API revision and semantic reuse records.

| Binding | Exact value |
|---|---|
| Accepted integration baseline | `d503586107974c56e0773b4ea106b41a7d144b43` |
| Frozen manifest 02 SHA-256 | `aeb36dad76ffbff5e8900b522a89950634c1e09c59fec8f4f01d0b7e05af44d3` |
| Complete source fingerprint | `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379` |
| Complete production modules | 691 |
| New physical source modules | 7 |
| Actual public source theorem candidates | 73 |
| Previously registered public theorem names | 4,272 |
| Current lexical hint groups / pairs | 25 / 61 |

I recomputed the complete module-name/NUL/source-bytes/NUL fingerprint from all
691 current production sources. Every recorded source-file length and hash
matches the accepted build identity. The exact historical consumer was loaded
from the baseline Git object, yielding 684 modules, 4,272 public names and ten
prior overlays. The unchanged parser rederived the new public-name set and
hints. Every old Lean source matches the baseline except the allowed import-only
extension of `TheoryCompletion.lean`; the added source set is exactly the seven
frozen modules. The five protocol source files retain their manifest01 hashes.

## Actual complete build and both native executions

| Execution | Actual exit | Elapsed time | Evidence |
|---|---:|---:|---|
| `lake build UEOT`, full-build02 | 0 | 14.230 s | [Receipt](../actual-execution/full-build-02/FULL_BUILD_RECEIPT.json), [raw log](../actual-execution/full-build-02/full-build.log) |
| Initial native exporter | 0 | 58.451 s | [Raw log](../actual-execution/native-02/native_export.log) |
| Fixed-edge native verifier | 0 | 58.297 s | [Raw log](../actual-execution/native-02/fixed_verifier.log) |

The actual build receipt SHA-256 is
`142c7f832a3d9cd9a012abf38a3bc748ae75f01a94c09f9296da40a5378658d7`.
Its 403,257-byte raw log has SHA-256
`cee7bac0fd4a65b69427bc2c5d7aa0d042b460bf544295020ff0e6a9755a2669`
and ends with the successful 9,397-job build marker. It retains replayed
warnings and records the actual rebuild of the revised safety witness and
import roots. This was an actual incremental Lake build; it is not described
as a clean-room or no-cache rebuild.

The receipt binds Lean 4.33.1 and Lake 5.0.0-src+819816b from the same actual
toolchain directory, with binary hashes and empty recorded Lean import
environment overrides. I checked the environment-file identities and all
nine clean dependency revision records against the unchanged identity helper.
The archived execution code checks this complete identity before and after
the build and each native execution. Successful raw records bind those checks
to this source and runtime; the review did not substitute a source-only scan
or a previous build receipt.

The two 763,143-byte native logs are byte-identical, SHA-256
`69d1e0ab5717a16608296b4396d3340bccedf8248be8ae270ceee1cd5a7d49f4`.
I independently extracted their single complete JSON markers. Both objects
are identical to `observed_first_native.json` and the final complete native
export. Those two 952,613-byte export files are also byte-identical, SHA-256
`61dabee5113b7fd2e640971c55ef6d2dba91e257744f587b57235f94a73b3308`.
This comparison covers all fields, not an abbreviated census.

## Actual ownership, public-type comparisons and proof edges

| Physical source module | Public source candidates | All owned native theorem constants |
|---|---:|---:|
| `C3ExecutableSearch` | 16 | 58 |
| `FiniteMemoryPhysicalSafety` | 8 | 13 |
| `FiniteMemoryRealization` | 7 | 17 |
| `FiniteMemorySafetyWitness` | 5 | 16 |
| `FiniteWindowDoob` | 9 | 34 |
| `FiniteWindowDoobWitness` | 14 | 59 |
| `SameSourceFiniteWindow` | 14 | 52 |
| **Total** | **73** | **249** |

The 249-constant census contains **51 private constants**, **73 confirmed
public source candidates** and **125 other nonprivate native theorem
constants**. It retains compiler-generated constants. Every public candidate
has the expected physical owner, is nonprivate, and matches its full-census
stored type, universe parameters and proof constants. Each transitive axiom
set is a subset of `propext`, `Classical.choice`, and `Quot.sound`; no
nonstandard axiom was observed.

Both actual executions completed **311,856 cross-layer comparisons**
(`73 × 4,272`) and **2,628 new-public pairwise comparisons**
(`73 × 72 / 2`), with zero observed stored-type collisions. Historical repair
count is zero; the unchanged prior scan covers all 4,272 registered theorems.
These are the protocol's raw stored-type `Meta.isDefEq` checks, not a general
logical-equivalence or semantic-novelty decision.

I regenerated the initial Lean exporter from the exact immutable registry,
source candidates and accepted renderer and obtained identical bytes. I then
reconstructed the fixed verifier from the first actual export's proof-value
dependencies and its observed census. It too is byte-identical to the executed
second source, SHA-256
`430aae70eec2c7cf87530020e24a8e43beae7021e2f8282f4c0c9b2949195714`.
Every public dependency list equals the actual direct proof constants
intersected with all prior and new registered public names, excluding the
source itself. The raw overlay contains exactly **114 registered direct
edges**, in agreement with those lists and the fixed-edge replay.

The raw overlay SHA-256 is
`e87a8b9a921e4f9014d59f761ed73c8432c869f354e3b498542d99133a84239a`.
Its public metadata, source overrides, census, verifier and native-export
hashes, complete execution records and build-receipt binding match the
independently recomputed values. It still has no registration-added keys.

## Revised safety endpoint: all five private facts are actually consumed

The public theorem `FiniteMemorySafetyWitness.physical_safety_premises_independent`
is compiler-confirmed. Its `direct_constants` and the matching full-census
`direct_theorem_constants` include all five actual private constants:

- `safe_source_all_times_mass_one`;
- `unsafe_transition_time_one_mass_zero`;
- `unsafe_transition_all_times_mass_zero`;
- `unsafe_initial_time_zero_mass_zero`;
- `unsafe_initial_all_times_mass_zero`.

Each has physical owner `FiniteMemorySafetyWitness`, `is_private = true`, a
retained stored type and proof-constant record, and only the standard three
axioms. None was dropped from the native audit. The companion JSON records
the full compiler private names. The separate [specialized dependency
review](memory-api-revision-02/NATIVE_02_DEPENDENCY_REVIEW.md) independently
confirms these same facts and the positive/negative consumers.

The [API revision review](memory-api-revision-02/REVIEW.md) and
[semantic supplement](TYPED_REUSE_SOURCE_REVIEW_REVISION_02.md) explain the
mathematical change: one public conjunction retains the original five mass
facts as projections, states each source's own zero occupancy and relevant
physical premise, and proves the explicit failure of the other physical
premise. The five private statement/proof bodies are preserved. Public raw-type
comparison scope therefore changed from 77 to 73. The unchanged comparison
algorithm completed the new scope; this review does not claim it completed
the former scope.

## Historical failure, diagnostics and cache qualifications remain intact

The first frozen source was
`c344bf6657ab31a32c46fba9feff6d5c04846b8f061d444aec8accb4994ad41b`,
with 77 public candidates. Its full-build01 passed in 30.553 seconds. Its
native01 first execution was interrupted for excessive actual resource use;
the retained native receipt records exit **130**, **798.761 seconds**, an empty
native log and state **FAILED**. No complete native JSON or fixed replay was
produced for that attempt. The process observation and interruption record
remain separately archived.

I streamed and hashed the lossless compressed diagnostic originals. The
52,296,728-byte runtime sample recovers SHA-256
`c33dbc209d6006eb7e77c409a817a31e86d1722dbb77564495942f8e04302ae5`.
The 129,525,390-byte progress log recovers SHA-256
`46eb243aced9a6757864eea0b729007f3db8184208e09dc4c40b76a0ce58cb1c`.
Its actual completed records are 328,944 cross comparisons and 2,065 internal
comparisons, with no equality reported among those completed records. The
last entered internal pair did not finish. The separately reversed isolated
pair was also interrupted after approximately 25 seconds. Neither diagnostic
decides that pair or supplies complete acceptance for the former 77-public set.

All ten focused attempt receipts retain their original status: attempts
01–08 are whole-batch FAIL; 09 and 10 are PASS. I checked every retained
focused result's source snapshot and log hash. Some individual modules had
already succeeded inside failed batches. In particular, compile08's later
Doob/witness successes followed a failed Window compile and used the prior
accepted dependency cache; they did not close the revised chain. The sequential
compile09 pass and the final full-build02/native02 evidence are separate.

`SOURCE_PREFLIGHT.json` still says `PENDING_ACTUAL_NATIVE_EXECUTION`, and the
native02 raw status still says `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`.
These original records are not rewritten by this independent CLEAR. Both
frozen manifests and both audit-preparation records are retained.

## Transport, executed protocol and repository archive

I independently decoded all 19 transport parts, verified their hashes,
decompressed the complete payload, and compared all **149 imported files**
(**9,377,318 bytes**) with their exported exact bytes. Payload SHA-256:
`860e1ff082994c2d545a8ea326f2e672d47ac84d9fcd1f0826e861db885cd95d`.
I then checked all **171 repository archive records**, including the actual
files, tool observations, original failed launch, import receipt and transport
drivers: each archived length, hash and byte sequence equals its reviewed
source. The [archive manifest](../actual-execution/import-01/ARCHIVE_MANIFEST.json)
has SHA-256
`347a9b751491240b0c0354fcf8dff8afb8c0c796eca66e87fb53db9a66066e33`.

For full-build02 and native02, the original delegated driver equals its
baseline Git bytes. The wrapper, adapter and frozen-manifest copies equal the
manifest-bound inputs. Applying the recorded single full-build substitution
and four native substitutions to the immutable originals reproduces the
complete archived executed Python bytes. No gate was removed. I also verified
all consumed immutable helper hashes and the predecessor overlay binding.

## Canonical wrapper and remaining gates

The new canonical wrapper has SHA-256
`f6dda475d5518ebf1e325fde43050e147e16f7b3c73d07bf948255c682796725`.
It differs from the accepted predecessor only in the module assertion
`684 → 691`. The actual `audit_umc_local.py` remains byte-identical to the
baseline, SHA-256
`7acc030d2607cd2afbcea00a5967a542cee34f7bb3ce897adca2c7761fd87c48`.
The original `--full` command, complete identity checks before/after,
raw command/log/exit/time retention and `NOT_ESTABLISHED` requirement remain.
This is static wrapper clearance; actual canonical execution is a separate gate.

No blocker remains in the reviewed actual build/native/archive scope. The
coordinator may now proceed to the separately authorized metadata registration
and live consumer integration. Full-current clone/FKRG checks, actual canonical
audit, Git-object preflight, CI and resulting-main/publication verification
remain independently evidenced obligations. This review changes neither the
frozen counted ledger nor global mathematical closure: counted impact is
`NONE`, and scientific closure remains `NOT_ESTABLISHED`.
