# Actual native02 dependency review of the revised safety witness

**Status: `ACTUAL_NATIVE_DEPENDENCIES_CLEAR_REGISTRATION_PENDING`.**

Reviewer: `/root/c3_executable_search`, independently of the witness author.
This is a new execution-bound supplement to [the source review](REVIEW.md).
It does not rewrite that review's earlier pending state. The complete native
protocol and execution-archive review is separately authored by
`/root/finite_window_source`.

The actual imported evidence is under
`/workspace/scratch/534b0448126c/tmp/core-path-realization-20261022/mac-import-01`.
The [machine-readable receipt](NATIVE_02_DEPENDENCY_REVIEW.json), SHA-256
`8b9b8780f4dcfac7f6c740536f40e2cdef1e7c506e25606d3e4b39aef71c5a0e`,
binds every input and the [executed read-only checker](check_native02_dependencies.py).

## Source and execution identity

| Item | Actual value |
|---|---|
| Immutable baseline | `d503586107974c56e0773b4ea106b41a7d144b43` |
| Complete source fingerprint | `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379` |
| Revised witness SHA-256 | `08060447a92c3b129351b95615ed2e1b3214e12e9ded21c638d0c6554c400c88` |
| Full-build02 receipt SHA-256 | `142c7f832a3d9cd9a012abf38a3bc748ae75f01a94c09f9296da40a5378658d7` |
| Native JSON SHA-256 | `61dabee5113b7fd2e640971c55ef6d2dba91e257744f587b57235f94a73b3308` |
| Raw overlay SHA-256 | `e87a8b9a921e4f9014d59f761ed73c8432c869f354e3b498542d99133a84239a` |
| Fixed verifier SHA-256 | `430aae70eec2c7cf87530020e24a8e43beae7021e2f8282f4c0c9b2949195714` |
| Both raw log SHA-256 values | `69d1e0ab5717a16608296b4396d3340bccedf8248be8ae270ceee1cd5a7d49f4` |

The actual exporter and fixed verifier exited `0` in `58.451` and `58.297`
seconds respectively. I compared the complete raw log bytes, decoded both
exports independently, and checked equality with both recorded native JSON
objects. The current source bytes agree with the frozen witness identity.

The observed audit contains **249 owned theorem constants**: 73 public source
candidates, 51 private constants and 125 other generated public constants.
All seven physical owners are represented. Every observed axiom set is
contained in `propext`, `Classical.choice`, and `Quot.sound`. Public stored
types, universe parameters, owners and direct constants agree with their
corresponding complete-owned rows.

The new public comparison run records `311856` cross comparisons and `2628`
internal comparisons, with an empty collision list. The public source graph
contains 114 direct registered edges. These are values from the complete
actual export, not source-parser predictions.

## All five private facts are real proof dependencies

The compiler reports one actual private constant for each original mass
calculation, owned by `FiniteMemorySafetyWitness`. All five occur directly in
both the public theorem's `direct_constants` and its complete-owned
`direct_theorem_constants`:

| Private calculation | Actual further proof dependency |
|---|---|
| `safe_source_all_times_mass_one` | `FiniteMemoryPhysicalSafety.controller_all_times_physical_safe` and the original initial, closure and occupancy facts |
| `unsafe_transition_time_one_mass_zero` | Actual coordinate-mass identity and the actual successor-support theorem |
| `unsafe_transition_all_times_mass_zero` | Its own time-one mass-zero calculation and the all-times-to-coordinate inclusion |
| `unsafe_initial_time_zero_mass_zero` | The actual coordinate-mass identity and its generated simplification proof |
| `unsafe_initial_all_times_mass_zero` | Its own time-zero mass-zero calculation and the all-times-to-coordinate inclusion |

All five have exactly the standard three-axiom closure. The receipt preserves
their complete compiled names, owners, universe parameters, stored-type
hashes and actual UEOT proof dependencies. The witness module has 16 owned
theorem constants, eight of them private.

The new public `physical_safety_premises_independent` has four registered
direct source edges: `safe_is_proper_nonempty`, `all_rows_zero_uncovered`,
`initial_false_safe`, and `source_false_preserves_safe`. Its private
dependencies are present in the full native audit and are not falsely
presented as registered public edges. The direct private proof path confirms
the source review's claim that the five original mass facts are used by the
public conjunction; the source review separately establishes their public
projections and the meaning of the two premise counterexamples.

## Scope and remaining integration

The five calculations remain outside the new public pairwise comparison
domain. This review does not claim that their former individual public
comparisons completed, and it does not reinterpret the interrupted native01
or its diagnostic as a PASS. Their complete private ownership, standard
axioms and real proof use have now been independently checked in actual
native02 evidence.

At this checkpoint, final registration and the live eleven-layer consumer,
clone and FKRG gates remain separate pending actions. The unchanged 89-test
parser result is reused. The existing ten overlay artifacts, old fixed
certificates, 68-row clone table and frozen scientific classifications are
unchanged by this review.
