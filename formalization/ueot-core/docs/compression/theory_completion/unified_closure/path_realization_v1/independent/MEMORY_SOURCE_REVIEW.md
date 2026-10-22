# Independent source review: actual finite-memory paths and physical safety

Review date: 2026-10-22. Reviewer: `/root/c3_executable_search`, independent of
the author `/root/finite_memory_realization`.

**Result: CLEAR for the reviewed mathematical statements, source construction,
and API scope.** This is a static source review. Actual Lean compilation,
compiler-native export, axiom closure, root-import integration, and publication
are separate gates owned by the release coordinator; this receipt does not
certify them. The physical-safety proof revision below was awaiting its
coordinator-run execution when reviewed.

## Reviewed source identities

Paths are relative to `formalization/ueot-core/`.

| File | SHA-256 |
|---|---|
| `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryRealization.lean` | `8306c376acbf26db8ae70a5064460c9e423da527a0c89efe4ec18e0e6150191f` |
| `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryPhysicalSafety.lean` | `7f231017ef32eb607c0187dc659a139101f92ee4ad2ed434f35d4f0687a46cdd` |
| `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemorySafetyWitness.lean` | `64f3c14471022b5b97330c06fe837f3f8f0f8b76bd6e22b81ab3fdd80b1d44dd` |
| `docs/compression/theory_completion/unified_closure/path_realization_v1/memory-realization/CONTRACT.md` | `8af7816091073d7b0fac5dd724b019599563f6093e49771a6dd39d355314cbe3` |

The initial physical-safety review read SHA
`b4b4702b02f66ac51bab10de38c54c6e24b02636b554a891513ee39d609bcaf8`.
The author subsequently revised only the local proof of
`stateTrajMeasure_coordinate_mass`: it now establishes the last coordinate of
the recursive-history equivalence and the last coordinate of the restricted
infinite path as separate equalities `hlast` and `hprefix`, then simplifies the
event preimages. I read that revision and checked the current SHA shown above.
Its declaration, premises, conclusion, and actual source are unchanged.

The review also checked the consumed definitions and theorem signatures in
`FiniteMemoryPolicy.lean`, `FiniteHorizonRisk.lean`,
`FiniteSupportViability.lean`, `SupportMemoryController.lean`,
`SameSourceInfinitePrefix.lean`, and `UEOT/V3/ViabilityPath.lean`.

## Source and timing checks

`augmentedInitial` is the pushforward of the original `p₀` by
`x ↦ (x, controller.initialMemory (q x))`. It neither selects a new initial
distribution nor conditions the original one on a safe set.

The accepted controller's memory recursion reads the initial observation,
selects the next action from the current memory, and then updates with the
recorded action and new observation. The new `augmentedRow` has exactly this
order: sample `a` from `controller.action m`; sample `z` from the actual
numeric row `P n x a`; return `(z, controller.update m a (q z))`.
`augmentHistory` replays those same recorded actions. This agrees with the
actual `riskMicroControlKernel` and the original `controller.policy`, including
unsupported histories where the controller remains total.

`actual_augmented_history_law` proves equality of complete history PMFs by
induction and a dependent map/bind identity. The new path-law agreement is a
conclusion, not an input field. `eraseMemory_augmentHistory` then preserves
the entire original state record, including time zero.

## Infinite-process and event checks

`sequenceTrajMeasure` constructs one Ionescu–Tulcea measure using the exact
time-indexed numeric row sequence. Its zero-prefix and successor-prefix
identities derive `state_history_eq_sequence_prefix`. Instantiating those rows
with `augmentedInitial` and `augmentedRow` therefore identifies every finite
prefix of the constructed infinite augmented law with the original finite
policy experiment.

`stateTrajMeasure` is the coordinatewise state projection of this same
augmented measure. `actual_state_prefix_eq` proves the complete state-prefix
identity, and `stateTrajMeasure_coordinate_mass` specializes it to actual
microscopic terminal events. No state-only Markov or lumpability condition is
silently introduced.

The type scope in the contract matches the code: finite PMF identities need
no finiteness or measurability; the infinite augmented law uses finite `X` and
`M` with measurable singletons; original action-history event-mass and support
arguments also require finite `A` with measurable singletons. Observations may
have arbitrary type. Actions can be erased by the augmentation, so events
depending on unrecoverable actions require a separate retained-action map;
the contract states this boundary.

## Physical-safety checks

The generic support argument retains three distinct premises: the original
initial support is physically safe; every certified actual transition from a
safe state has safe successor support; and the same policy's actual
deployment row law has zero uncertified occupancy at every time.

For each supported microscopic successor history, the proof obtains its
supported predecessor, actual selected action, and actual next-state support.
The existing `zero_uncovered_iff_support_certified` certifies that action at
the realized state. The independent physical closure premise then propagates
safety. This proves finite support safety before any infinite measure is
used.

`controller_all_times_physical_safe` transfers those actual coordinate masses
to the constructed infinite state law and consumes the existing countable
probability-one intersection theorem. It does not infer physical safety from
certification alone, positive finite survival, or QSD stabilization.

The support-controller consumer instantiates the theorem with the previously
constructed controller itself. Its exact source-support matching,
certification matching, and initial-winning premises discharge that
controller's zero occupancy through its existing theorem. Numeric transition
rows may still vary with time; fixed support is not turned into a fixed
numeric kernel or killed matrix. No finite-horizon selector is identified
with this controller, and no reference-process checking budget is reduced.

## Nonempty witnesses and boundaries

The witness has Boolean state, one memory, one action, constant observation,
and proper nonempty safe set `{false}`. Every row is certified, so actual
uncertified occupancy is zero in all three examples.

| Original initial state and source | Physical conclusion and responsibility |
|---|---|
| Start at `false`; each transition returns `false` | Both physical premises hold, and the actual all-times safe event has mass one. |
| Start at `false`; each transition returns `true` | Initial safety holds, but actual time-one safety and all-times safety have mass zero. Certified transition closure cannot be omitted. |
| Start at `true`; each transition returns `false` | Certified transition closure holds, but original time-zero safety and all-times safety have mass zero. Initial safety cannot be omitted, even with immediate repair. |

The negative masses use the proved actual coordinate identity and the support
of the original microscopic PMFs. They do not assume the desired event masses
as data. These examples test the physical premises; the accepted separate
memory-separation example retains responsibility for showing that memory can
increase control power.

## Decision and remaining gates

I found no mathematical/API blocker in the reviewed sources. The new bridge
constructs the missing actual infinite law and proves its source identities;
the physical endpoint uses its own policy and explicit physical premises.
The reviewed contract does not claim that a source audit is compilation or
that the new local result establishes global mathematical closure.

Actual compilation, axiom audit, independent execution receipts, public import
integration, source-derived DAG refresh, and compiler-certified reuse export
must be assessed from their own final-source records. Any later declaration
or source-construction change requires renewed review of the affected part.

## Supplemental review: witness proof elaboration and execution separation

The original hashes above remain the historical reviewed snapshots. I then
read the revised complete witness at SHA-256
`fcc011bd9c7571e9ae95e6df606baaf500e2f7767453be6788af5da470b934e7`.
The time-one zero-mass proof now binds the existing microscopic PMF to an
explicitly typed local `p` before applying its `toMeasure_apply_eq_zero_iff`.
The two all-times zero-mass proofs supply `zero_le` directly instead of
applying it as a function. No witness definition, theorem premise, theorem
conclusion, source identity, or event was changed. **The static CLEAR extends
to this proof-only revision.** Its successful Lean execution was still pending
when this supplement was written.

The current memory contract at SHA-256
`dbd21f25819793b7c8a1575a5c56dfc9c5f2f593798cbea8fa99a67e9d32bfec`
updates its execution-status paragraph to report the realization module's
successful focused execution and retains the earlier failed attempts.
The mathematical/API contract reviewed above is unchanged.

I also read the coordinator's unmodified `FOCUS_04_TOOL_OUTPUT.txt`. It records
actual focused success for `FiniteMemoryPhysicalSafety.lean` at reviewed SHA
`7f231017ef32eb607c0187dc659a139101f92ee4ad2ed434f35d4f0687a46cdd`,
exit code `0`, `3.7029871250000004` seconds, with an empty log. The same batch
records failure for the earlier witness SHA `64f3c144...`; that failure is not
relabelled as a pass. Successful execution of the revised witness, full build,
native export, axiom closure, and final integration remain separate records.

## Subsequent focused execution checkpoint

I independently read the coordinator's unmodified `FOCUS_05_TOOL_OUTPUT.txt`
(SHA-256
`2cce57cd4b3587ef05583d1fcdeab56f0ee68d622e722a572f29dab80df2f9b8`).
It records actual focused success for `FiniteMemorySafetyWitness.lean` at
the reviewed revision
`fcc011bd9c7571e9ae95e6df606baaf500e2f7767453be6788af5da470b934e7`,
exit code `0`, `3.8005266250000003` seconds, with an empty log whose SHA-256 is
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The current on-disk source has that exact hash. This resolves the witness's
focused-execution pending item at the earlier checkpoint; the earlier failed
attempt and its review history remain unchanged.

The updated memory contract at SHA-256
`4a0677545cae77df6f1aad306f489c8ab98fec33a0b7c88dd616a73bf5555051`
now records focused success for all three memory modules while retaining the
initial failed attempts. Its mathematical/API scope is unchanged. The combined
batch still contains failures in other work, so this witness receipt is not
reported as whole-batch or whole-library success. Full build, native ownership
and axiom audit, compiler-certified reuse registration, and final integration
remain independently evidenced gates.
