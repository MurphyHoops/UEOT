# UEOT unified closure R2/R3/R4 — Reuse-first proof checkpoint (2026-10-09)

## Repository and rules

- Research branch: `compression/theory-completion-unified-local`; parent checkpoint `d6ed828c1f792ddb195541fd4df49160515a7cd0`.
- Only additive modifications inside Track TC and its public import root. No frozen 106-P-ID counted ledgers, four compression generator records, P12 declarations, or other frozen modules changed.
- All following source claims refer to the indicated **existing Lean files**. No external empirical input is validated.
- Fully universal UEOT and scientific claims remain **NOT_ESTABLISHED**. Program-derived safe control does not prove that reward-optimal control is a program repairer.

## Mandatory reuse inventory (checked before proof coding)

| Already proven | Source Lean module | Reuse / NOT to redo |
|---|---|---|
| Finite *deterministic* future probes, cardinal <= |X|² | `ScientificClosure/SISCFiniteFutureProbes.lean` | Keep existing chooseSeparatingWord, finiteCompleteProbeFamily, finite_complete_probe_card_le; do not write a second deterministic proof |
| Minimal finite separating intervention subfamily | `CrossTrack/InteractionProbeSelection.lean` | Reuse exists_minimal_pairwiseSeparating_probeFamily if actual intervention semantics match; it does not by itself supply stochastic state-test rank |
| Stochastic trace identifiability without lumpability | `ScientificClosure/SISCStochasticTraceNoGo.lean` | Reuse six-state countermodel; never claim finite pairwise probes force a Markov kernel |
| Finite PMF viability and infinite survival laws | `ViabilitySource.lean`, `ViabilityTrajectory.lean` | No new independent viability fixed-point algorithm |
| State-dependent arbitrary causal randomized policy optimum | `FiniteDiscountedCausal*.lean`, `FiniteDiscountedGreedy.lean` | Reuse P-CTL-01 causal policy types, Bellman optimality, greedy attainment |
| Maximal finite controlled quotient viability | `UnifiedClosure/ViabilityKernelIntertwining.lean`, `CorePMFViabilityReconciliation.lean` | R3 does not rebuild PMF↔real-kernel identification |
| Physical repair and internal program executable semantics | `Objecthood/RepairLawSelfReconstruction/TrustedSubstrate.lean`, `ProgramSemantics.lean` | Preserve trusted interpreter/executor boundary |
| Triple redundancy and one-copy fault correction | `Objecthood/RepairLawSelfReconstruction/TripleRedundancy.lean` | Already proves exact one-replica restoration and two-replica collision no-go |
| Recovered repair program/controller & physical kernel | `Objecthood/RepairLawSelfReconstruction/JointRecovery.lean` | Reuse jointRepairKernel_restored and jointRepairKernel_staysIn_recoveredTarget |
| Recurrent fault path law under correctable-fibre envelope | `Objecthood/RepairLawSelfReconstruction/RecurrentFaultPathLaw.lean` | Faults preserving physical state and encoded program semantics leave recovered-step law unchanged; NOT arbitrary fault immunity |
| Explicit accounting and same-parent resource synthesis | `Objecthood/ResourceClosure/ResourceAccounting.lean`, `ResourceMaintenanceSynthesis.lean` | Resource costs are *abstract accounting units*, not experimentally identified thermodynamic quantities |
| Endogenous persistent controller & failure to auto-repair arbitrary corruption | `CrossTrack/EndogenousConstitutivePersistence.lean` | Do not replace by another copy-only controller state |

### Corrected interpretation of R4

The earlier high-level roadmap under-described **existing RLSR and resource-maintenance proofs**. Program redundancy, conditional joint restoration, trusted execution, recurrent fault path-law and explicit abstract cost accounting are **already in the library**. Therefore R4 is not a greenfield self-repair module. Remaining scientific gates are: independent physical realization and calibration of interpreter, codec, resource acquisition/replenishment; a single registered physically interpreted source that simultaneously validates these assumptions; fault envelopes beyond the guaranteed correctable fibre; and non-circular intrinsic goal provenance. Even a complete formal proof conditioned on TrustedRepairSubstrate cannot eliminate that trust by renaming the premise.

## New R2 result: actual finite stochastic probe cardinal

`UnifiedClosure/FinitePredictiveProbeCompleteness.lean` now contains `finite_family_has_quadratic_separating_probes` and `stochastic_future_complete_probes_card_le`:

For every finite source X and real stochastic future-response function on words, some fixed test Finset of cardinal at most (card X)^2 separates exactly the same states as all future words. The old `finite_family_has_complete_separating_probes` is now only a thin corollary of the stronger general lemma, **not duplicated**. The existing stochastic six-state non-lumpability rejection is preserved.

**Not proved**: a uniform *word-length* upper bound, efficient search, lower singular-value bound, statistical rank/indicator spanning, or stochastic Markov lumpability. Finite pairwise distinguishability does not discharge those conditions.

## New R3 result: arbitrary causal positive-path survival

`UnifiedClosure/SafeCausalHistoryTransport.lean` reuses the exact R3 viableSourceAction subtype and the **frozen CausalPolicy type**:

- `viable_action_positive_source_successor`: real source transition with positive mass under any admissible action cannot escape the actual PMF fixed region.
- `ViableCausalReachable`: positive-policy-probability + positive-real-transition histories of any causal memory type, with memory advancing using existing `CausalPolicy.advance`.
- `all_positive_causal_histories_preserve_viability`: inductive preservation for **every finite reachable memory**, no stationarity or deterministic policy restriction.
- `safe_causal_history_optimality_and_path_invariance`: combines the path invariant with the existing infinite discounted causal Bellman domination, restricted to safe actions.

This is a support/path theorem plus conditional optimality, **not** yet an independent measure-one infinite-path construction for arbitrary nonstationary policies or a source-unrestricted causal-policy equivalence.

## New R3/R4 bridge: repaired program -> same-source admissible action

`UnifiedClosure/RepairProgramSafeControlBridge.lean` imports existing RLSR JointRecovery and uses its actual program-validity interface, not a newly declared `safe=true` label:

- `recoveredProgramSourceSafeAction` maps an RLSR `RepairProgramValid T (M.transitionPMF) K r` to a source-derived `viableSourceAction M K x`.
- `reconstructed_program_source_kernel_agrees_with_safe_action` rewrites the **existing** recovered joint kernel via `jointRepairKernel_restored`, with original M transitions.
- `reconstructed_program_preserves_source_viability` gives support-level R3 safety for that actual decoded program.
- `reconstructed_program_joint_and_source_safety` combines source PMF closure with existing RLSR recovered joint-carrier closure.

No assumption that the valid repaired program attains the safe Bellman optimum. Program correctness and full scientific origin of the trusted substrate remain external requirements.

## Remaining high-value obligations (not theorem-count-driven)

1. **R3 gap:** characterize source causal policies assigning probability zero to unsafe actions, derive restriction/lift exactly and compare discounted values without assuming a policy already typed by the restricted subtype.
2. **R3 control conflict:** formally separate unrestricted optimal value from safe constrained value on the nonzero reward witness; previous one-step contrast alone is insufficient.
3. **R2 mathematical gap:** finite future test length / constructive selector / robustness and rank with proper stochastic counterexamples; reuse SISC deterministic/cardinality, existing stochastic nullspace and probe-selection primitives.
4. **R4 integration gap:** combine a *single* explicitly typed physical resource/process model with RLSR's trusted-program guarantees, original R3 source, stochastic damaged/reconstructed trajectory, and P6 accounts. No conflation of abstract budget and thermodynamics.
5. **R1 semantic provenance:** source-v3 canonical mathematical statement to elaborated Lean theorem contract, 102 completely unreviewed and 4 preliminary; no 106/106 semantic FULL claim.

## Build and epistemic acceptance

- New modules imported by `UEOT/V3/Compression/TheoryCompletion.lean`.
- All additions must pass local lake build, source-exact V4 graph validator, full UMC axiom check and negative-control governance.
- Existing contradictory toy/no-go theorems are retained and never silenced.
- Stage conclusion: **bounded finite stochastic probes proved, arbitrary causal positive-path viability proved, RLSR->R3 typed bridge proved; general scientific/physical closure NOT_ESTABLISHED**.
