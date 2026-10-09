# UEOT UMC R0–R3 local scientific checkpoint — 2026-10-09

## Scope and identity

- Current research lane: `compression/theory-completion-unified-local`.
- Frozen reference main: `6fa4c39d2a41f1563ba75c277b7112b61b2799db`.
- Canonical v3 theory file: `UEOT_Core_Mathematics_v3.0_Complete.md`; pinned SHA-256 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`. The separately available user-provided file matched that pinned hash in this session; the canonical source was **not** copied into or rewritten within the repository.
- This checkpoint is **local, uncounted Track TC research**. Core 106/106, the four counted Compression generators, and P12 `PARTIAL / EXPLICIT BOUNDARY` remain frozen.
- No cloud push, PR creation, modification of counted ledgers, branch deletion, or cleanup of pre-existing untracked research caches.

## R0 — source-exact evidence

The older `UMC_GLOBAL_MODULE_DAG_V3.json` and `UMC_LOCAL_EXACT_HEAD_AUDIT_V3.json` remain as historical receipts (618/22 at their actual capture time).

The updated graph builder now writes `UMC_GLOBAL_MODULE_DAG_V4.json` with a deterministic SHA-256 of every source module's name and bytes. The local audit now writes `UMC_LOCAL_EXACT_HEAD_AUDIT_V4.json` and refuses a stale inventory, differing module set, missing import, differing source hash, or wrong UMC subtree count.

Do not put a self-referential Git HEAD SHA into a committed receipt; record the verified exact HEAD in the command output and final checkpoint report.

## R1 — actual semantic audit initiated, NOT completed

New repeatable seed `seed_core_106_semantic_review.py` produces `UMC_CORE_106_SEMANTIC_REVIEW_V1.json` without modifying the frozen ledger or pretending symbol presence is scientific validation.

- 106 counted P-ID records present.
- Four **preliminary contract alignments**: P-PER-03, P-CTL-01, P-QUO-01, P-ALG-01.
- 102 remaining P-IDs remain `NOT_REVIEWED`.
- Even the four preliminary entries are not certified as fully semantically matched: all retain a named assumption/domain/source correspondence question.

The next R1 pass must compare the canonical text line-by-line against fully elaborated Lean types, intermediate proof dependencies, measurable assumptions, action spaces, and scope, before assigning any independent PASS.

## R2 — finite predictive probe extraction, with explicit no-go

New module `FinitePredictiveProbeCompleteness.lean`:

- `finite_family_has_complete_separating_probes`: any finite family `X → W → ℝ` can be distinguished by finitely many inputs `W` exactly as its full functions can; no finite observation horizon bound is claimed.
- `exists_finite_complete_stochastic_future_probes`: apply this to the actual `stochasticFuture K read` with a single finite set of future action/observation words.
- `finite_predictive_separation_does_not_force_markov_quotient`: use the existing six-state stochastic trace no-go to prove that finite predictive distinguishing tests can coexist with failure of StrongLumpability.

New mathematical consequence: finite test *existence* for finite source state families. This is not yet a computable efficient selector with horizon/conditioning guarantees; pairwise distinction does not imply linear indicator spanning or a quotient.

## R3 — source-derived safety-constrained discounted optimality

New module `SafeOptimalControlFromViability.lean`:

- `viableSourceAction`: state-dependent subtype of **original** source actions, with no restriction outside K and a PMF-support viability restriction inside K.
- `exists_viable_source_action`: from a real fixed point `viabilityStep P K=K`, derive availability of admissible actions for every state. There is no externally supplied safe controller.
- `viableRestrictedModel`: inherit the exact source transitions, bounded source rewards, and discount on these actions.
- `viable_restricted_greedy_preserves_source_kernel`: the restricted Bellman greedy action preserves K.
- `viable_restricted_optimal_dominates_all_causal_policies`: invoke the frozen causal discounted theorem for every history-dependent randomized policy respecting this action type.

New module `SafeRewardConflictWitness.lean`:

- `conflictRewardControl`: reuse the existing four-microstate, two-action, non-Dirac `survivalMicroKernel` with **nonzero** reward favoring the unsafe action.
- `conflict_same_source_reward_and_risk`: precise per-action reward and next-state probability computations.
- `conflict_region_is_actual_pmf_viability_fixed`: the nonempty visible-true set is a real PMF viability fixed point for the same source.
- `conflict_nonzero_reward_safe_bellman_preserves`: certify the constrained Bellman greedy source action remains safe for all visible-true microstates.

Critical boundary: the guaranteed optimum is relative to the **derived admissible-safe action set**, NOT an unrestricted GOD optimum. No numerical unconstrained-vs-constrained optimal-value gap, self-programmed goal, program repair, constitutive Ω-loop, or empirical performance improvement is claimed.

## Repeatable acceptance

Run from repository root:

```bash
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/build_umc_global_map.py
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/validate_unified_closure.py --repo-root .
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/test_validate_unified_closure.py
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/audit_umc_local.py --full
cd formalization/ueot-core && lake build UEOT
```

Root imports include the three new proofs. The exact module/theorem totals and new source fingerprint are in the V4 reports. Local `#print axioms` must contain only `propext`, `Classical.choice`, `Quot.sound`, or none; proof escapes forbidden.

## Next mathematical proof obligations

1. **R2.2:** establish explicit finite probe bound and constructive selection / linear independence or rank-conditioned robust-class guarantees, with near-singular counterexamples.
2. **R3.2:** identify every constrained causal policy of the source with a policy over the restricted action subtype; prove its exact reward/path/value fidelity. Then prove or refute a strict unrestricted-vs-restricted optimum difference on the nonzero witness.
3. **R4.1:** reuse CrossTrack constitutive persistence and the P12 synthesis no-go; build one actual resource-consumption, damage, program production and repair kernel with a legitimate nonempty self-maintaining fixed domain. Controller copied unchanged does **not** count as self-repair.
4. **R1:** independently validate 106 source propositions instead of upgrading the four preliminary comparisons into FULL prematurely.

**Overall claim:** local R0 complete after exact report validation; R1 initiated; R2/R3 first compile-checked finite theorems proved; full UEOT physical/mathematical closure NOT ESTABLISHED.
