# SISC N3 — registered causal candidate discovery without supplied transporter

**Date:** 2026-10-09. **Scope:** additive post-Core research on `research/sisc-local-20261008`, no modifications to frozen 106/106 or counted Compression generators.

## 1. Reuse-first repository audit

The following *pre-existing* formalizations were checked before this construction:

- `TheoryCompletion/InverseObjecthood/FiniteCandidateRecovery.lean`: exact selection of a strict finite unique risk minimizer under a sufficiently small simultaneous uniform estimation radius. Does **not** construct causal provenance or abstain on model noncoverage.
- `TheoryCompletion/InverseObjecthood/Identifiability.lean`: observational equivalence and identification of a scientific object *class* among valid candidates. It explicitly does **not** identify literal physical tokens solely from matching evidence.
- `TheoryCompletion/InverseObjecthood/NonIdentifiabilityBoundaries.lean`: multiple observationally indistinguishable candidates can make identity impossible.
- `TheoryCompletion/ScientificClosure/C2IntervalDecision.lean`: existing three-way `certified/rejected/ambiguous` scalar interval decision and proven soundness under one good event. This is directly reused, not reimplemented.
- `ScientificClosure/C3NestedSearch.lean`: least good index in a nested registered chain, not general causal successor discovery. No redundant replacement.
- `SISCFiniteStochasticQuotient.lean`: finite controlled normalized transition kernel; supplies actual post-action expected responses, consistent with the Core post-transition measurement convention.
- `SISCFiniteFormation.lean` and `SISCFormationIdentityBridge.lean`: one transported candidate forms given an externally supplied `tp`, plus uniqueness under local response gap. N3 does **not** take `tp` as input.

No new general theorem is claimed for external causal semantics or statistical concentration; these remain explicitly supplied contracts.

## 2. True risk directly from the lower stochastic mechanism

For source microstate x, action a, registered measurement coordinate j, kernel K, microstate response r(y,j), and candidate expected response R_c(j), define

`trueRisk(c) = Σ_j |Σ_y K_a(x,y) r(y,j) - R_c(j)|`.

This is a model-calculated post-action mismatch. The coordinate space is required to be **nonempty**, preventing the empty-protocol vacuity of the earlier SI-3 audit.

For each registered candidate c, accept the already defined C2 interval certificate `I_c` of risk, with separate estimation and drift radii. The scientific calibration obligation is

`∀ c∈registered, |I_c.estimate-trueRisk(c)| ≤ I_c.totalRadius`.

This is explicitly **not** inferred from K or from the mere existence of an interval certificate. It requires real measurement reliability evidence.

## 3. Candidate sets and the correct three-way decision

`possible = {c∈registered | causal(parent,c) ∧ C2(I_c, tolerance) ≠ rejected}`

`certified = {c∈registered | causal(parent,c) ∧ C2(I_c, tolerance) = certified}`.

The algorithm has **no selected parent transporter** and does not choose the first acceptable candidate. It returns

- **unique(c)** only if possible is exactly {c} **and** c has a C2-certified risk bound.
- **ambiguous** if possible is nonempty but the above full unique condition is not met. This includes two registered possible successors *or* one statistically undecided candidate.
- **uncovered** if possible is empty. This means only that the registered, causally admitted experimental model did not cover a compatible candidate. It does **not** imply that the physical object died, split or ceased to exist.

## 4. Formal soundness proven

`unique_resolution_sound`: conditional on simultaneous calibration, a `unique(c)` output yields that c is registered, causally allowed, truly risk-compatible, and **the only** registered causally allowed truly compatible candidate.

`uncovered_excludes_registered_truth`: under the same calibration, an uncovered result rules out any true compatible candidate **inside the declared registered causal family**, not outside it.

`two_compatible_force_nonunique`: two different genuinely compatible registered causal candidates contradict any claimed unique selection.

`two_possible_candidates_force_ambiguity`: two different merely possible candidates already force an *ambiguous* output, even if one is certified.

`undecided_singleton_force_ambiguity`: having exactly one possible candidate that is not certified does **not** license an identity decision.

`registered_candidate_risk_nonnegative`: the model risk is a finite sum of absolute deviations, so it is nonnegative.

These results reuse the existing C2 certificate soundness lemmas; the proof does not add new axioms or a pretend physical `SameObject` relation.

## 5. Why this is progress, and why it is not full Objecthood

Previous SI-3 uniqueness had an externally supplied `tp`; this finite method **scans the whole registered finite candidate set**, combines independent declared causal admissibility and interval decision evidence, and produces a sound abstaining outcome. It bridges measured post-action stochastic expected response to *operational successor identification*.

However, `causal`, the candidate registration, emission response maps, and interval calibration still need independently verified data. The theorem does not infer the physical edge from the observation map, prove the candidate universe complete with respect to nature, or derive boundary/repair/viability/GOD/GOA conditions. It also works on a finite expected response statistic, not the full distributional observation process unless such moments are experimentally sufficient.

Strongest justified label: **finite evidence-limited operational candidate resolver**, not ontic unique physical successor.

## 6. Future falsification and upgrading conditions

1. Construct concrete positive/ambiguous/uncovered examples with exact C2 intervals and exact kernel responses; compile them without admits/sorries.
2. Replace externally supplied `Calibrated` good event with a proven finite simultaneous confidence event using the repository's existing P-STAT concentration/schedule machinery, preserving dependent-data restrictions.
3. Extend from expectation vectors to distributions/controlled trace tests and robust class-indicator spanning; give a no-go whenever registered tests do not identify candidates.
4. Prove conditional stability over multiple time steps when independently registered causal edges can branch/merge; never force a singleton identity across actual splits.
5. Integrate formation, persistence, repair/viability only when independent mechanism and measurement assumptions are available.

**Governance:** local formal stage only; frozen Core untouched; external independent experiment HOLD; GitHub push HOLD.
