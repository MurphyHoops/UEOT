# Finite-Horizon Risk: Source and Boundary Audit

Date: 2026-10-19. Scope: five additive UnifiedClosure modules and their public imports.
Independent mathematical source review: **PASS** for the source hashes below.
Canonical local build and native axiom audit: **PASS** for these exact sources.
Remote integration evidence is tracked by the final PR and recovery issues.
This extension consumes existing proof infrastructure; it does not add a counted
generator, alter the 106-P-ID coverage ledger, or close every scientific port.

## 1. Mathematical contract

Let `X`, `Y`, and `A` be finite state, represented-state, and action types.
Fix a representation `q : X → Y`, initial law `p₀ : PMF X`, actual transition
rows `P n x a : PMF X`, and normalized reference rows `Q n y a : PMF Y`.
Both processes use the same causal policy
`π n : CausalHistory Y (A × Y) n → PMF A`.
The reference starts from exactly `p₀.map q`.

For a chosen finite horizon `T`, assume, for every `n < T`, `x`, and `a`,

\[
0\leq\varepsilon_n\leq1,\qquad
\operatorname{TV}\bigl(q_*P_n(x,a),Q_n(qx,a)\bigr)\leq\varepsilon_n.
\]

Write `Actual_T` for the pushforward of the **microscopic causal path law**,
retaining the initial represented state and every action/next-state record.
Write `Reference_T` for the reference causal path law under that same policy.
The proved bounds are

\[
\operatorname{TV}(\mathrm{Actual}_T,\mathrm{Reference}_T)
\leq B_T:=1-\prod_{n<T}(1-\varepsilon_n)
\leq\sum_{n<T}\varepsilon_n.
\]

For any measurable represented-history event `F`, the failure endpoint gives

\[
\mathrm{Actual}_T(F)\leq
\min\{1,\mathrm{Reference}_T(F)+B_T\}.
\]

These assumptions cover all states and actions before `T`, not only sampled
or visited rows. They impose no independence of successive deployment steps
and no row assumptions after `T`. “Actual” denotes the declared microscopic
PMF model; identifying it with a physical system remains an application task.

## 2. Why this is the actual projected law

`riskFiberPosterior` conditions the actual microscopic history PMF on the
observed history. Its support theorem identifies the observation fibre and
the original support; normalization is inherited from `PMF.filter`.
The positive-mass identity `risk_map_mul_fiberPosterior` reconstructs the
original joint mass. On a null observation fibre, `riskConditionedRow` uses
the reference row; the zero-weight identity proves this choice does not
change the pushforward law.

`risk_causalLaw_map` proves the resulting history-kernel law equals the
pushforward of the microscopic causal law at every horizon. The construction
retains history dependence; approximate row agreement does not assert an
exact Markov quotient. `risk_same_policy_row_tv` uses identical conditional
action weights on both sides. The microscopic controller is defined by the
projected history and cannot use additional hidden-state information.

`finite_horizon_path_error` extends the compared kernels identically after
`T`, proves the finite law unchanged, and calls the existing
`UEOT.V3.PathError.p_dyn_03_finite_path_error`.
It does not assume the desired survival recurrence or duplicate that proof.

## 3. Source map and public endpoints

Except for the nested `AbsorbingLeakage` namespace, all new declarations are
under `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure`.

| Source | Principal role and endpoints |
| --- | --- |
| [FinitePMFProjection.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FinitePMFProjection.lean) | `riskFiberPosterior_support`, `risk_map_extend_eq`, `risk_conditionedRow_tv_le`: finite disintegration and mixture bounds. |
| [FiniteHorizonPathAdapter.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteHorizonPathAdapter.lean) | `causalLaw_congr_before`, `finite_horizon_path_error`: finite-prefix adapter to frozen P-DYN-03. |
| [CalibratedRiskRows.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CalibratedRiskRows.lean) | `finiteKernelRowPMF_map_toReal`, `calibrated_pmf_tv_budget`, `calibrated_observable_partition_tv_budget`: actual kernel mass and calibrated row budgets. |
| [FiniteHorizonRisk.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteHorizonRisk.lean) | `risk_causalLaw_map`; the projected, coordinate, and representative endpoint pairs below. |
| [AbsorbingLeakage.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/AbsorbingLeakage.lean) | `row_tv_eq`, `failure_mass_closed`, `bounded_row_error_with_asymptotic_failure`: actual PMF negative control. |

The endpoint pairs are `same_policy_projected_path_error` /
`same_policy_projected_failure_risk`, `same_policy_coordinate_path_error` /
`same_policy_coordinate_failure_risk`, and `calibrated_representative_path_error` /
`calibrated_representative_failure_risk`.
The coordinate pair consumes bounds on **true normalized PMF coordinates**;
its budget is `min 1 ((1 / 2) * ∑ y, Γ n y)`.
It does not itself estimate those coordinates or establish measurement coverage.

## 4. Calibration into a specified reference model

`finiteKernelRowPMF` uses the existing finite probability-row constructor.
Its pointwise and pushforward identities connect the PMF to the **same**
`modelAsFiniteKernel M` mass, including `massIntoClass`.
The coordinate-to-TV step reuses
`UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs`.
The chosen-partition step consumes existing SISC approximate-indicator and
model/kernel reconciliation theorems; it does not introduce a parallel kernel.

For a fixed chosen setoid `S`, the representative endpoints take the reachable
representation `qS` and an explicit section `r` satisfying `qS (r y) = y`.
They define `Q n y a = (P n (r y) a).map qS` from actual source rows.
The section identity proves `x` and `r (qS x)` lie in the same fibre, allowing
`calibrated_observable_partition_tv_budget` to establish the required row bound.

| Parameter | Required meaning at time `n < T` |
| --- | --- |
| `δ n` | Uniform error in reconstructing every chosen-class indicator from the tests, over every state. |
| `η n` | Uniform difference between measured test responses within each chosen fibre, for every action/test. |
| `ρ n` | Uniform error between each measured response and its true one-step test expectation, over every state/action/test. |
| `κ n` | Bound on the sum of absolute reconstruction coefficients for every target class. |

With `N` the number of represented classes, the resulting row budget is

\[
\varepsilon_n=\min\left\{1,\frac N2
\left(2\delta_n+(\eta_n+2\rho_n)\kappa_n\right)\right\}.
\]

The representative endpoints require nonnegative budgets and the displayed
uniform hypotheses before `T`, then compose the proved row bound with the
actual-path and event-transfer results. Here `κ` is coefficient conditioning,
not an additional error for an independently learned reference kernel.
The future-probe endpoints elsewhere in `CalibratedRiskRows` concern canonical
predictive classes; an arbitrary chosen partition requires its own indicator
reconstruction hypotheses. Pairwise test separation alone is insufficient.

## 5. Negative control and limits of the conclusion

`AbsorbingLeakage` constructs a normalized Bool PMF: `false` is safe, `true`
is absorbing failure, and a safe step leaks with probability `ε ∈ [0,1]`.
The initial PMF is `pure false`. Expanding actual `PMF.bind` derives the
recurrences and proves safe mass `(1 - ε)^n` and failed mass `1 - (1 - ε)^n`.
Against identity PMF rows, the row TV is exactly `ε` at the safe state and
zero at the failed state. For every fixed `ε > 0`, failed mass tends to one.
Thus a uniform small local TV budget cannot yield probability-one safety
at all times. This file proves actual row errors and failure marginals;
it does not separately instantiate the full causal-history path-TV equality.

- `F` is a represented-history event. A hidden microscopic failure needs a
  proved preimage identity or inclusion before applying the risk conclusion.
- The common policy and projected initial law are explicit premises of the
  construction; different policies or initial laws need additional error terms.
- The calibrated representative reference is specified by `r` and the actual
  source. An independently learned `Q̂` needs its own reference-calibration bound.
- Calibration assumptions are deterministic conditional hypotheses. No outer
  statistical confidence, data sampling theorem, or physical validation is supplied.
- The representation is fixed, and the guarantee is finite. These results do
  not establish C4 reference drift/contraction, all-time viability, GOA, or all
  C1–C7 scientific closures. A bound clipped to one may provide no useful margin.

## 6. Reviewed source pins and validation

The public TheoryCompletion root adds exactly the five imports in the source map.
The final main-source review also checked the four restored declaration-level
`letI` bindings; the proof bodies retain their original local instance meaning.

| Source | SHA-256 |
| --- | --- |
| `FinitePMFProjection.lean` | `0807f667e0473e9bc063b446add02d0d1e477e6dbbf1125f15245093acc1ccc2` |
| `FiniteHorizonPathAdapter.lean` | `001261ea8ac5e9277037ecb620aaf84a16b9604614577d6ba5ba7bed1ea5d84f` |
| `CalibratedRiskRows.lean` | `04e1a1915fa30f1e1df387074d62d36c2562c56cf8ccb411c4eeed50f5907ba7` |
| `AbsorbingLeakage.lean` | `31212ec53f321e485ce6e5738b04b9dfcef523c1f8118140d05b753286cf2dc5` |
| `FiniteHorizonRisk.lean` | `d39f58ddbc8a41edf0221bcbb875c294def320319230a7c113cb18765ad46f08` |

| Validation | Result for these exact integrated sources |
| --- | --- |
| Independent mathematical source review | PASS; contracts, actual-law identity, calibration composition, and negative-control scope checked. |
| Canonical Lean build | PASS: pinned Lean 4.33.1, `lake build UEOT.V3.Compression.TheoryCompletion` (9,107 tasks), then `lake build UEOT` (9,347 tasks), on the exact five source hashes above. |
| Native theorem provenance and transitive axiom audit | PASS: 48 public source theorems; all 75 compiled theorem constants from the five modules, including 8 private constants, use only the standard axiom allowlist. The fixed type/direct-edge certificate passed at SHA `8624de79f7bde2b2af5b1cafc65342d925b3ea4a753ba3f62f86207dcd5e37de`. |
| Required CI at final PR head | Separate integration gate, recorded by exact commit and run links in the final PR and live recovery issues #146 / #302. |
| Resulting-main validation after merge | Separate integration gate, recorded by the resulting main commit and run links in the same live records. |

The fixed certificate rechecked 73 registered direct theorem edges and produced
exactly the same native export as the initial pass. Its 183,216 cross and 1,128
internal comparisons found no collision under the existing raw-stored-type
`Meta.isDefEq` protocol. This is not exhaustive universe-renaming or mathematical
equivalence detection. The registered graph has 3,865 nodes and 4,968 direct
edges after this additive overlay; definitions and private/generated constants
are separately recorded by native inspection. A further compiler census of all
42 UnifiedClosure source modules passed for 345 theorem constants, including
11 private constants. Source-review evidence and build evidence are distinct.

Remote CI is recorded at the final commit and resulting-main identifiers in the
PR and live recovery issues, so this source document does not embed its own
future commit identity or turn a pre-merge local result into a main claim.
