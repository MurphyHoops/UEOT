# Independent semantic review of the registered-interfaces reuse candidates

**Status: `SEMANTIC_CLEAR_NATIVE_PENDING`.** All 18 flagged declarations and all 39 candidate pairs have been reviewed against their actual source. No mathematical source change is required by these reuse hints. This is a semantic clearance; compiled type comparisons and native evidence remain pending.

## Evidence and exact scope

- Actual base: `65db00a12d20be41cd6c8befacb9ba2e74a2a8a9`.
- Candidate source commit: `c30aa219b90173ca15e0eb9878f244de363e1fc3`.
- PR preflight SHA256: `ac5ec378ef71525a0b780eb698a6293bb480f5d5ab639eb50ab3ea6ce48345db`; 52 new lexical public theorems, 18 flagged groups, 39 pairs.
- Complete identity receipt SHA256: `47b089acd78085c3d3ba4871d981f841064943cddde4487046f65a3addd638e1`.
- Complete source fingerprint: `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`; 666 modules.
- The individual files read below were rehashed against that complete identity. Existing mathematical and boundary reviews are reused; no Lean build, project test or native export was run by this review.
- The original preflight and its pending review fields are preserved. This separate receipt records the independent result.

## Classification

| Classification | Pairs | Meaning |
|---|---:|---|
| `EXISTING_THEOREM_REUSED` | 2 | The hinted theorem is actually called through a justified adapter. |
| `ADAPTER_OR_GENERALIZATION` | 16 | The relationship is real, but types, quantifiers or assumptions differ. |
| `DIFFERENT_PROPOSITION` | 21 | The hint does not identify a replacement for the new proposition. |

These categories are not a claim that the Lean kernel has checked definitional inequality. Only the actual native comparison can supply that separate result.

## Pair-by-pair findings

### R01 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.factorized_same_policy_path_error`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ArbitraryObservationRisk.lean`, declaration at line 39.

**`UEOT.V3.CoreOperationalAssembly.same_policy_path_error` — `DIFFERENT_PROPOSITION`.** Old CoreOperationalAssembly compares two finite controlled models under a stationary policy and a uniform row error, using a product bound. The new theorem permits a general causal history policy and arbitrary Y, factors live observations through a finite carrier, and bounds actual occupation-weighted additive row TV. The old theorem cannot replace these premises and this conclusion.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_path_error` — `EXISTING_THEOREM_REUSED`.** The proof directly applies coverage_same_policy_path_error to the finite Option I escape construction. escape_path_tv, escape_deployment_row_law and escape_transition_row_tv transport the conclusion back to the actual Y-valued reference, policy and deployment row law. This is explicit reuse of the existing finite theorem through a proved adapter.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_coordinate_path_error` — `DIFFERENT_PROPOSITION`.** same_policy_coordinate_path_error supplies a uniform coordinate-error/product estimate for a finite observation type. Its premises and coordinate metric differ from the actual occupation-weighted TV sum here.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_projected_path_error` — `DIFFERENT_PROPOSITION`.** same_policy_projected_path_error assumes a uniform row error in [0,1] and has a product conclusion. The new bound is an additive sum weighted by the actual deployment row law, without imposing finiteness on Y.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_certified_path_error` — `DIFFERENT_PROPOSITION`.** coverage_same_policy_certified_path_error adds a certification predicate and an uncovered-mass budget. Those are downstream budget assumptions; the new theorem is the underlying raw row-TV estimate and does not assume them.

### R02 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_certified_path_error`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ArbitraryObservationRisk.lean`, declaration at line 98.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_certified_path_error` — `ADAPTER_OR_GENERALIZATION`.** The old theorem requires Fintype Y. The new theorem retains the same actual uncovered occupation and certified-row budget but obtains the path comparison from the finite-carrier escape adapter. The proof reuses coverage_expected_error_le. An infinite Y cannot be passed directly to the old finite-Y endpoint.

### R03 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_microscopic_failure_risk`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ArbitraryObservationRisk.lean`, declaration at line 128.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_empirical_registered_microscopic_failure_risk` — `ADAPTER_OR_GENERALIZATION`.** The old empirical endpoint additionally packages fixed-N calibration and fit assumptions and obtains a finite-Y risk bound. The new theorem takes a sampling-independent certified row-TV premise, permits arbitrary Y, and requires measurable F explicitly. Empirical row calibration is reusable upstream; this old endpoint cannot replace the broader risk transfer.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_microscopic_failure_risk` — `ADAPTER_OR_GENERALIZATION`.** The finite-Y endpoint and the new endpoint express related event transfer, but the old environment supplies finite history measurability. The new theorem states MeasurableSet F explicitly and uses the arbitrary-Y path theorem. It reuses risk_microscopic_event_le_envelope and risk_event_transfer, preserving the same real Q experiment.

### R04 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_le_of_event_sub_le`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscape.lean`, declaration at line 29.

**`UEOT.V3.FiniteAlphabetConcentration.tvDist_le_of_finset_event_le` — `ADAPTER_OR_GENERALIZATION`.** The old finite-alphabet lemma uses absolute discrepancies over all finite sets. The new theorem works for arbitrary measurable observation spaces and signed forward discrepancies over measurable events; probability-measure complement identities supply the opposite sign. The finite-alphabet lemma does not remove its finite-type assumption.

**`UEOT.V3.AverageErrorTransport.expectation_le_of_tvDist_le` — `DIFFERENT_PROPOSITION`.** expectation_le_of_tvDist_le consumes a TV bound to bound the expectation of a [0,1]-valued observable. The new theorem constructs a TV bound from the family of all measurable-event inequalities.

**`UEOT.V3.StatisticalDefect.abs_tvDist_sub_tvDist_le` — `DIFFERENT_PROPOSITION`.** abs_tvDist_sub_tvDist_le is a perturbation inequality for two TV distances using four measures. It is not the event-supremum characterization proved here.

**`UEOT.V3.TotalVariation.tvEvent_le` — `DIFFERENT_PROPOSITION`.** tvEvent_le bounds one event discrepancy by TV. The new theorem proves the converse universal inference from all measurable-event inequalities, using tvEventSet_nonempty, the supremum bound and probability complements.

### R05 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.pmfExtend_apply_general`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscape.lean`, declaration at line 296.

**`UEOT.V3.PathError.pmfExtend_apply` — `ADAPTER_OR_GENERALIZATION`.** The atom formula agrees after imposing finiteness, but PathError.pmfExtend_apply requires finite history and next-state types. The new theorem removes these assumptions using PMF.bind_apply, PMF.map_apply and two tsum_eq_single reductions. It is needed for histories over arbitrary Y; finite support is not substituted for a Fintype instance.

### R06 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.live_injective`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscapeBoundary.lean`, declaration at line 22.

**`UEOT.V3.Compression.CrossTrack.BindingIsolation.injective` — `DIFFERENT_PROPOSITION`.** The new statement is injectivity of the explicit map Bool → Nat sending false to 0 and true to 2, discharged by the four cases. BindingIsolation.injective instead infers injectivity of a general map from a positive metric lower-bound certificate. It would require an additional metric/certificate construction and is not the same proposition.

### R07 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.references_encoded_tv_zero`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscapeBoundary.lean`, declaration at line 192.

**`CrooksJarzynski.MeasureProtocol.ContinuousTimeJump.Simplex.reference_ne_zero` — `DIFFERENT_PROPOSITION`.** The new statement says two explicitly encoded probability references have TV distance zero, using reference_encoded and tvDist_self_eq_zero. reference_ne_zero proves nonzero mass for a scaled continuous-time reference measure. The names are a heuristic false positive; no common theorem claim or missing reuse is indicated.

### R08 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.riskHistoryMap_comp_general`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PathObservationEscape.lean`, declaration at line 18.

**`UEOT.V3.DynamicsKernel.mapHistory_comp_appendHistory` — `DIFFERENT_PROPOSITION`.** The new recursive CausalHistory lemma states composition of maps on the initial record and every appended record. DynamicsKernel.mapHistory_comp_appendHistory states that one state map commutes with append in a different, Finset.Iic-indexed history representation. Neither the history type nor the identity is the same; the new induction is appropriate.

### R09 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_comp`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PathObservationEscape.lean`, declaration at line 55.

**`UEOT.V3.DynamicsKernel.mapHistory_comp_appendHistory` — `DIFFERENT_PROPOSITION`.** This theorem specializes riskHistoryMap_comp_general to observation maps preserving action coordinates. The old DynamicsKernel statement concerns append naturality in another history representation, rather than composition of two observation maps.

**`UEOT.V3.InformationPredictiveFactorization.compProd_map_historyGraph` — `DIFFERENT_PROPOSITION`.** compProd_map_historyGraph is a joint-measure/kernel graph embedding identity for an S-finite composition product. The new theorem is equality of concrete finite recursive histories; no composition-product law replaces it.

### R10 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.map_observationHistoryMap_comp`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PathObservationEscape.lean`, declaration at line 74.

**`UEOT.V3.DynamicsKernel.mapHistory_comp_appendHistory` — `DIFFERENT_PROPOSITION`.** The new theorem lifts observationHistoryMap_comp through PMF.map_comp. The old append-naturality identity has another history representation and does not assert PMF pushforward composition.

**`UEOT.V3.InformationPredictiveFactorization.compProd_map_historyGraph` — `DIFFERENT_PROPOSITION`.** The old historyGraph theorem concerns a measurable graph map and a kernel composition product. Here ordinary PMF pushforward functoriality and the preceding deterministic history-composition identity are the direct reusable primitives.

### R11 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_deployment_row_law`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PathObservationEscape.lean`, declaration at line 142.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PolicyPrefixCongruenceCheck.deployment_rowLaw_congr_through` — `ADAPTER_OR_GENERALIZATION`.** deployment_rowLaw_congr_through compares two policies in one fixed observation alphabet assuming prefix agreement. The escape theorem changes the observation alphabet between Y and Option I and proves equality after decoding actual microscopic histories. escape_micro_control_kernel and escapePolicy_actual_history justify the exact state/action PMF equality; fixed-alphabet congruence alone cannot type this adapter.

### R12 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_calibration_good_bad_le`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredJoint.lean`, declaration at line 51.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredGoodJointCheck.registered_calibration_good_bad_le` — `ADAPTER_OR_GENERALIZATION`.** The new registration assigns N j samples to each fixed row, so its sample index and concentration budget depend on j. The old theorem assumes one uniform N. The new proof uses VariableRegisteredSamples.registered_row_calibration and the same event-inclusion argument; constant N is an adapter case, not the general signature.

### R13 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredJoint.lean`, declaration at line 90.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredGoodJointCheck.registered_selected_joint_failure_of_cap_on_good` — `ADAPTER_OR_GENERALIZATION`.** Three premise changes are substantive: dependent row sample counts, arbitrary Y with selected-event measurability on Good, and envelope assumptions only for the selected candidate on that same Good. The old endpoint requires finite Y, uniform N and an envelope for every candidate. The proof reuses selectedTrainingDeployment_failure_le, empirical_coarse_row_tv and the occupation budget, with the new arbitrary-observation risk theorem. The training law, select function, P and selected policy remain identical across fit, cap, envelope, checked event and final joint law.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good` — `DIFFERENT_PROPOSITION`.** The old viable theorem chooses a specific viableFamilyPolicy and derives its zero uncovered occupation internally from viable initial fibers. The new cap theorem accepts a general policy with an occupation bound and does not require viability. A restricted viable-policy theorem cannot replace this general endpoint; the old uniform-N/finite-Y assumptions also differ.

### R14 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_measurable`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredSamples.lean`, declaration at line 46.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_measurable` — `ADAPTER_OR_GENERALIZATION`.** The new measurable projection uses dependent coordinates Sigma j, Fin (N j); the old one uses J × Fin N. Both correctly reuse measurable_pi_apply. A constant-N coordinate equivalence gives an adapter, but the old signature is not the general dependent sample space.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_independent` — `DIFFERENT_PROPOSITION`.** Joint independence is a property of the entire family and its probability law. It is not the measurability assertion for one coordinate.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_law` — `DIFFERENT_PROPOSITION`.** The marginal pushforward equality is a property of the probability law, stronger and different from coordinate measurability.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_measurable` — `ADAPTER_OR_GENERALIZATION`.** sourceSample_measurable specializes to controlled source rows with a uniform count and a time-bound wrapper. The new theorem is the generic dependent-coordinate projection for arbitrary registered rows; the old specialization cannot replace it.

### R15 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_law`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredSamples.lean`, declaration at line 52.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_law` — `ADAPTER_OR_GENERALIZATION`.** The old marginal law has a product coordinate with a uniform count; the new marginal law has a dependent Sigma coordinate with row-specific count. Both reuse measurePreserving_eval.map_eq for the same real product construction, without assuming the desired law.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_independent` — `DIFFERENT_PROPOSITION`.** Independence does not state which marginal distribution a coordinate has. The new pushforward equality identifies that marginal with the registered row distribution.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_measurable` — `DIFFERENT_PROPOSITION`.** Measurability alone does not determine a marginal distribution. The actual product-law equality remains a separate required property.

### R16 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_independent`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredSamples.lean`, declaration at line 59.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_independent` — `ADAPTER_OR_GENERALIZATION`.** The new proof reuses coordinate_iIndep and iIndepFun.precomp with the injective embedding Fin (N j) → Sigma j, Fin (N j). The old proof uses Fin N → J × Fin N. The actual product law and coordinate independence are proved in both cases, but the dependent family requires the new adapter.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_law` — `DIFFERENT_PROPOSITION`.** Correct one-coordinate marginal laws do not imply independence of samples. This old theorem is therefore not a replacement for the independence statement.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_measurable` — `DIFFERENT_PROPOSITION`.** Measurability of projections does not imply their probabilistic independence.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_independent` — `ADAPTER_OR_GENERALIZATION`.** sourceSample_independent is a controlled-row, uniform-N specialization with an n < T wrapper. The new theorem proves independence for a fixed generic row with its own N j and dependent sample coordinate type.

### R17 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.registered_row_calibration`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredSamples.lean`, declaration at line 79.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_registered_row_calibration` — `EXISTING_THEOREM_REUSED`.** The proof actually applies coverage_registered_row_calibration to Unit separately for each j at N j and then combines the resulting row failure bounds by a finite union bound. It reuses the existing concentration result instead of reproving it. Registration and counts are fixed before data; cross-row independence is not added as a hidden assumption.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_registered_source_calibration` — `ADAPTER_OR_GENERALIZATION`.** coverage_registered_source_calibration specializes the old uniform-count theorem to controlled source rows. The new theorem is generic in the finite registered row type and permits unequal sample counts; the source specialization is narrower.

### R18 — `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableVariableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good`

Source: `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ViableVariableRegisteredJoint.lean`, declaration at line 39.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good` — `ADAPTER_OR_GENERALIZATION`.** The new theorem uses the same existing viableFamilyPolicy construction and proves its own zero uncovered occupation with viablePolicy_zero_uncovered. It extends the old endpoint to row-specific counts, arbitrary Y and selected Good-only measurability/envelope assumptions. In the new call to VariableRegisteredJoint the cap is derived internally with kappa = 0 for that exact policy and Good; no cap of another policy is borrowed.

**`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredGoodJointCheck.registered_selected_joint_failure_of_cap_on_good` — `ADAPTER_OR_GENERALIZATION`.** The old cap theorem can be specialized to a viable policy only within its fixed-N, finite-Y, all-candidate-envelope scope. The new proof composes the generalized cap endpoint with the existing viability result. The viability derivation is an explicit adapter and is not an assumption replacing the required zero-occupation proof.

## Historical omission discovered during scope reconciliation

The 4,095 actual-base lexical declarations and the 4,094 registered graph nodes differ by exactly `UEOT.V3.FreeInformationValue.integrable_finset_sup'`. The unchanged source really declares this public theorem. The historical declaration CSV truncated the trailing apostrophe, marked the resulting name `UNRESOLVED`, and omitted the actual declaration from the proof graph. Its source SHA is `e4375851def0e735d54c7d3f56ba48517040e064073fdc1283a006f1d33c1a87`. This is an actual audit gap, not merely a display-count convention.

The old `fkrg.py` regex ends the identifier pattern with `\b`; after a trailing apostrophe, that boundary fails and the regex can backtrack to the preceding letter. The frozen parser is not modified by this review. The precise declaration must instead be confirmed by actual native ownership/type/axiom extraction and added through an explicit historical repair record. The historical CSV and original 4,094-node identity remain immutable.

The registered `p_ref_03` proof explicitly invokes this helper, while its frozen registered dependency list is empty. An additive existing-node edge repair is therefore required after native direct-constant confirmation. See the separate repair protocol; neither a comparison supplement nor a new graph edge is certified merely by this lexical observation.

## Pending execution and canonical gates

- Actual native ownership, types, direct proof constants and allowed axiom closure for all seven new source modules plus the unchanged historical repair module.
- 52 new public source declarations plus one explicitly historical public repair: 53*4094 cross comparisons and 53*52/2 internal comparisons, including all 52 new-versus-repair comparisons.
- Actual compiled proof-edge evidence for the repair and p_ref_03; preserve frozen CSV and the old registered scope identity.
- Independent binding to the actual native/fixed-verifier outputs after execution; no type-distinctness, no-collision or full-build PASS is asserted here.
- Canonical authorization, actual-base parser/preflight and complete FKRG integration gates remain the root task; this semantic review does not substitute for them.

## Source bindings

| Source | SHA256 |
|---|---|
| `formalization/ueot-core/UEOT/V3/AverageErrorTransport.lean` | `60cc6d0d118db8c26a1c696cd56eac3b4c2db8618eb3cd367c4f981c51a073cb` |
| `formalization/ueot-core/UEOT/V3/Compression/CrossTrack/DualIsolationCore.lean` | `f75f8deedff13ddae1dbd2ba0ae67f2c277adde648dd587c3494541a2e000e0c` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion.lean` | `cc36122dd6d95f2d4c03763769af43f2b6f5aad112c8509edff62d1287303c0a` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ArbitraryObservationRisk.lean` | `71a98f27b191c161f8a5a4b89a93ba8bde3afefc207d2d70d7277cf96527bcbb` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DeploymentCoverage.lean` | `5869824d0b059abcdf7e211d330cc944d0e5448275732bfad60f5728d1819585` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteHorizonRisk.lean` | `d39f58ddbc8a41edf0221bcbb875c294def320319230a7c113cb18765ad46f08` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscape.lean` | `88cfb12b7321a3892ce1d73e38caa84362507f2e61175c665726019eef4b158b` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscapeBoundary.lean` | `0fe9d180c44a7b35784472ecee3a8baee0b6e6464edee85e5dfaa78863c0cbc9` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PathObservationEscape.lean` | `eb963f19ae5d0a22a7d6215f7c769becbbd688a1bb5cbc33fa09880368cfa854` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ReachablePolicyExtension.lean` | `9296990a6656f38dd0d522e6d17086121d064ec10d835e18a3273b2eaeafb451` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisteredDeploymentRisk.lean` | `9f5655420a5ff33707041060e841dcddcb3630b0b967fd6373d14a4f1a208f51` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskWitness.lean` | `9bd381fde5c6db2ae84e02363d33ed68de412b1fd9a2f827a72fe474bf82405e` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredJoint.lean` | `f7075995f53cb7a67c3400a4ffad5006227267384f5cc732bd47aaab8124b4b9` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredSamples.lean` | `98972b20af6a18004c428c0905d571922296be8d79695b7201d6518b8e111ee5` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ViableRegisteredJoint.lean` | `2d0dbdd7a546dbe321885155524936afb9299a8457ff5b5b129ca33a9f2519d0` |
| `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ViableVariableRegisteredJoint.lean` | `ca182fe7e2367901452451d4adc4dd97b266c190c0194f37e9873baac314a357` |
| `formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean` | `1f8c4f5be6d3906cdeaa6d88809cc5e0fa5f601ce8b69b21cef67a16dc7a7384` |
| `formalization/ueot-core/UEOT/V3/DynamicsKernel.lean` | `97ed375855ff5d76e657f3d2c135ef4b36fa154c7377106fc24d1a97126599bc` |
| `formalization/ueot-core/UEOT/V3/FiniteAlphabetConcentration.lean` | `2ee3e3ac690df51ba25306a8db8820e703e332f9e285c7de6317a4a4fd420a8a` |
| `formalization/ueot-core/UEOT/V3/FreeInformationValue.lean` | `e4375851def0e735d54c7d3f56ba48517040e064073fdc1283a006f1d33c1a87` |
| `formalization/ueot-core/UEOT/V3/InformationPredictiveFactorization.lean` | `1faa13ec3489bc32237aa2370ce176471527684e90c407f7ec546cc5b21e23cb` |
| `formalization/ueot-core/UEOT/V3/PathError.lean` | `d561a56db79bbd5dd9d01673c5fa7970c7d31199356bd5169a416cd930d917ba` |
| `formalization/ueot-core/UEOT/V3/StatisticalDefect.lean` | `acf043effe89364adec73d1b2dae5a4d10504b10ac2cf984369a6baae69f1fe0` |
| `formalization/ueot-core/UEOT/V3/ThirdParty/CrooksJarzynski/ContinuousTimeJumpSimplex.lean` | `c2d22cd7399479127a39ce7e0542c684017e6c067f905ee3bbd0bf0567c97dcc` |
| `formalization/ueot-core/UEOT/V3/TotalVariation.lean` | `f048fa2b68ca691f326395f940a29b6f8b50822910b6d0a9dda43700caf1dbe6` |

The structured receipt contains every exact candidate name and its source path. The candidate pairs are generated from the immutable preflight input, so neither an unreviewed hint nor a name-similarity-only conclusion is silently dropped.
