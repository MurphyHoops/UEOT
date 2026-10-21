import UEOT
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command Meta
set_option maxHeartbeats 0

private def registeredInterfacesEvidenceName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part => Name.str n part) Name.anonymous

run_cmd do
  let env ← getEnv
  let graph ← liftIO <| IO.FS.readFile
    "docs/compression/theory_completion/knowledge/audits/2026-10-10/all_3793_theorem_direct_reuse_graph.csv"
  let baseNames := (graph.splitOn "\n").drop 1 |>.filterMap fun line =>
    if line.isEmpty then none else
      match line.splitOn "," with
      | [] => none
      | name :: _ => some (registeredInterfacesEvidenceName name)
  unless baseNames.length == 3793 do throwError "REGISTERED_INTERFACES_BASE_GRAPH_COUNT"
  let priorNames : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_rel,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_defect,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_preserves_exact_relation,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_zero_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_budget_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectPresentation.rescale_changes_nonzero_defect,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.same_relation_arbitrary_positive_scale,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.no_relation_only_quantitative_recovery,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.exists_same_relation_different_defect,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.relationDefectPresentation_does_not_force_triangle,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.zero_defect_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.rel_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.forward_budget,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.reverse_budget,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.tendsto_zero_iff,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.rescaleCalibration,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.calibrated_weighted_chain_bound,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.same_relation_does_not_transport_unit_budget,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.triangle_quasi,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.calibrated_cross_stage_contraction,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.rescale_triangle_preserved,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.rescale_contraction_transformed,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.rescale_local_budget_transformed,
    `UEOT.V3.Compression.TheoryCompletion.MinCore.rescaled_weighted_chain_bound,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.transitionMass_nonneg,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.transitionMass_sum,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.kernel_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.failed_absorbing,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.row_tv_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.row_tv_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.law_zero,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.bind_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.safe_mass_succ,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.failure_mass_succ,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.safe_mass_closed,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.failure_mass_closed,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.one_step_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.positive_leakage_not_all_times_safe,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.failure_mass_tendsto_one,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.bounded_row_error_with_asymptotic_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.pmf_tv_le_clipped_coordinate_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_pmf_tv_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_apply_toReal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_map_toReal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.quantitative_future_probe_tv_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_future_probe_tv_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.approximate_observable_partition_tv_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_observable_partition_tv_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.causalLaw_congr_before,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finite_horizon_path_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_causalLaw_map,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_projectedKernel_tv_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_projected_causalLaw_finite_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_event_transfer,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_last_project,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_tv_extend_same_initial,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_same_policy_row_tv,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_projected_path_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_projected_failure_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_coordinate_path_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_coordinate_failure_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_representative_path_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_representative_failure_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.riskFiberPosterior_support,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_map_mul_fiberPosterior,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_conditionedRow_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_map_extend_apply,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_map_extend_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_map_extend_right,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_commonMass_bind_lower_bound,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_tv_bind_same_weights,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_conditionedRow_tv_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empiricalResponsePMF_toMeasure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empiricalResponsePMF_event_mean,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.pmf_event_test_mean,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_full_event_row_tv,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_coarse_row_tv,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_reference_risk_of_calibrated,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_empirical_reference_certificate,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_microscopic_event_le_envelope,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_ever_failure_envelope,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_failure_envelope_covers,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_failure_envelope_minimal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_failure_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_exit_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_canonical_exit_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.trainingLaw_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.actualFailure_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selectedAction_empirically_minimal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.badFlag_iff_calibration_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.fixed_action_bad_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selected_bad_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selected_bad_iff_false_risk_bound,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.pointwise_confidence_not_selected_confidence,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.simultaneous_calibration_protects_any_selector,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_trueRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_finite_row_calibration_bad_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_empirical_transition_uncalibrated_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measurableSet_empirical_transition_calibrated,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_representative_risk_of_calibrated,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_representative_risk_certificate,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_measurable,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_law,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_independent,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_before,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_measurable,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_law,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_independent,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.product_experiment_risk_certificate,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.partition_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.actualRow_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_bounded,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.indicators_spanned,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.coefficient_norm,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_expectation,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.fibre_test_gap,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.hidden_gap_nonzero,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.action_gap_nonzero,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.coarse_not_injective,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.partition_not_stable,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.classBit_project,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.representative_section,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_card,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_confidence_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_confidence_nonvacuous,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measurable_good,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_bad_probability_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_good_probability_ge,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.good_sample_exists,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measured_fibre_bound,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.representative_risk_on_good,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_row_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_path_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.referenceInitialLaw_project,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.actualRow_ofReal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.boolReferenceKernel_apply,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.boolReference_two_step_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_history_last,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.classReferenceKernel_map,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_control_map,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_transport,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_ever_failure_equiv,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_two_step_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.microscopic_two_step_risk_on_good,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.joint_statistical_microscopic_risk_witness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_statistical_selected_joint_failure_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_fixed_policy_training_deployment_witness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_sum_toReal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_tv_extend_same_initial,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_tv_extend_same_kernel,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_map_extend_reference,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_projected_extension_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_projected_causalLaw_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_expectation_map,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_rowLaw_expectation,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_uncovered_indicator_expectation,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_expected_error_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_row_tv,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_path_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_certified_path_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_microscopic_failure_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_registered_row_calibration,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_registered_source_calibration,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_empirical_registered_microscopic_failure_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.actualRow_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.actual_row_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.certified_row_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.uncovered_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.reference_one_step_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.reference_two_step_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.restrictedActionLaw_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.restricted_uncovered_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.restricted_two_step_budget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.restricted_two_step_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.restricted_two_step_failure_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.training_mean_true_error,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.uncovered_deployment_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.uncovered_deployment_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.training_average_does_not_bound_deployment,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.empirical_loss,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness.zero_empirical_loss_with_failed_deployment,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finite_training_selection_measurable,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedDeployment_measure_measurable,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_training_marginal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_path_marginal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_failure_tower,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_failure_integral,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_data_dependent_bound,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_good_bad_bound,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_failure_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_selected_empirical_deployment_risk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentWitness.training_bad_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentWitness.good_deployment_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentWitness.bad_deployment_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentWitness.selected_deployments_are_nonconstant,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentWitness.sharp_joint_failure_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentWitness.sharp_mixture_is_attained,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentWitness.wrong_conditional_law_counterexample,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.EmptyCommonAction.current_fiber_is_nonempty,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.EmptyCommonAction.each_state_has_a_certified_action,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.EmptyCommonAction.no_common_certified_action,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.EmptyCommonAction.fiber_mask_is_empty,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.MissingFiber.representative_is_certified,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.MissingFiber.observable_action_leakage_is_zero,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.MissingFiber.actual_initial_row_law,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.MissingFiber.actual_uncovered_mass_is_one,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.MissingFiber.checking_one_representative_does_not_bound_actual_coverage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.initial_apply,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.actualPrefix_apply,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.actualPrefix_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.actual_prefix_masses,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.left_history_supported,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.right_history_supported,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.coarsePrefix_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.left_coarse_supported,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.right_coarse_supported,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.two_positive_coarse_histories,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.left_posterior_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.right_posterior_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.posterior_supports_are_singletons,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.both_terminal_states_reachable,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.actual_uncovered_probability_zero,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.whole_current_fiber_has_no_common_action,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.null_history_boundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.mem_source_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.supportTable_exact,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.deadend_checker_rejects,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.initial_support_eq_univ,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.a_complete_zero_uncovered_policy_exists,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.deadend_policy_first_step_covered,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.deadend_history_actually_supported,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.deadend_trace_support_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.deadend_has_no_common_certified_action,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.deadend_policy_second_step_not_covered,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.SafePrefixDeadend.viable_source_with_a_covered_deadend,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.mem_microLaw_succ_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.mem_coarseLaw_zero_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.mem_traceSupport_iff_realized,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.mem_coarseLaw_succ_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.traceSupport_eq_fiberTerminalPosterior_support,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.successorSupport_eq_fiberTerminalPosterior_support,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.mem_deploymentRowLaw_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.zero_uncertified_mass_iff_support,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.zero_uncovered_iff_support_certified,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.viableWith_step_of_lt,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.viablePolicy_support_step,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.viablePolicy_supported_histories_viable,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.viablePolicy_zero_uncovered,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.supported_viable_of_zero_uncovered,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.initial_viability_iff_exists_zero_uncovered_policy,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.finiteSuccessor_coe_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.finiteViabilityCheck_correct,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.finiteRelationSuccessor_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.finiteRelationViabilityCheck_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.finiteRelationViabilityCheck_correct,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.mem_fiberCertifiedActions,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.uncovered_occupancy_le_observable_action_leakage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.observable_action_restriction_bounds_coverage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.hard_observable_action_restriction_has_zero_uncovered_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageContinuationCheck.deployment_coverage_budget_le_of_actual_occupancy_cap,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageContinuationCheck.observable_action_coverage_budget_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageContinuationCheck.microscopic_failure_risk_under_observable_action_cap,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageContinuationCheck.finiteHorizonSupportedPolicy_hard_support,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageContinuationCheck.nonempty_fiber_masks_give_zero_uncovered_policy,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportCoverageCheck.mem_fiberTerminalPosterior_support_iff,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportCoverageCheck.supported_history_actions_bound_actual_coverage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportCoverageCheck.posterior_supported_actions_bound_actual_coverage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PolicyPrefixCongruenceCheck.actual_causalLaw_congr_before,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PolicyPrefixCongruenceCheck.deployment_rowLaw_congr_through,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ReachablePolicyExtensionCheck.extend_policy_at_reachable_histories,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ReachablePolicyExtensionCheck.exists_zero_uncovered_policy_of_extendability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredGoodJointCheck.registered_calibration_good_bad_le,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredGoodJointCheck.registered_selected_joint_failure_of_cap_on_good,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.actualRow_mass,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.registered_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.registered_card,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.samples_measurable,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.samples_independent,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.samples_law,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.actual_failure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.actual_occupancy_zero,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.empirical_fit,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.empirical_failure_on_good,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.referenceFailure_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.checkedBudget_on_good,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.confidenceBudget_eq,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.confidenceBudget_small,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.registered_selected_joint_bound,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.selectedAction_law,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.selectedAction_pmf,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.selection_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.actual_deployments_distinct,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.two_positive_deployment_choices,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.actual_joint_failure_exact,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.empiricalRow_allTrue,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.allTrue_checkedBudget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.all_record_budget_false,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.allTrue_positive_probability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredSelectionWitness.registered_selection_joint_witness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good,
  ]
  let newNames : Array (Name × Name) := #[
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.escape_transition_row_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.factorized_same_policy_path_error, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_path_error, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_certified_path_error, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_microscopic_failure_risk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_le_of_event_sub_le, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_map_eq_of_carrier_traces, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_some_iff, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_atom, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_none_iff, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_carrier_trace, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_atomEncode_eq, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_map_some, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_escape_probability, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.pmf_eq_of_eq_except_one, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_reference_eq, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_embedded_eq_encoded, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_eq_of_live_reference_masses, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.pmfExtend_apply_general, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.causalLaw_live_history_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.live_injective, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.place_five_injective, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.atomEncode_place, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.reference_encoded, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.reference_escape_probability, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.source_reference_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.recode_seven, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.references_original_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.references_encoded_tv_zero, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.infinite_ambient_positive_escape_boundary, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.riskHistoryMap_comp_general, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.riskHistoryMap_injective_general, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_comp, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_injective, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.map_observationHistoryMap_comp, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escapePolicy_live_history, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escapePolicy_actual_history, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_micro_control_kernel, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_deployment_row_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_initial_live_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_macro_live_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_reference_live_history_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_path_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_calibration_good_bad_le, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJoint),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJoint),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_independent, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.registered_row_calibration, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.product_experiment_calibration, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableVariableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableVariableRegisteredJoint),
    (`UEOT.V3.FreeInformationValue.integrable_finset_sup', `UEOT.V3.FreeInformationValue),
  ]
  let historicalRepairNames : Array Name := #[
    `UEOT.V3.FreeInformationValue.integrable_finset_sup',
  ]
  let sourceModules : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJoint,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableVariableRegisteredJoint,
    `UEOT.V3.FreeInformationValue,
  ]
  for sourceModule in sourceModules do
    unless env.header.moduleNames.contains sourceModule do
      throwError s!"REGISTERED_INTERFACES_SOURCE_MODULE_NOT_IMPORTED {sourceModule}"
  let registered := baseNames ++ priorNames.toList
  unless registered.length == 4094 do throwError "REGISTERED_INTERFACES_REGISTERED_PRIOR_COUNT"
  unless newNames.size == 53 && historicalRepairNames.size == 1 && sourceModules.size == 8 do
    throwError "REGISTERED_INTERFACES_PUBLIC_AND_NATIVE_SCOPE_COUNT"
  let allRegistered := registered ++ (newNames.toList.map Prod.fst)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let expectedEdges : Array (Name × List Name) := #[
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.escape_transition_row_tv, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_embedded_eq_encoded]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.factorized_same_policy_path_error, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.escape_transition_row_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_deployment_row_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_path_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_same_policy_path_error]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_path_error, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.factorized_same_policy_path_error]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_certified_path_error, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_path_error, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_expected_error_le, `UEOT.V3.TotalVariation.tvDist_le_one]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_microscopic_failure_risk, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_certified_path_error, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_event_transfer, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_microscopic_event_le_envelope]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_le_of_event_sub_le, [`UEOT.V3.TotalVariation.tvEventSet_nonempty]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_map_eq_of_carrier_traces, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_le_of_event_sub_le, `UEOT.V3.TotalVariation.tvDist_map_le, `UEOT.V3.TotalVariation.tvEvent_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_some_iff, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_atom, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_some_iff]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_none_iff, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_measurable, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_none_iff]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_carrier_trace, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_atom, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_none_iff]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_atomEncode_eq, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_carrier_trace, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_map_eq_of_carrier_traces]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_map_some, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_atom, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_some_iff]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_escape_probability, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_none_iff, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_measurable]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.pmf_eq_of_eq_except_one, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_sum_toReal]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_reference_eq, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_map_some, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.pmf_eq_of_eq_except_one]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_embedded_eq_encoded, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_atom, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_atomEncode_eq]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_eq_of_live_reference_masses, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_reference_eq, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_embedded_eq_encoded]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.pmfExtend_apply_general, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.causalLaw_live_history_mass, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.pmfExtend_apply_general]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.live_injective, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.place_five_injective, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.live_injective]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.atomEncode_place, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.live_injective, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_atom, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_none_iff]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.reference_encoded, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.atomEncode_place]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.reference_escape_probability, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.reference_encoded, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_escape_probability, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_measurable]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.source_reference_tv, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.live_injective, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.reference_encoded, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_embedded_eq_encoded, `UEOT.V3.PathError.tvDist_eq_one_sub_pmfCommonMass]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.recode_seven, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.place_five_injective, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_atom, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_eq_none_iff]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.references_original_tv, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.place_five_injective, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.recode_seven, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_embedded_eq_encoded, `UEOT.V3.PathError.tvDist_eq_one_sub_pmfCommonMass]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.references_encoded_tv_zero, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.reference_encoded, `UEOT.V3.TotalVariation.tvDist_self_eq_zero]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.infinite_ambient_positive_escape_boundary, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.reference_escape_probability, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.references_encoded_tv_zero, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.references_original_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck.source_reference_tv]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.riskHistoryMap_comp_general, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.riskHistoryMap_injective_general, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_comp, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.riskHistoryMap_comp_general]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_injective, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.riskHistoryMap_injective_general]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.map_observationHistoryMap_comp, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_comp]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escapePolicy_live_history, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_comp]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escapePolicy_actual_history, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_comp]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_micro_control_kernel, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escapePolicy_actual_history]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_deployment_row_law, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escapePolicy_actual_history, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_micro_control_kernel]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_initial_live_mass, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_atom, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_map_some]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_macro_live_mass, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.atomEncode_map_some, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.pmfExtend_apply_general, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escapePolicy_live_history, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_last_project]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_reference_live_history_mass, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.causalLaw_live_history_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_initial_live_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_macro_live_mass]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_path_tv, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_eq_of_live_reference_masses, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_micro_control_kernel, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.escape_reference_live_history_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.map_observationHistoryMap_comp, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck.observationHistoryMap_injective]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_calibration_good_bad_le, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.registered_row_calibration]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_microscopic_failure_risk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageContinuationCheck.deployment_coverage_budget_le_of_actual_occupancy_cap, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_calibration_good_bad_le, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_coarse_row_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.selectedTrainingDeployment_failure_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_measurable, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_law, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_independent, [`UEOT.V3.HilbertMeanProductBlockIndependence.coordinate_iIndep]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.registered_row_calibration, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.coverage_registered_row_calibration]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.product_experiment_calibration, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_independent, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.productRowSample_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples.registered_row_calibration]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableVariableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.viablePolicy_zero_uncovered, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good]),
    (`UEOT.V3.FreeInformationValue.integrable_finset_sup', []),
  ]
  let mut nativeScope : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo decl := info then
      if let some idx := env.getModuleIdxFor? name then
        let sourceModule := env.header.moduleNames[idx]!
        if sourceModules.contains sourceModule then
          let actual ← Lean.collectAxioms name
          unless (actual.filter fun ax => !allowed.contains ax).isEmpty do
            throwError s!"REGISTERED_INTERFACES_NONSTANDARD_AXIOM {name}: {actual}"
          let rendered ← liftTermElabM do ppExpr decl.type
          let constants := decl.value.getUsedConstants.toList
          let theoremDeps := constants.filter fun dep =>
            match env.find? dep with
            | some (.thmInfo _) => true
            | _ => false
          nativeScope := nativeScope.push <| Json.mkObj [
            ("name", toJson name.toString),
            ("source_module", toJson sourceModule.toString),
            ("is_private", toJson (Lean.privateToUserName? name).isSome),
            ("axioms", toJson (actual.map Name.toString)),
            ("type", toJson rendered.pretty),
            ("level_parameters", toJson (decl.levelParams.map Name.toString)),
            ("direct_constants", toJson (constants.map Name.toString)),
            ("direct_theorem_constants", toJson (theoremDeps.map Name.toString))]
  -- The only historical rescan is a direct-proof search for the exact omitted
  -- name. Emit every positive row; do not prefill a supposed singleton caller.
  let expectedExistingRepairs : Array (Name × List Name × List Name) := #[
    (`UEOT.V3.FreeInformationValue.p_ref_03, [], [`UEOT.V3.FreeInformationValue.integrable_finset_sup']),
  ]
  let mut registeredScanned := 0
  let mut historicalIncoming : Array Json := #[]
  for name in registered do
    let some (.thmInfo decl) := env.find? name
      | throwError s!"REGISTERED_INTERFACES_PRIOR_NOT_THEOREM {name}"
    let constants := decl.value.getUsedConstants.toList
    let hits := constants.filter fun dep => historicalRepairNames.contains dep
    registeredScanned := registeredScanned + 1
    if !hits.isEmpty then
      let some idx := env.getModuleIdxFor? name
        | throwError s!"REGISTERED_INTERFACES_EXISTING_REPAIR_OWNER_MISSING {name}"
      let sourceModule := env.header.moduleNames[idx]!
      let actualDeps := constants.filter fun dep => dep != name && allRegistered.contains dep
      let some (_, prior, added) := expectedExistingRepairs.find? (fun entry => entry.1 == name)
        | throwError s!"UNEXPECTED_HISTORICAL_REPAIR_CALLER {name}"
      unless hits.length == added.length && added.all (fun dep => hits.contains dep) do
        throwError s!"HISTORICAL_REPAIR_DIRECT_HITS_DRIFT {name}"
      let expectedDeps := prior ++ added
      unless actualDeps.length == expectedDeps.length && expectedDeps.all (fun dep => actualDeps.contains dep) do
        throwError s!"HISTORICAL_REPAIR_PRIOR_PLUS_DELTA_DRIFT {name}"
      historicalIncoming := historicalIncoming.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("source_module", toJson sourceModule.toString),
        ("direct_constants", toJson (constants.map Name.toString)),
        ("historical_repair_deps", toJson (hits.map Name.toString)),
        ("actual_source_theorem_deps", toJson (actualDeps.map Name.toString))]
  unless registeredScanned == 4094 && historicalIncoming.size == expectedExistingRepairs.size do
    throwError "HISTORICAL_REPAIR_COMPLETE_NARROW_SCAN_DRIFT"
  let historicalScan := Json.mkObj [
    ("registered_theorems_scanned", toJson registeredScanned),
    ("historical_public_repair_targets", toJson (historicalRepairNames.map Name.toString)),
    ("incoming_rows", toJson historicalIncoming)]
  unless nativeScope.size == 92 do
    throwError s!"REGISTERED_INTERFACES_NATIVE_THEOREM_SCOPE_DRIFT {nativeScope.size}"
  let mut cross := 0
  let mut newCross := 0
  let mut repairCross := 0
  let mut internal := 0
  let mut newInternal := 0
  let mut mixedInternal := 0
  let mut repairInternal := 0
  let mut collisions : Array Json := #[]
  let mut rows : Array Json := #[]
  for (name, owner) in newNames do
    let some (.thmInfo decl) := env.find? name | throwError s!"REGISTERED_INTERFACES_NEW_THEOREM_MISSING {name}"
    let some idx := env.getModuleIdxFor? name | throwError s!"REGISTERED_INTERFACES_SOURCE_MODULE_MISSING {name}"
    unless env.header.moduleNames[idx]! == owner do
      throwError s!"REGISTERED_INTERFACES_SOURCE_MODULE_MISMATCH {name}"
    if (Lean.privateToUserName? name).isSome then throwError s!"REGISTERED_INTERFACES_PUBLIC_CANDIDATE_PRIVATE {name}"
    for old in registered do
      let some oldInfo := env.find? old | throwError s!"REGISTERED_INTERFACES_PRIOR_SYMBOL_MISSING {old}"
      let eq ← liftTermElabM do Meta.isDefEq decl.type oldInfo.type
      cross := cross + 1
      if historicalRepairNames.contains name then
        repairCross := repairCross + 1
      else
        newCross := newCross + 1
      if eq then collisions := collisions.push <| toJson [name.toString, old.toString]
    let constants := decl.value.getUsedConstants.toList
    let deps := constants.filter fun dep => dep != name && allRegistered.contains dep
    let some (_, expected) := expectedEdges.find? (fun pair => pair.1 == name)
      | throwError s!"REGISTERED_INTERFACES_EXPECTED_EDGES_MISSING {name}"
    unless deps.length == expected.length && expected.all (fun dep => deps.contains dep) do
      throwError s!"REGISTERED_INTERFACES_FIXED_PROOF_DEPENDENCIES_MISMATCH {name}: actual={deps} expected={expected}"
    let rendered ← liftTermElabM do ppExpr decl.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("registration_kind", toJson (if historicalRepairNames.contains name then
        "historical_public_repair" else "new_source_public")),
      ("source_module", toJson owner.toString),
      ("type", toJson rendered.pretty),
      ("level_parameters", toJson (decl.levelParams.map Name.toString)),
      ("source_theorem_deps", toJson (deps.map Name.toString)),
      ("direct_constants", toJson (constants.map Name.toString))]
  for i in [:newNames.size] do
    for j in [i+1:newNames.size] do
      let ni := newNames[i]!.1
      let nj := newNames[j]!.1
      let ci ← getConstInfo ni
      let cj ← getConstInfo nj
      let eq ← liftTermElabM do Meta.isDefEq ci.type cj.type
      internal := internal + 1
      if historicalRepairNames.contains ni && historicalRepairNames.contains nj then
        repairInternal := repairInternal + 1
      else if historicalRepairNames.contains ni || historicalRepairNames.contains nj then
        mixedInternal := mixedInternal + 1
      else
        newInternal := newInternal + 1
      if eq then collisions := collisions.push <| toJson [ni.toString, nj.toString]
  let output := Json.mkObj [
    ("schema", toJson "REGISTERED_INTERFACES_NATIVE_EXPORT_V1"),
    ("registered_prior_theorems", toJson registered.length),
    ("new_source_public_theorem_count", toJson (newNames.size - historicalRepairNames.size)),
    ("historical_public_repair_count", toJson historicalRepairNames.size),
    ("overlay_public_registration_count", toJson newNames.size),
    ("native_audit_modules", toJson (sourceModules.map Name.toString)),
    ("cross_isDefEq_comparisons", toJson cross),
    ("new_source_to_registered_isDefEq_comparisons", toJson newCross),
    ("historical_repair_to_registered_isDefEq_comparisons", toJson repairCross),
    ("internal_isDefEq_comparisons", toJson internal),
    ("new_source_internal_isDefEq_comparisons", toJson newInternal),
    ("new_source_to_historical_repair_isDefEq_comparisons", toJson mixedInternal),
    ("historical_repair_internal_isDefEq_comparisons", toJson repairInternal),
    ("historical_repair_incoming_scan", historicalScan),
    ("collisions", toJson collisions),
    ("public_source_theorems", toJson rows),
    ("all_native_theorem_constants", toJson nativeScope)]
  liftIO <| IO.println ("REGISTERED_INTERFACES_NATIVE_JSON " ++ output.compress)
  unless collisions.isEmpty do throwError "REGISTERED_INTERFACES_OVERLAY_TYPE_COLLISION"
