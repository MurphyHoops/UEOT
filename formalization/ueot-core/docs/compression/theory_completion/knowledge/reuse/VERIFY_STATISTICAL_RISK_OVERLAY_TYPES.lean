import UEOT
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command Meta
set_option maxHeartbeats 0

private def statisticalRiskEvidenceName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part => Name.str n part) Name.anonymous

run_cmd do
  let env ← getEnv
  let graph ← liftIO <| IO.FS.readFile
    "docs/compression/theory_completion/knowledge/audits/2026-10-10/all_3793_theorem_direct_reuse_graph.csv"
  let baseNames := (graph.splitOn "\n").drop 1 |>.filterMap fun line =>
    if line.isEmpty then none else
      match line.splitOn "," with
      | [] => none
      | name :: _ => some (statisticalRiskEvidenceName name)
  unless baseNames.length == 3793 do throwError "STATISTICAL_RISK_BASE_GRAPH_COUNT"
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
  ]
  let newNames : Array (Name × Name) := #[
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empiricalResponsePMF_toMeasure, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empiricalResponsePMF_event_mean, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.pmf_event_test_mean, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_full_event_row_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_coarse_row_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_reference_risk_of_calibrated, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_empirical_reference_certificate, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_microscopic_event_le_envelope, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_ever_failure_envelope, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_failure_envelope_covers, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_failure_envelope_minimal, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_failure_risk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_exit_risk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_canonical_exit_risk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.trainingLaw_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.actualFailure_eq, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selectedAction_empirically_minimal, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.badFlag_iff_calibration_error, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.fixed_action_bad_probability, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selected_bad_probability, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selected_bad_iff_false_risk_bound, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.pointwise_confidence_not_selected_confidence, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.simultaneous_calibration_protects_any_selector, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_trueRisk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_finite_row_calibration_bad_le, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_empirical_transition_uncalibrated_le, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measurableSet_empirical_transition_calibrated, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_representative_risk_of_calibrated, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_representative_risk_certificate, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_independent, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_before, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_independent, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.product_experiment_risk_certificate, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.partition_iff, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.actualRow_mass, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_bounded, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.indicators_spanned, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.coefficient_norm, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_expectation, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.fibre_test_gap, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.hidden_gap_nonzero, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.action_gap_nonzero, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.coarse_not_injective, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.partition_not_stable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.classBit_project, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.representative_section, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_card, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_confidence_budget, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_confidence_nonvacuous, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measurable_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_bad_probability_le, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_good_probability_ge, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.good_sample_exists, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measured_fibre_bound, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.representative_risk_on_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_row_budget, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_path_budget, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.referenceInitialLaw_project, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.actualRow_ofReal, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.boolReferenceKernel_apply, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.boolReference_two_step_failure, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_history_last, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.classReferenceKernel_map, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_control_map, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_transport, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_ever_failure_equiv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_two_step_failure, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.microscopic_two_step_risk_on_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.joint_statistical_microscopic_risk_witness, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness),
  ]
  let sourceModules : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness,
  ]
  for sourceModule in sourceModules do
    unless env.header.moduleNames.contains sourceModule do
      throwError s!"STATISTICAL_RISK_SOURCE_MODULE_NOT_IMPORTED {sourceModule}"
  let registered := baseNames ++ priorNames.toList
  unless registered.length == 3865 do throwError "STATISTICAL_RISK_REGISTERED_PRIOR_COUNT"
  let allRegistered := registered ++ (newNames.toList.map Prod.fst)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let expectedEdges : Array (Name × List Name) := #[
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empiricalResponsePMF_toMeasure, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empiricalResponsePMF_event_mean, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empiricalResponsePMF_toMeasure, `UEOT.V3.FiniteAlphabetSampling.empiricalMeasure_real_finset]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.pmf_event_test_mean, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_full_event_row_tv, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empiricalResponsePMF_event_mean, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_trueRisk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.pmf_event_test_mean, `UEOT.V3.FiniteAlphabetConcentration.tvDist_le_of_finset_event_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_coarse_row_tv, [`UEOT.V3.TotalVariation.tvDist_le_one, `UEOT.V3.TotalVariation.tvDist_map_le, `UEOT.V3.TransportDefect.tvDist_triangle]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_reference_risk_of_calibrated, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_full_event_row_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_coarse_row_tv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_failure_risk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_projected_path_error]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_empirical_reference_certificate, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_reference_risk_of_calibrated, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measurableSet_empirical_transition_calibrated, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_empirical_transition_uncalibrated_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_microscopic_event_le_envelope, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_ever_failure_envelope, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_failure_envelope_covers, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_failure_envelope_minimal, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_failure_risk, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_microscopic_event_le_envelope, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_projected_failure_risk]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_exit_risk, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_ever_failure_envelope, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_failure_risk]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_canonical_exit_risk, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_failure_envelope_covers, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_policy_microscopic_exit_risk]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.trainingLaw_mass, [`UEOT.V3.PathError.pmfExtend_apply]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.actualFailure_eq, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.kernel_mass]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selectedAction_empirically_minimal, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.badFlag_iff_calibration_error, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.actualFailure_eq]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.fixed_action_bad_probability, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selected_bad_probability, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selected_bad_iff_false_risk_bound, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.actualFailure_eq]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.pointwise_confidence_not_selected_confidence, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.fixed_action_bad_probability, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.selected_bad_probability]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.simultaneous_calibration_protects_any_selector, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary.actualFailure_eq]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_trueRisk, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_apply_toReal]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_finite_row_calibration_bad_le, [`UEOT.V3.BoundedLossTwoSided.measure_exists_candidate_bad_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_empirical_transition_uncalibrated_le, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_trueRisk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_finite_row_calibration_bad_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measurableSet_empirical_transition_calibrated, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_representative_risk_of_calibrated, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_representative_failure_risk, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.calibrated_representative_path_error, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_microscopic_event_le_envelope]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_representative_risk_certificate, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_representative_risk_of_calibrated, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measurableSet_empirical_transition_calibrated, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_empirical_transition_uncalibrated_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_measurable, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_law, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_independent, [`UEOT.V3.HilbertMeanProductBlockIndependence.coordinate_iIndep]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_before, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_measurable, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_before]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_law, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_before]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_independent, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.productRowSample_independent, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_before]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.product_experiment_risk_certificate, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_independent, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.statistical_representative_risk_certificate]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.partition_iff, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.actualRow_mass, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finiteKernelRowPMF_apply_toReal]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_bounded, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.indicators_spanned, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.coefficient_norm, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_expectation, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.fibre_test_gap, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_expectation]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.hidden_gap_nonzero, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_expectation]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.action_gap_nonzero, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_expectation]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.coarse_not_injective, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.partition_not_stable, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.classBit_project, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.representative_section, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_card, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_confidence_budget, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_confidence_nonvacuous, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measurable_good, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measurableSet_empirical_transition_calibrated]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_bad_probability_le, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_confidence_budget, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_confidence_nonvacuous, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_independent, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_law, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.sourceSample_measurable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.test_bounded, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.measure_empirical_transition_uncalibrated_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_good_probability_ge, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measurable_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_bad_probability_le]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.good_sample_exists, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_good_probability_ge]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measured_fibre_bound, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.fibre_test_gap]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.representative_risk_on_good, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.coefficient_norm, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.indicators_spanned, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measured_fibre_bound, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.representative_section, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.empirical_representative_risk_of_calibrated]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_row_budget, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_card]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.concrete_path_budget, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.referenceInitialLaw_project, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.actualRow_ofReal, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.actualRow_mass]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.boolReferenceKernel_apply, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.actualRow_ofReal]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.boolReference_two_step_failure, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_history_last, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.classReferenceKernel_map, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_control_map, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.classReferenceKernel_map, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_history_last, `UEOT.V3.RepresentationCovariance.pmfExtend_map_equiv]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_transport, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_control_map, `UEOT.V3.RepresentationCovariance.causalLaw_transport_equiv]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_ever_failure_equiv, []),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_two_step_failure, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.boolReference_two_step_failure, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_ever_failure_equiv, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_transport]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.microscopic_two_step_risk_on_good, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_card, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.class_reference_two_step_failure, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.representative_risk_on_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_ever_failure_envelope]),
    (`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.joint_statistical_microscopic_risk_witness, [`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.measurable_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.microscopic_two_step_risk_on_good, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.partition_not_stable, `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness.training_good_probability_ge]),
  ]
  let mut nativeScope : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo decl := info then
      if let some idx := env.getModuleIdxFor? name then
        let sourceModule := env.header.moduleNames[idx]!
        if sourceModules.contains sourceModule then
          let actual ← Lean.collectAxioms name
          unless (actual.filter fun ax => !allowed.contains ax).isEmpty do
            throwError s!"STATISTICAL_RISK_NONSTANDARD_AXIOM {name}: {actual}"
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
  unless nativeScope.size == 126 do
    throwError s!"RISK_NATIVE_THEOREM_SCOPE_DRIFT {nativeScope.size}"
  let mut cross := 0
  let mut internal := 0
  let mut collisions : Array Json := #[]
  let mut rows : Array Json := #[]
  for (name, owner) in newNames do
    let some (.thmInfo decl) := env.find? name | throwError s!"STATISTICAL_RISK_NEW_THEOREM_MISSING {name}"
    let some idx := env.getModuleIdxFor? name | throwError s!"STATISTICAL_RISK_SOURCE_MODULE_MISSING {name}"
    unless env.header.moduleNames[idx]! == owner do
      throwError s!"STATISTICAL_RISK_SOURCE_MODULE_MISMATCH {name}"
    if (Lean.privateToUserName? name).isSome then throwError s!"STATISTICAL_RISK_PUBLIC_CANDIDATE_PRIVATE {name}"
    for old in registered do
      let some oldInfo := env.find? old | throwError s!"STATISTICAL_RISK_PRIOR_SYMBOL_MISSING {old}"
      let eq ← liftTermElabM do Meta.isDefEq decl.type oldInfo.type
      cross := cross + 1
      if eq then collisions := collisions.push <| toJson [name.toString, old.toString]
    let constants := decl.value.getUsedConstants.toList
    let deps := constants.filter fun dep => dep != name && allRegistered.contains dep
    let some (_, expected) := expectedEdges.find? (fun pair => pair.1 == name)
      | throwError s!"RISK_EXPECTED_EDGES_MISSING {name}"
    unless deps.length == expected.length && expected.all (fun dep => deps.contains dep) do
      throwError s!"RISK_FIXED_PROOF_DEPENDENCIES_MISMATCH {name}: actual={deps} expected={expected}"
    let rendered ← liftTermElabM do ppExpr decl.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
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
      if eq then collisions := collisions.push <| toJson [ni.toString, nj.toString]
  let output := Json.mkObj [
    ("schema", toJson "STATISTICAL_RISK_NATIVE_EXPORT_V1"),
    ("registered_prior_theorems", toJson registered.length),
    ("cross_isDefEq_comparisons", toJson cross),
    ("internal_isDefEq_comparisons", toJson internal),
    ("collisions", toJson collisions),
    ("public_source_theorems", toJson rows),
    ("all_native_theorem_constants", toJson nativeScope)]
  liftIO <| IO.println ("STATISTICAL_RISK_NATIVE_JSON " ++ output.compress)
  unless collisions.isEmpty do throwError "STATISTICAL_RISK_OVERLAY_TYPE_COLLISION"
