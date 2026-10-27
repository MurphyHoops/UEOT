import UEOT
import Lean.Elab.Command
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 16384
run_cmd do
  let env ← getEnv
  let requested : Array String := #[
    "*.risk_bind_apply_toReal",
    "PMF.bind_apply",
    "UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC.third_singular_zero_of_rank_le_two",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConditionedActionTransportCheck.occupied_conditioned_fibers_supply_actual_experiment",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConditionedActionTransportCheck.occupied_fibers_supply_actual_path",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConditionedActionTransportCheck.state_selection_realizes_its_conditioned_path",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConditionedActionTransportCheck.time_action_state_path_eq_mixture",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.actual_next_state_eq_target",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.actual_state_path_eq_target",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.causalLaw_initial_marginal",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.initial_tv_le_path_tv",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.observation_realizable_iff_fiber_convexHull",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.path_implementation_requires_initial",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.pmf_barycenter_exists_iff_mem_convexHull",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.realRow_actionMixture",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.row_realizable_iff_mem_convexHull",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.stationary_row_eq_actionMixture",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck.actual_conditioning_changes_initial_tv",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck.added_safe_actions_realize_conditional_row",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck.conditional_row_outside_original_action_hull",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck.deterministic_extended_action_does_not_realize",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck.no_common_policy_for_aliased_rows",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck.original_actions_have_irreducible_conditional_error",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck.separately_feasible_hidden_rows",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck.unchanged_initial_forces_path_error",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability.mass_mul_conditioned_atom",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobWitnessCheck.actual_conditioned_doob_tv",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobWitnessCheck.conditioned_safe_atom",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.EmptyCommonAction.each_state_has_a_certified_action",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverageCheck.EmptyCommonAction.no_common_certified_action",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportStrictWitness.whole_current_fiber_has_no_common_action",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceFiniteWindowCheck.actual_conditioned_initial_mass",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.causalLaw_map_prefix",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.pmfExtend_map_fst",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridgeCheck.actual_next_state_eq_stationary_row",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridgeCheck.actual_state_path_eq_stationary_path",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindowCheck.generated_ambient_eq_actual",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.fixed_injective_latent_decoder_identifies_latents",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.labelled_axis_lines_iff_nonzero_diagonal_gauge",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.latent_GL2_reparameterization_preserves_all_responses",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.nondegenerate_linear_factorization_unique_gauge",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.one_unit_anchor_leaves_nontrivial_gauge",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.oriented_axis_rays_iff_positive_diagonal_gauge",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.phi_identified_of_pi_anchor",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.pi_identified_of_phi_anchor",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.registered_unit_interventions_identify_factorization",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_tv_bind_same_weights",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_linear_response_iff_unique_gauge",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_objective_iff_gauge_related",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.two_drive_GL2_gauge_is_nontrivial",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.two_oriented_axes_do_not_identify_units",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.two_unit_anchors_identify_gauge",
    "UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal",
    "UEOT.V3.CoreOperationalAssembly.policyTransitionPMF_apply_toReal",
    "UEOT.V3.TotalVariation.tvDist_map_le",
    "convexHull_range_eq_exists_affineCombination",
    "mem_convexHull_of_exists_fintype",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety.actual_state_prefix_eq",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.risk_causalLaw_map",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.riskFiberPosterior_support",
  ]
  let mut rows : Array Json := #[]
  for request in requested do
    let exactName := request.toName
    let suffix := "." ++ (request.splitOn ".").getLast!
    let candidates := env.constants.toList.filter fun (name, _) => name.toString.endsWith suffix
    let name ← if (env.find? exactName).isSome then pure exactName else do
      unless candidates.length == 1 do throwError s!"REUSE_NAME_NOT_UNIQUE {request}: {candidates.map (fun x => x.1)}"
      pure candidates.head!.1
    let some info := env.find? name | throwError s!"REUSE_SYMBOL_MISSING {request}"
    let rendered ← liftTermElabM do ppExpr info.type
    let owner := (env.getModuleIdxFor? name).map fun idx => env.header.moduleNames[idx]!.toString
    let axs ← Lean.collectAxioms name
    rows := rows.push <| Json.mkObj [("requested", toJson request), ("name", toJson name.toString),
      ("source_module", toJson owner), ("is_private", toJson (Lean.privateToUserName? name).isSome),
      ("type", toJson rendered.pretty), ("axioms", toJson (axs.map Name.toString))]
  liftIO <| IO.println ("TYPED_REUSE_ACTUAL_JSON " ++ (toJson rows).compress)
