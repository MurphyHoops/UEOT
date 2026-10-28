import UEOT
import Lean.Elab.Command
open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 16384
run_cmd do
  let env ← getEnv
  let requested : Array String := #[
    "UEOT.V3.Compression.ActionGapGaugeStability.targetGreedy_eq_transportedSourceGreedy",
    "UEOT.V3.Compression.ApproximateHistoryEncoder.representativeMacroModel_transitionPMF",
    "UEOT.V3.Compression.ApproximateSemanticGauge.pushforwardTransitionPMF_relabel",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConditionedActionTransportCheck.occupied_conditioned_fibers_supply_actual_experiment",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.acceptedWeights",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.cast_fiberScore",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.checkNegative_path_no_go",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.checkNegative_sound",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.checkPositive_sound",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.checkPositive_sound_rows",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.occupied_iff",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.pathMass_eq",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck.rowPMF_toReal",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.independent_baseline_variant.output_actual_path",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.original_actions.conditional_path_no_go",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.same_source_alias.conditional_path_no_go",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.two_step_added_actions.output_actual_path",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.unprepared_initial.conditional_path_no_go",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.unprepared_initial.every_causal_path_tv_obstacle",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.unreachable_fallback.output_actual_path",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.zero_horizon.output_actual_path",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitnessCheck.zero_survival.zero_survival_event",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.actual_state_path_eq_target",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.initial_tv_le_path_tv",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck.realRow_actionMixture",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPathCheck.causal_path_eq_iff",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPathCheck.full_path_eq_prefix",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPathCheck.specified_policy_conditioned_path_iff",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPathCheck.specified_policy_path_iff",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPathCheck.specified_policy_path_of_rows",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobCheck.doobRowPMF_apply_toReal",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.HomogeneousMemorySurvival.augmentedModel_transitionPMF",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracle.empiricalMass_eq",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.actualSource_pos",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.baselineRow_cast",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.baselineRow_nonneg",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.rationalModel_transitionPMF",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.rationalRemaining_cast",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.rationalRemaining_nonneg",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceInitial_eq_prepared",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceInitial_valid",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceMass_eq_actual",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceRemaining_eq_actual",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceRemaining_nonneg",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceRemaining_succ",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceTargetPath_eq_actual",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceTarget_eq_row",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck.sourceTarget_valid",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceFiniteWindowCheck.finiteWindowRowPMF_apply_toReal",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceFiniteWindowCheck.remainingSurvival_nonneg",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceFiniteWindowCheck.remainingSurvival_succ",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceFiniteWindowCheck.remainingSurvival_zero",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.causalLaw_map_prefix",
    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindowCheck.generated_ambient_eq_actual",
    "UEOT.V3.DynamicsKernel.pathMeasure_eq_of_prefix_eq",
    "UEOT.V3.FiniteCTMCPathKL.sourceRateIntegrand_nonneg",
    "UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal",
    "UEOT.V3.FiniteDobrushin.rowPMF_toReal",
    "UEOT.V3.FiniteDobrushin.simplexPMF_toReal",
    "UEOT.V3.QSDTVLimit.qSurvival_zero",
    "UEOT.V3.SymmetricKilledSpectralStability.squarePMF_toReal"
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
