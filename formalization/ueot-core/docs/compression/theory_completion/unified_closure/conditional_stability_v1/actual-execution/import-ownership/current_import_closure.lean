import UEOT.V3.Compression.TheoryCompletion
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let sourceModules : Array Name := #[
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ActiveHiddenOptimalControlExample,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BeliefTimingBoundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.C3ExecutableSearch,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CalibratedDeploymentJoint,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CalibratedRiskRows,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ControlCoverageWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreInfinitePathClosure,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreNonvacuousAllTimesWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CorePMFViabilityReconciliation,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreSourceAllTimesAssembly,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DependentEventFormationBudget,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverageWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeterministicDiracPredictiveBridge,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveGaugeCompleteness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveLinearGauge,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportController,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportControllerWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteCommonProcessWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStabilityWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteFormationBoundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteHorizonPathAdapter,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteHorizonRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryCheckWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPolicy,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryRealization,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySafetyWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySeparation,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePMFProjection,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePredictiveProbeCompleteness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportFixedPoint,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViabilityCheck,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoob,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FixedSampleSupportNoGo,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.HomogeneousMemorySurvival,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.InfiniteSupportViability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurableProcessTransport,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MultiScaleExactControlComposition,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MultiScaleFiniteWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracle,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracleWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotient,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotientWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OrganizationalCoreAssembly,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OrganizationalSufficiencyWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OrganizationalViabilityMaximality,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportCoverage,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveGoalClosureBoundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveOptimalControlLift,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveViabilityTransport,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ProgramPurposeInformationBoundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ReachablePolicyExtension,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRisk,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRiskWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RepairProgramSafeControlBridge,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RowwiseProbeSampling,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SISCRowwiseProbeCalibration,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SISCRowwiseProbeWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeCausalHistoryTransport,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeOptimalControlFromViability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeRewardConflictWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminal,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceFiniteWindow,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceInfinitePrefix,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFlux,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledPath,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceQSDBinding,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceSafePrefix,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceSurvivalTail,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourcePolicyPathBridge,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskBoundary,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticHiddenAliasExample,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPersistentHiddenExample,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveNullspace,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveObservabilityBridge,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveRobustObservability,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportMemoryCheck,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportMemoryController,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindow,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindowWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentJoint,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TwoStageCommonProcessExample,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TwoStageFormationTransport,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.UnifiedCoreClosureCertificate,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJoint,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViabilityKernelIntertwining,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViabilityNonvacuityWitness,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableRegisteredJoint,
    `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableVariableRegisteredJoint,
  ]
  for sourceModule in sourceModules do
    unless env.header.moduleNames.contains sourceModule do
      throwError s!"UMC_COMPILED_SOURCE_MODULE_MISSING {sourceModule}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        let sourceModule := env.header.moduleNames[idx]!
        if sourceModules.contains sourceModule then
          let actual ← Lean.collectAxioms name
          let unexpected := actual.filter fun ax => !allowed.contains ax
          unless unexpected.isEmpty do
            throwError s!"UMC_NONSTANDARD_AXIOM {name}: {unexpected}"
          rows := rows.push <| Json.mkObj [
            ("name", toJson name.toString),
            ("source_module", toJson sourceModule.toString),
            ("is_private", toJson (Lean.privateToUserName? name).isSome),
            ("axioms", toJson (actual.map Name.toString))]
  unless rows.size > 0 do throwError "UMC_NATIVE_SCOPE_EMPTY"
  let report := Json.mkObj [
    ("schema", toJson "UMC_NATIVE_AXIOM_CENSUS_V1"),
    ("source_modules", toJson (sourceModules.map Name.toString)),
    ("theorems", toJson rows)]
  liftIO <| IO.println ("UMC_NATIVE_AUDIT_JSON " ++ report.compress)
