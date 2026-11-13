import UEOT.V3.PredictionDependent
import UEOT.V3.FiniteDiscountedControl
import UEOT.V3.FiniteDiscountedGreedy
import UEOT.V3.CoreOperationalAssembly
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeRepair
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFormation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure
import docs.compression.theory_completion.unified_closure.core_growth_classification_v1.GrowthClassificationCheck
import UEOT
import UEOT.V3.OmegaMinimalFailure
import UEOT.V3.CommonBottleneckRank
import UEOT.V3.DiffusionHJBVerification
import UEOT.V3.SelectionBridge
import UEOT.V3.Compression.TheoryCompletion.GOA
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer

/- D3 targeted fixed-source reproduction probe.
   Prepared but NOT executed in the preparation environment.
   This file adds no production theorem. Review the runner receipt for actual execution. -/

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

-- Print structures/definitions that carry the critical assumptions.
#print UEOT.V3.FiniteDiscountedControl.Model
#print UEOT.V3.CoreOperationalAssembly.FixedSourceApproximation
#print UEOT.V3.CoreOperationalAssembly.CorePointwiseCertificate
#print UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.Valid
#print UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation.ValidIdentity
#print UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.Policy
#print UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.State
#print UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.ProgramPopulation
#print UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.ProbabilityValid
#print UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.HasExpectedGrowth
#print UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.UniformExpectedUpper
#print UEOT.V3.SelectionBridge.ReplicationBridge

-- prediction/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/PredictionDependent.lean
#check @UEOT.V3.PredictionDependent.canonical_ae_minimal
#print axioms UEOT.V3.PredictionDependent.canonical_ae_minimal

-- prediction/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/PredictionDependent.lean
#check @UEOT.V3.PredictionDependent.canonical_ae_sigma_minimal
#print axioms UEOT.V3.PredictionDependent.canonical_ae_sigma_minimal

-- prediction/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/PredictionDependent.lean
#check @UEOT.V3.PredictionDependent.canonical_kernel_sufficient
#print axioms UEOT.V3.PredictionDependent.canonical_kernel_sufficient

-- control/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/FiniteDiscountedControl.lean
#check @UEOT.V3.FiniteDiscountedControl.Model.fixedPoint_unique
#print axioms UEOT.V3.FiniteDiscountedControl.Model.fixedPoint_unique

-- control/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/FiniteDiscountedGreedy.lean
#check @UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality
#print axioms UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality

-- assembly/K2-K3 | fresh_recompiled | formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean
#check @UEOT.V3.CoreOperationalAssembly.optimal_qValue_macro_error_le_D
#print axioms UEOT.V3.CoreOperationalAssembly.optimal_qValue_macro_error_le_D

-- assembly/K2-K3 | fresh_recompiled | formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean
#check @UEOT.V3.CoreOperationalAssembly.macro_gap_certifies_micro_action
#print axioms UEOT.V3.CoreOperationalAssembly.macro_gap_certifies_micro_action

-- assembly/K2-K3 | fresh_recompiled | formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean
#check @UEOT.V3.CoreOperationalAssembly.p_core_01
#print axioms UEOT.V3.CoreOperationalAssembly.p_core_01

-- same-source/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeSource.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.realizedMean_eq
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.realizedMean_eq

-- repair/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeRepair.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.programStep_uses_paid_repair
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.programStep_uses_paid_repair

-- repair/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeRepair.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.source_strongRepairable
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.source_strongRepairable

-- formation/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeFormation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.actual_formed_candidate_family_nonempty
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.actual_formed_candidate_family_nonempty

-- formation/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeFormation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.actual_formed_candidate_nonempty
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.actual_formed_candidate_nonempty

-- identity/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativePopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation.newborn_fresh_from_old_population
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation.newborn_fresh_from_old_population

-- identity/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativePopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation.actualStep_budget
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation.actualStep_budget

-- identity/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativePopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation.descendants_length
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation.descendants_length

-- program-and-transport/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeControlPopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.step_outputs_program
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.step_outputs_program

-- program-and-transport/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeControlPopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.reachable_program
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.reachable_program

-- program-and-transport/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeControlPopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.populationExpectation_eraseState
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.populationExpectation_eraseState

-- program-and-transport/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeControlPopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.attainable_test_values_eraseState
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.attainable_test_values_eraseState

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.valid_iff_probability_advantage_supercritical
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.valid_iff_probability_advantage_supercritical

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.optimalRate_formula
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.optimalRate_formula

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.actual_one_step_value_le
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.actual_one_step_value_le

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.actual_selected_one_step_value_eq
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.actual_selected_one_step_value_eq

-- growth/K1-K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.optimal_population_upper
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.optimal_population_upper

-- growth/K1-K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.optimal_hasExpectedGrowth
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.optimal_hasExpectedGrowth

-- growth/K1-K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.programPolicy_positive_branch_is_internal
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.programPolicy_positive_branch_is_internal

-- growth/K1-K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.founder_program
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.founder_program

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.optimalRate_isLeast_uniform_upper
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.optimalRate_isLeast_uniform_upper

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.false_program_attains_iff
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.false_program_attains_iff

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.true_program_attains_iff
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.true_program_attains_iff

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.same_damaged_program_repairs_and_attains_iff
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.same_damaged_program_repairs_and_attains_iff

-- growth/K1 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.subcritical_existing_programs_do_not_attain
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.subcritical_existing_programs_do_not_attain

-- same-source-public/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreTheoryClosure.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure.same_program_regenerates_and_attains
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure.same_program_regenerates_and_attains

-- same-source-public/K2 | fresh_recompiled | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreTheoryClosure.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure.positive_source_class_nonempty
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure.positive_source_class_nonempty

-- boundary-consumer/K4 | fresh_recompiled | formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/GrowthClassificationCheck.lean
#check @UEOTGrowthClassificationCheck.enlarged_domain_actual_internal
#print axioms UEOTGrowthClassificationCheck.enlarged_domain_actual_internal

-- boundary-consumer/K4 | fresh_recompiled | formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/GrowthClassificationCheck.lean
#check @UEOTGrowthClassificationCheck.subcritical_actual_internal_failure
#print axioms UEOTGrowthClassificationCheck.subcritical_actual_internal_failure

-- retained-boundary | fresh_probe_of_reused_olean | formalization/ueot-core/UEOT/V3/OmegaMinimalFailure.lean
#check @UEOT.V3.OmegaMinimalFailure.p_omg_01
#print axioms UEOT.V3.OmegaMinimalFailure.p_omg_01

-- retained-boundary | fresh_probe_of_reused_olean | formalization/ueot-core/UEOT/V3/CommonBottleneckRank.lean
#check @UEOT.V3.CommonBottleneckRank.p_ddh_04
#print axioms UEOT.V3.CommonBottleneckRank.p_ddh_04

-- retained-boundary | fresh_probe_of_reused_olean | formalization/ueot-core/UEOT/V3/DiffusionHJBVerification.lean
#check @UEOT.V3.DiffusionHJBVerification.p_ctl_03
#print axioms UEOT.V3.DiffusionHJBVerification.p_ctl_03

-- retained-boundary | fresh_probe_of_reused_olean | formalization/ueot-core/UEOT/V3/SelectionBridge.lean
#check @UEOT.V3.SelectionBridge.ReplicationBridge.behavior_equiv_fitness_eq
#print axioms UEOT.V3.SelectionBridge.ReplicationBridge.behavior_equiv_fitness_eq

-- retained-boundary | fresh_probe_of_reused_olean | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/GOA.lean
#check @UEOT.V3.Compression.TheoryCompletion.greedyInvariantGOASet_nonempty
#print axioms UEOT.V3.Compression.TheoryCompletion.greedyInvariantGOASet_nonempty

-- disclosed-native/K4 | fresh_probe_of_reused_olean | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionConsumer.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer.exact_cached_data
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer.exact_cached_data

-- disclosed-native/K4 | fresh_probe_of_reused_olean | formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionConsumer.lean
#check @UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer.exact_two_data
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer.exact_two_data

