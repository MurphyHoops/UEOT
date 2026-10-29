import UEOT
namespace SecondEnergyPopulationConsumers
open MeasureTheory ProbabilityTheory Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianMartingaleSource BrownianPredictableInputs
open BrownianIntegralTimeEnergy BrownianIntegralCompensator BrownianIntegralContinuousVersion
open BrownianQuadraticVariation
open scoped ENNReal NNReal Topology
noncomputable section
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    Martingale (compensatedIntegral T f) naturalFiltration sourceLaw ∧
    ∀ᵐ w ∂sourceLaw, Monotone (fun s => timeEnergy T f s w) ∧
      Continuous (fun s => timeEnergy T f s w) := by
  refine ⟨compensatedIntegral_martingale T f, ?_⟩
  filter_upwards [timeEnergy_monotone_ae T f,timeEnergy_continuous_ae T f] with w hm hc
  exact ⟨hm,hc⟩
example (T : ℝ≥0) : Tendsto (fun n => quadraticVariationClass (uniformClock T n)) atTop
    (𝓝 (clockClass T)) := uniformQuadraticVariationClass_tendsto T
example : RegisterPopulationTypePrice.parentCount RegisterPopulationTypePrice.selectionStore = 2 :=
  RegisterPopulationTypePrice.selection_parentCount
example : RegisterPopulationTypePrice.birthCount (0 : Fin 1) ⟨true,1⟩
    RegisterPopulationTypePrice.selectionStore (fun _ => none) (fun _ => false) (fun _ => true) = 0 :=
  RegisterPopulationTypePrice.all_faults_birthCount_zero _ _ _ _ _
#check RegisterPopulationHistorySource.child_journal_parent_bridge
#check RegisterPopulationHistorySource.actual_child_enters_maintenance
#check RegisterPopulationTypePrice.actual_program_type_price
#check RegisterPopulationTypePrice.selection_and_empty_generation_witness
#print axioms BrownianIntegralCompensator.compensatedIntegral_martingale
#print axioms BrownianIntegralCompensator.compensatedIntegral_continuous_ae
#print axioms BrownianQuadraticVariation.uniformQuadraticVariationClass_tendsto
#print axioms BrownianIntegralSquareL1.actualSquareClass_tendsto
#print axioms RegisterPopulationTypePrice.actual_program_type_price
end
end SecondEnergyPopulationConsumers
