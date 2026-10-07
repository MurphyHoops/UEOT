import UEOT.V3.Compression.Objecthood.OntogeneticConstruction.Boundaries

/-!
# Theory Completion P7.4 — terminal ontogenetic closure

The terminal theorem proves the finite benchmark promised by P7: an explicit
seed/components state is transformed by the specialized P7 assembler into a
formed organization with a bound controller and encoded repair program, and —
under the complete P5 hypotheses — that organization is a legal initial state
of the actual finite recurrent-homeostasis system.  P6 resource conclusions
remain available only after their additional budget/replenishment premises are
supplied.
-/

namespace UEOT.V3.Compression.Objecthood.OntogeneticConstruction

open Set MeasureTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis

universe uX uA uP uR
noncomputable section

/-- **P7 terminal theorem.**  This is a conditional trusted ontogenetic assembly
benchmark, not construction ex nihilo.  The output is a valid initial condition
for the actual P5 finite recurrent-maintenance system. -/
theorem p7_terminal_ontogenetic_assembly
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A] [Nonempty A] [Fintype Representation]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T P
      seed.repairProgramSource
      (repairThenPreservePolicy P K hfix R.repairPolicy))
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : FiniteJointFaultEnvelope P K R T codec
      seed.repairProgramSource F)
    (hx : seed.physicalComponent ∈ K) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec seed.repairProgramSource himpl
      F epsilon hepsilon hF
    ontogeneticConstructionKernel T codec
        (OntogeneticState.seed seed) =
      PMF.pure (OntogeneticState.formed
        (assembleRepairOrganization T codec seed)) ∧
    ControllerImplementsProgram T
      (assembleRepairOrganization T codec seed).controller
      seed.repairProgramSource ∧
    assembleRepairOrganization T codec seed ∈
      S.legitimate ∧
    StaysIn (PMF.pure (assembleRepairOrganization T codec seed))
      S.carrier := by
  dsimp only
  have hvalid : RepairProgramValid T P K seed.repairProgramSource :=
    repairProgramValid_of_dynamicsImplements_repairThenPreserve
      T P K hfix R.repairPolicy seed.repairProgramSource himpl
  refine ⟨rfl, assembled_controller_implements_source T codec seed, ?_, ?_⟩
  · exact seed_constructs_jointLegitimate T codec K seed hx
  · exact pure_assembled_stays_p5MaintenanceSystem
      P K hfix R T codec seed himpl F epsilon hepsilon hF hx

end
end UEOT.V3.Compression.Objecthood.OntogeneticConstruction
