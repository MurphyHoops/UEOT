import UEOT.V3.Compression.Objecthood.OntogeneticConstruction.Boundaries

/-!
# Theory Completion P7.4 — terminal ontogenetic closure

The terminal theorem proves the finite benchmark promised by P7: an explicit
seed/components state is transformed into a formed organization with a bound
controller and encoded repair program, and that organization is admitted to the
already-proved P5 finite maintenance carrier.  P6 resource conclusions remain
available only after their additional budget/replenishment premises are supplied.
-/

namespace UEOT.V3.Compression.Objecthood.OntogeneticConstruction

open Set MeasureTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis

universe uX uA uP uR
noncomputable section

/-- **P7 terminal theorem.**  Construction is a genuine pre-formation → formed
transition, and the formed organization is a valid initial condition for P5's
finite recurrent-maintenance regime. -/
theorem p7_terminal_ontogenetic_selfConstruction
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program)
    (hvalid : RepairProgramValid T P K seed.repairProgramSource)
    (hx : seed.physicalComponent ∈ K) :
    constructionKernel (assembleRepairOrganization T codec)
        (OntogeneticState.seed seed) =
      PMF.pure (OntogeneticState.formed
        (assembleRepairOrganization T codec seed)) ∧
    ControllerImplementsProgram T
      (assembleRepairOrganization T codec seed).controller
      seed.repairProgramSource ∧
    assembleRepairOrganization T codec seed ∈
      jointLegitimate T codec K seed.repairProgramSource ∧
    StaysIn (PMF.pure (assembleRepairOrganization T codec seed))
      (finiteJointRepairCarrier P K R T codec seed.repairProgramSource) := by
  refine ⟨rfl, assembled_controller_implements_source T codec seed, ?_, ?_⟩
  · exact seed_constructs_jointLegitimate T codec K seed hx
  · exact pure_assembled_stays_finiteMaintenanceCarrier
      P K R T codec seed hvalid hx

end
end UEOT.V3.Compression.Objecthood.OntogeneticConstruction
