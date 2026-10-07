import UEOT.V3.Compression.Objecthood.OntogeneticConstruction.ConstructionKernel
import UEOT.V3.Compression.Objecthood.JointHomeostasis.FiniteBurden

/-!
# Theory Completion P7.2 — entry into the maintenance regime

The P7 assembler is connected to the already-proved P5 maintenance carrier.
The theorem below does not assume that a fully formed organization is present in
the seed: only a physical component and a repair-program source are supplied.
Controller state and encoded mutable repair state are produced by the assembler.
-/

namespace UEOT.V3.Compression.Objecthood.OntogeneticConstruction

open Set MeasureTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis

universe uX uA uP uR
noncomputable section

/-- A physically admissible seed whose program is valid constructs directly into
P5's exact joint-legitimate set. -/
theorem seed_constructs_jointLegitimate
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (K : Set X)
    (seed : OntogeneticSeed X Program)
    (hx : seed.physicalComponent ∈ K) :
    assembleRepairOrganization T codec seed ∈
      jointLegitimate T codec K seed.repairProgramSource :=
  assembleRepairOrganization_mem_jointLegitimate T codec K seed hx

/-- Under the existing finite P5 assumptions, the freshly assembled organization
is already inside the finite repair carrier from which recurrent homeostasis is
certified. -/
theorem seed_constructs_finiteMaintenanceCarrier
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
    assembleRepairOrganization T codec seed ∈
      finiteJointRepairCarrier P K R T codec seed.repairProgramSource := by
  apply jointLegitimate_subset_finiteJointRepairCarrier
    P K R T codec seed.repairProgramSource hvalid
  exact seed_constructs_jointLegitimate T codec K seed hx

/-- The pure post-construction distribution is a legal P5 initial distribution
for the finite maintenance carrier. -/
theorem pure_assembled_stays_finiteMaintenanceCarrier
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
    StaysIn (PMF.pure (assembleRepairOrganization T codec seed))
      (finiteJointRepairCarrier P K R T codec seed.repairProgramSource) := by
  have hmem := seed_constructs_finiteMaintenanceCarrier
    P K R T codec seed hvalid hx
  simp [StaysIn, hmem]

end
end UEOT.V3.Compression.Objecthood.OntogeneticConstruction
