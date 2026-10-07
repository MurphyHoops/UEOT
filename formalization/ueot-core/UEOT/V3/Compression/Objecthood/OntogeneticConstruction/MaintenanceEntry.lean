import UEOT.V3.Compression.Objecthood.OntogeneticConstruction.ConstructionKernel
import UEOT.V3.Compression.Objecthood.JointHomeostasis.FiniteBurden

/-!
# Theory Completion P7.2 — entry into the P5 maintenance regime

The P7 assembler is connected to the already-proved P5 maintenance system.
Carrier membership and actual recurrent-homeostasis-system entry are kept
separate: the latter threads the full P5 policy bridge, viability fixed point,
finite representation, fault envelope and hazard premises instead of inferring a
maintenance regime from a Dirac-law support fact.
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

/-- Under the full P5 premises, the freshly assembled organization is a legal
initial law for the *actual* finite recurrent-homeostasis system, not merely a
member of a similarly named carrier. -/
theorem pure_assembled_stays_p5MaintenanceSystem
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
    StaysIn (PMF.pure (assembleRepairOrganization T codec seed)) S.carrier := by
  dsimp only
  have hvalid : RepairProgramValid T P K seed.repairProgramSource :=
    repairProgramValid_of_dynamicsImplements_repairThenPreserve
      T P K hfix R.repairPolicy seed.repairProgramSource himpl
  exact pure_assembled_stays_finiteMaintenanceCarrier
    P K R T codec seed hvalid hx

end
end UEOT.V3.Compression.Objecthood.OntogeneticConstruction
