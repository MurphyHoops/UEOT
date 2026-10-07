import UEOT.V3.Compression.Objecthood.JointHomeostasis.RepairCarrier

/-!
# Theory Completion P7.0 — conditional ontogenetic assembly adapter

Ontogenetic construction is kept distinct from repair.  A seed supplies a
physical component and an internal repair-program source, but does not already
contain a controller or encoded mutable repair representation.  The trusted
assembler creates those two organizational coordinates from the seed.

This is an explicit *trusted assembly adapter*.  The generic UEOT layer does not
derive the physical assembly map from Objecthood.  A domain implementation must
independently justify that its component-to-physical map is an actual formation
mechanism.  In particular, the existence of the functions below is not itself a
theorem of nontrivial self-construction.
-/

namespace UEOT.V3.Compression.Objecthood.OntogeneticConstruction

open Set
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis

universe uC uX uA uP uR

/-- Domain-supplied component assembly plan.  Unlike `OntogeneticSeed`, its
input need not already have the physical-state type `X`.  The plan is still an
adapter: P7 does not derive `physicalAssembly` or `programSource` from generic
Objecthood. -/
structure OntogeneticAssemblyPlan
    (Component : Type uC) (X : Type uX) (Program : Type uP) where
  physicalAssembly : Component → X
  programSource : Component → Program

/-- Minimal P7 seed/components package.  It deliberately omits the controller
and the encoded mutable repair-program representation; those are assembled. -/
structure OntogeneticSeed (X : Type uX) (Program : Type uP) where
  physicalComponent : X
  repairProgramSource : Program

/-- Turn one domain component package into the seed consumed by the
organizational assembler. -/
def OntogeneticAssemblyPlan.toSeed
    {Component : Type uC} {X : Type uX} {Program : Type uP}
    (plan : OntogeneticAssemblyPlan Component X Program)
    (components : Component) : OntogeneticSeed X Program :=
  { physicalComponent := plan.physicalAssembly components
    repairProgramSource := plan.programSource components }

@[simp] theorem OntogeneticAssemblyPlan.toSeed_physical
    {Component : Type uC} {X : Type uX} {Program : Type uP}
    (plan : OntogeneticAssemblyPlan Component X Program)
    (components : Component) :
    (plan.toSeed components).physicalComponent =
      plan.physicalAssembly components := rfl

@[simp] theorem OntogeneticAssemblyPlan.toSeed_program
    {Component : Type uC} {X : Type uX} {Program : Type uP}
    (plan : OntogeneticAssemblyPlan Component X Program)
    (components : Component) :
    (plan.toSeed components).repairProgramSource =
      plan.programSource components := rfl

/-- Assemble a repair organization from seed components. -/
def assembleRepairOrganization
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program) :
    RepairOrganizationState X A Representation :=
  canonicalRepairOrganizationState T codec
    seed.repairProgramSource seed.physicalComponent

@[simp] theorem assembleRepairOrganization_physical
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program) :
    (assembleRepairOrganization T codec seed).physical =
      seed.physicalComponent := rfl

@[simp] theorem assembleRepairOrganization_controller
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program) :
    (assembleRepairOrganization T codec seed).controller =
      T.execute seed.repairProgramSource := rfl

@[simp] theorem assembleRepairOrganization_program
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program) :
    (assembleRepairOrganization T codec seed).repairProgram =
      codec.encode seed.repairProgramSource := rfl

/-- If the seed's physical component is already in the declared target, its
assembled organization is exactly a P5 legitimate organization for the seed's
own repair program. -/
theorem assembleRepairOrganization_mem_jointLegitimate
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (K : Set X)
    (seed : OntogeneticSeed X Program)
    (hx : seed.physicalComponent ∈ K) :
    assembleRepairOrganization T codec seed ∈
      jointLegitimate T codec K seed.repairProgramSource := by
  exact ⟨seed.physicalComponent, hx, rfl⟩

/-- The assembler genuinely installs a controller implementing the seed's
internal program; the controller is not supplied as a seed field. -/
theorem assembled_controller_implements_source
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program) :
    ControllerImplementsProgram T
      (assembleRepairOrganization T codec seed).controller
      seed.repairProgramSource := by
  rfl

end UEOT.V3.Compression.Objecthood.OntogeneticConstruction
