import UEOT.V3.Compression.Objecthood.OntogeneticConstruction.MaintenanceEntry

/-!
# Theory Completion P7.3 — construction boundaries

P7 is ontogenetic construction under an explicit assembler.  It is not a theorem
that repair alone can generate missing organizational information, nor a theorem
of origin from an empty substrate.
-/

namespace UEOT.V3.Compression.Objecthood.OntogeneticConstruction

open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

universe uX uA uP uR

/-- Distinct repair-program sources have distinct trusted encodings.  Hence the
program source carried by the seed is real information; the assembler does not
create it from nothing. -/
theorem encode_injective
    {Program : Type uP} {Representation : Type uR}
    (codec : TrustedRepairCodec Program Representation) :
    Function.Injective codec.encode := by
  intro r₁ r₂ h
  calc
    r₁ = codec.decode (codec.encode r₁) := (codec.decode_encode r₁).symm
    _ = codec.decode (codec.encode r₂) := congrArg codec.decode h
    _ = r₂ := codec.decode_encode r₂

/-- Two seeds with the same physical component but distinct internal program
sources assemble to different mutable repair-program representations. -/
theorem distinct_program_sources_assemble_distinct_program_state
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (x : X) {r₁ r₂ : Program} (hne : r₁ ≠ r₂) :
    (assembleRepairOrganization T codec
      ({ physicalComponent := x, repairProgramSource := r₁ } :
        OntogeneticSeed X Program)).repairProgram ≠
    (assembleRepairOrganization T codec
      ({ physicalComponent := x, repairProgramSource := r₂ } :
        OntogeneticSeed X Program)).repairProgram := by
  simp only [assembleRepairOrganization_program]
  exact fun h => hne (encode_injective codec h)

/-- Construction and already-formed maintenance are separated at the type level. -/
theorem construction_state_not_formed_state
    {Seed : Type*} {Org : Type*} (s : Seed) (o : Org) :
    (OntogeneticState.seed s : OntogeneticState Seed Org) ≠
      OntogeneticState.formed o :=
  seed_ne_formed s o

end UEOT.V3.Compression.Objecthood.OntogeneticConstruction
