import UEOT.V3.Compression.Objecthood.OntogeneticConstruction.Assembly

/-!
# Theory Completion P7.1 — typed construction transition

A construction process has a typed pre-formation state and a formed state.
The one-step deterministic benchmark is specialized to the explicit P7 seed
and the declared trusted assembler.  This blocks the degenerate instantiation
`Seed := Org; assemble := id` that would merely relabel an already formed
organization as a seed.  Repair acts only after the formed organization exists.
-/

namespace UEOT.V3.Compression.Objecthood.OntogeneticConstruction

open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

universe uSeed uOrg uX uA uP uR

/-- Pre-formation and post-formation states are different constructors. -/
inductive OntogeneticState (Seed : Type uSeed) (Org : Type uOrg)
  | seed : Seed → OntogeneticState Seed Org
  | formed : Org → OntogeneticState Seed Org
  deriving DecidableEq

/-- Deterministic one-step P7 construction benchmark.  Its source and target
types are fixed to the explicit ontogenetic seed and repair-organization state,
and the only constructor used is `assembleRepairOrganization`.  Formed
organizations are absorbing for this construction-only kernel; their subsequent
maintenance is a separate P5/P6 kernel. -/
noncomputable def ontogeneticConstructionKernel
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation) :
    OntogeneticState (OntogeneticSeed X Program)
      (RepairOrganizationState X A Representation) →
      PMF (OntogeneticState (OntogeneticSeed X Program)
        (RepairOrganizationState X A Representation))
  | .seed s => PMF.pure (.formed (assembleRepairOrganization T codec s))
  | .formed o => PMF.pure (.formed o)

@[simp] theorem ontogeneticConstructionKernel_seed
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (s : OntogeneticSeed X Program) :
    ontogeneticConstructionKernel T codec (.seed s) =
      PMF.pure (.formed (assembleRepairOrganization T codec s)) := rfl

@[simp] theorem ontogeneticConstructionKernel_formed
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (o : RepairOrganizationState X A Representation) :
    ontogeneticConstructionKernel T codec (.formed o) =
      PMF.pure (.formed o) := rfl

/-- A seed state is definitionally distinct from every formed state.  This is a
small but useful type-level guard against silently relabeling repair as
construction. -/
theorem seed_ne_formed
    {Seed : Type uSeed} {Org : Type uOrg}
    (s : Seed) (o : Org) :
    (OntogeneticState.seed s : OntogeneticState Seed Org) ≠
      OntogeneticState.formed o := by
  intro h
  cases h

/-- The typed P7 construction kernel enters any target predicate satisfied by
the explicitly assembled repair organization with probability one. -/
theorem ontogeneticConstructionKernel_seed_staysIn_formedTarget
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (Ready : RepairOrganizationState X A Representation → Prop)
    (s : OntogeneticSeed X Program)
    (hready : Ready (assembleRepairOrganization T codec s)) :
    UEOT.V3.ViabilityKernel.StaysIn
      (ontogeneticConstructionKernel T codec (.seed s))
      {q : OntogeneticState (OntogeneticSeed X Program)
          (RepairOrganizationState X A Representation) |
        ∃ o, Ready o ∧ q = .formed o} := by
  intro q hq
  have hqeq : q = OntogeneticState.formed
      (assembleRepairOrganization T codec s) := by
    simpa [ontogeneticConstructionKernel] using hq
  subst q
  exact ⟨assembleRepairOrganization T codec s, hready, rfl⟩

end UEOT.V3.Compression.Objecthood.OntogeneticConstruction
