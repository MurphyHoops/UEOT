import UEOT.V3.Compression.Objecthood.OntogeneticConstruction.Assembly

/-!
# Theory Completion P7.1 — construction transition

A construction process has a typed pre-formation state and a formed state.
The one-step deterministic benchmark makes the distinction between ontogeny and
repair explicit: repair acts only after the formed organization exists.
-/

namespace UEOT.V3.Compression.Objecthood.OntogeneticConstruction

universe uSeed uOrg

/-- Pre-formation and post-formation states are different constructors. -/
inductive OntogeneticState (Seed : Type uSeed) (Org : Type uOrg)
  | seed : Seed → OntogeneticState Seed Org
  | formed : Org → OntogeneticState Seed Org
  deriving DecidableEq

/-- Deterministic one-step construction benchmark.  Formed organizations are
absorbing for this construction-only kernel; their subsequent maintenance is a
separate P5/P6 kernel. -/
noncomputable def constructionKernel
    {Seed : Type uSeed} {Org : Type uOrg}
    (assemble : Seed → Org) :
    OntogeneticState Seed Org → PMF (OntogeneticState Seed Org)
  | .seed s => PMF.pure (.formed (assemble s))
  | .formed o => PMF.pure (.formed o)

@[simp] theorem constructionKernel_seed
    {Seed : Type uSeed} {Org : Type uOrg}
    (assemble : Seed → Org) (s : Seed) :
    constructionKernel assemble (.seed s) =
      PMF.pure (.formed (assemble s)) := rfl

@[simp] theorem constructionKernel_formed
    {Seed : Type uSeed} {Org : Type uOrg}
    (assemble : Seed → Org) (o : Org) :
    constructionKernel assemble (.formed o) =
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

/-- The construction kernel enters any target predicate satisfied by the
assembled organization with probability one. -/
theorem constructionKernel_seed_staysIn_formedTarget
    {Seed : Type uSeed} {Org : Type uOrg}
    (assemble : Seed → Org) (Ready : Org → Prop)
    (s : Seed) (hready : Ready (assemble s)) :
    UEOT.V3.ViabilityKernel.StaysIn
      (constructionKernel assemble (.seed s))
      {q : OntogeneticState Seed Org |
        ∃ o, Ready o ∧ q = .formed o} := by
  intro q hq
  have hqeq : q = OntogeneticState.formed (assemble s) := by
    simpa [constructionKernel] using hq
  subst q
  exact ⟨assemble s, hready, rfl⟩

end UEOT.V3.Compression.Objecthood.OntogeneticConstruction
