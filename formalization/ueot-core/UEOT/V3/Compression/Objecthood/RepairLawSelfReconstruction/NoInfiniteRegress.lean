import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.JointRecovery

/-!
# RLSR7 — finite trusted-boundary closure / no infinite repair regress

RLSR is intentionally relative to a trusted execution/decoder substrate.  This
module makes the dependency graph explicit and proves it is well founded.  The
result is a finite repair-of-repair architecture, not a claim of absolute
self-foundation.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

/-- Semantic layers in the concrete RLSR benchmark. -/
inductive RepairDependencyNode
  | trustedSubstrate
  | repairProgram
  | controller
  | physical
  deriving DecidableEq, Repr

/-- `RepairDependencyStep a b` means layer `b` depends on layer `a` for its
repair/reconstruction semantics. -/
inductive RepairDependencyStep :
    RepairDependencyNode → RepairDependencyNode → Prop
  | program : RepairDependencyStep .trustedSubstrate .repairProgram
  | controller : RepairDependencyStep .repairProgram .controller
  | physical : RepairDependencyStep .repairProgram .physical

/-- Strict layer rank from trusted boundary outward. -/
def repairDependencyRank : RepairDependencyNode → Nat
  | .trustedSubstrate => 0
  | .repairProgram => 1
  | .controller => 2
  | .physical => 2

/-- Every dependency edge strictly increases rank away from the trusted
substrate. -/
theorem repairDependencyRank_lt_of_step
    {a b : RepairDependencyNode}
    (h : RepairDependencyStep a b) :
    repairDependencyRank a < repairDependencyRank b := by
  cases h <;> decide

/-- The dependency relation is well founded when followed backward toward the
repair source. -/
theorem repairDependencyStep_wellFounded :
    WellFounded RepairDependencyStep := by
  apply (measure repairDependencyRank).wf.mono
  intro a b h
  exact repairDependencyRank_lt_of_step h

/-- The trusted substrate has no repair dependency inside the declared RLSR
architecture.  This is the explicit trusted boundary. -/
theorem trustedSubstrate_has_no_internal_repair_predecessor :
    ¬ ∃ a, RepairDependencyStep a .trustedSubstrate := by
  rintro ⟨a, h⟩
  cases h

/-- There is a genuine two-edge repair-of-repair chain: the trusted substrate
reconstructs repair-program organization, which in turn repairs controller and
physical state. -/
theorem exists_two_step_repair_chain :
    (RepairDependencyStep .trustedSubstrate .repairProgram ∧
      RepairDependencyStep .repairProgram .controller) ∧
    (RepairDependencyStep .trustedSubstrate .repairProgram ∧
      RepairDependencyStep .repairProgram .physical) := by
  exact ⟨⟨.program, .controller⟩, ⟨.program, .physical⟩⟩

/-- No three-edge dependency path exists in this benchmark. -/
theorem no_three_step_repair_regress
    {a b c d : RepairDependencyNode}
    (h₁ : RepairDependencyStep b a)
    (h₂ : RepairDependencyStep c b)
    (h₃ : RepairDependencyStep d c) :
    False := by
  cases h₁ <;> cases h₂ <;> cases h₃

/-- In particular, no infinite repairer-of-repairer regress exists relative to
the declared trusted substrate. -/
theorem no_infinite_repair_regress :
    ¬ ∃ f : Nat → RepairDependencyNode,
      ∀ n, RepairDependencyStep (f (n + 1)) (f n) := by
  rintro ⟨f, hf⟩
  exact no_three_step_repair_regress
    (hf 0) (by simpa using hf 1) (by simpa using hf 2)

end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
