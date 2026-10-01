import UEOT.V3.Compression.TeleologicalEquivalence
import UEOT.V3.SelectionBridge

namespace UEOT.V3.Compression.Hierarchy

open UEOT.Reward
open UEOT.V3.Compression.TeleologicalEquivalence
open UEOT.V3.SelectionBridge
open UEOT.V3.SelectionBridge.ReplicationBridge

/-- A carrier/state space alone does not determine a unique objective or
maximizer set: there exist two objectives on the same finite carrier that are
not maximizer-equivalent. -/
theorem carrier_does_not_determine_maximizers :
    ∃ f g : Bool → ℝ, ¬ MaximizerEquivalent f g := by
  let f : Bool → ℝ := fun b => if b then 1 else 0
  let g : Bool → ℝ := fun b => if b then 0 else 1
  refine ⟨f, g, ?_⟩
  intro h
  have hg : IsMaximizer g false := by
    intro q
    cases q <;> simp [g]
  have hf : IsMaximizer f false := (h false).mp hg
  have hbad := hf true
  norm_num [f] at hbad

/-- Behavioral response alone does not determine replication/selection
semantics: two bridges can have the same response map and different fitness. -/
theorem response_does_not_determine_fitness :
    ∃ B₀ B₁ : ReplicationBridge Bool Bool,
      B₀.response = B₁.response ∧
      B₀.fitness false ≠ B₁.fitness false := by
  let B₀ : ReplicationBridge Bool Bool :=
    { response := id
      replicate := fun q => if q then 2 else 1 }
  let B₁ : ReplicationBridge Bool Bool :=
    { response := id
      replicate := fun q => if q then 4 else 3 }
  refine ⟨B₀, B₁, ?_, ?_⟩
  · rfl
  · norm_num [B₀, B₁, ReplicationBridge.fitness]

end UEOT.V3.Compression.Hierarchy
