import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySeparation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportMemoryCheck

/-!
# Executable finite-memory decisions tied to the Boolean source

The finite relation is an explicitly decidable Boolean flip table. Kernel
reduction checks both singleton initial supports and rejects the mixed
support. The positive computation is consumed by the actual-source theorem
for the newly constructed support controller. The rejected full support,
matched to the uniform original initial law, excludes every all-times causal
policy for that separate initial experiment.

These are computations on a finite relation with a proved PMF-support
identity. They do not supply an executable oracle for arbitrary PMFs or an
algorithm for the separate carrier-discovery problem.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace FiniteMemoryCheckWitness

open MeasureTheory UEOT.V3.PathError SupportViabilityClosure
open FiniteMemorySeparation

/-- An executable exact support table for the same deterministic source. -/
def flipRelation (x _a z : Bool) : Prop := z = !x

/-- The same state-action certification, now as fixed finite input data. -/
def matchingAction (x a : Bool) : Prop := a = x

instance (x a z : Bool) : Decidable (flipRelation x a z) :=
  inferInstanceAs (Decidable (z = !x))

instance (x a : Bool) : Decidable (matchingAction x a) :=
  inferInstanceAs (Decidable (a = x))

/-- With the initial hidden state known to be false, the bounded executable
criterion accepts. The fixed horizon is `2 ^ card Bool - 1 = 3`. -/
private theorem singleton_false_check :
    finiteMemoryCheck observe flipRelation matchingAction
      ({false} : Finset Bool) = true := by
  decide

/-- The other known initial phase is also accepted by the same checker. -/
private theorem singleton_true_check :
    finiteMemoryCheck observe flipRelation matchingAction
      ({true} : Finset Bool) = true := by
  decide

/-- An initially ambiguous phase has no action certifying both possibilities. -/
private theorem mixed_initial_check :
    finiteMemoryCheck observe flipRelation matchingAction
      ({false, true} : Finset Bool) = false := by
  decide

/-- The executable decision table accepts either known phase and rejects
their ambiguous union. The elementary kernel computations stay private. -/
theorem finite_decision_table :
    finiteMemoryCheck observe flipRelation matchingAction
        ({false} : Finset Bool) = true ∧
      finiteMemoryCheck observe flipRelation matchingAction
        ({true} : Finset Bool) = true ∧
      finiteMemoryCheck observe flipRelation matchingAction
        ({false, true} : Finset Bool) = false :=
  ⟨singleton_false_check, singleton_true_check, mixed_initial_check⟩

noncomputable section

local instance : MeasurableSpace Bool := ⊤

/-- The Boolean relation matches the actual PMF support at every time;
the checker is not applied to a separately asserted graph. -/
theorem source_support_exact (n : ℕ) (x a z : Bool) :
    z ∈ (source n x a).support ↔ flipRelation x a z := by
  simp [source, flipRelation, PMF.support_pure]

private theorem initial_support_exact (x : Bool) :
    x ∈ ({false} : Finset Bool) ↔ x ∈ initial.support := by
  simp [initial, PMF.support_pure]

/-- The actual support controller obtained from the positive executable
check certifies every row of the original `pure false` source experiment.
No identity with the independently written Boolean controller is assumed. -/
theorem checked_support_controller_zero_uncovered :
    ∀ n, (coverageDeploymentRowLaw initial observe source
      (supportMemoryController initial observe flipRelation matchingAction
        (PMF.pure false)).policy n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  apply (finiteMemoryCheck_iff_controller_zero_uncovered
    observe flipRelation matchingAction ({false} : Finset Bool)
    initial source certified (PMF.pure false)
    initial_support_exact source_support_exact (fun _ _ _ => Iff.rfl)).mp
  exact singleton_false_check

/-- If the same hidden flip process instead starts with both phases having
positive probability, no complete causal policy can certify every time.
The change of initial law is explicit; the source and certification are the
same ones used by the positive experiment. -/
theorem mixed_initial_has_no_all_times_policy :
    ¬ ∃ π : ∀ n, CausalHistory Unit (Bool × Unit) n → PMF Bool,
      ∀ n, (coverageDeploymentRowLaw (PMF.uniformOfFintype Bool)
        observe source π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  rintro ⟨π, hzero⟩
  have h0 : ∀ x : Bool, x ∈ ({false, true} : Finset Bool) ↔
      x ∈ (PMF.uniformOfFintype Bool).support := by
    intro x
    cases x <;> simp
  have hcheck := (finiteMemoryCheck_iff_exists_all_times_policy
    observe flipRelation matchingAction ({false, true} : Finset Bool)
    (PMF.uniformOfFintype Bool) source certified (PMF.pure false)
    h0 source_support_exact (fun _ _ _ => Iff.rfl)).mpr ⟨π, hzero⟩
  rw [mixed_initial_check] at hcheck
  cases hcheck

end
end FiniteMemoryCheckWitness
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
