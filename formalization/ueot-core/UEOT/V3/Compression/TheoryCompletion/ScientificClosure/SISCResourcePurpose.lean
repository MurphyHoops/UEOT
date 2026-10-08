import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C6PurposeMechanism
import Mathlib.Tactic.Linarith

/-!
# SISC C6: one independently measurable resource/performance mechanism

This is a **conditional** objective bridge: objective weight and evaluation
horizon are supplied by a registered evaluator, not inferred from objecthood.
The measured resource/performance pair permits refutable comparisons; its
mechanism alone does not identify a unique physical purpose.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion

universe uA

/-- Independently calibrated action-performance, expenditure and budget.
No utility or 'purpose' is stored in the mechanism data itself. -/
structure ResourceSignal (A : Type uA) where
  performance : A → ℝ
  expenditure : A → ℝ
  budget : ℝ

def ResourceSignal.Feasible {A : Type uA} (R : ResourceSignal A) (a : A) : Prop :=
  R.expenditure a ≤ R.budget

/-- The evaluator introduces an explicit resource-expenditure price `lambda`.
This is an evaluation **contract**, not a first-principles physical force. -/
def ResourceSignal.objective {A : Type uA} (R : ResourceSignal A)
    (lambda : ℝ) : NumericalObjective A :=
  fun a => R.performance a - lambda * R.expenditure a

/-- A measured Pareto improvement is a weak policy improvement for any
independently registered nonnegative resource price. -/
theorem resource_Pareto_dominance
    {A : Type uA} (R : ResourceSignal A) (lambda : ℝ)
    (hprice : 0 ≤ lambda) (a b : A)
    (hperf : R.performance b ≤ R.performance a)
    (hcost : R.expenditure a ≤ R.expenditure b) :
    R.objective lambda b ≤ R.objective lambda a := by
  have hmul := mul_le_mul_of_nonneg_left hcost hprice
  dsimp [ResourceSignal.objective]
  linarith

/-- Strict performance superiority and no higher expenditure give a strict
measured-objective advantage. No inferred viability or long-run GOA here. -/
theorem strict_resource_dominance
    {A : Type uA} (R : ResourceSignal A) (lambda : ℝ)
    (hprice : 0 ≤ lambda) (a b : A)
    (hperf : R.performance b < R.performance a)
    (hcost : R.expenditure a ≤ R.expenditure b) :
    R.objective lambda b < R.objective lambda a := by
  have hmul := mul_le_mul_of_nonneg_left hcost hprice
  dsimp [ResourceSignal.objective]
  linarith

/-- **C6 mechanism-to-purpose no-go in a concrete calibrated domain.**
Identical performance/expenditure/budget measurements can yield different
policy orderings when the independently specified evaluation price changes.
Thus even a perfectly measured resource mechanism does not identify one
purpose without a separate evaluator/faithfulness bridge. -/
theorem resource_mechanism_alone_does_not_select_objective :
    ∃ R : ResourceSignal Bool,
      ¬ PolicyOrderingEquivalent (R.objective 0) (R.objective 2) := by
  let R : ResourceSignal Bool :=
    { performance := fun a => if a then 1 else 0
      expenditure := fun a => if a then 1 else 0
      budget := 2 }
  refine ⟨R, ?_⟩
  intro h
  have hcomp := h false true
  simp [R, ResourceSignal.objective, InducedPreference] at hcomp

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
