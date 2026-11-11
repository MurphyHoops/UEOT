import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeRepair
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFormation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeOneStep
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedbackBoundary
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeLineage
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment

/-!
# Public common-source consumer for the definitive Core closure

The substantive constructions are in the imported source consumers. This entry
identifies the very same damaged founder, physical code, paid repair and actual
population execution; it does not supply a success, mean, fitness or optimality
certificate to a source. All parameters in the open `Valid` class are admitted.
The old conditional Core results and their interfaces remain unchanged.
The separately named growth-classification endpoints admit primitive probability
validity and classify both inherited programs; they do not widen feedback contracts.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure

noncomputable section
open CoreRegenerativeSource CoreRegenerativePopulation CoreRegenerativeControlPopulation
open FiniteSourceGrowthControl.SourceConsumer CoreRegenerativeQuotient
open scoped BigOperators

abbrev commonFounder (index : ℕ) (tag : Bool) : State := trueFounderState index true tag

theorem common_founder_is_actual (index : ℕ) (tag : Bool) :
    (commonFounder index tag).population = [founder index true true tag] ∧
    (founder index true true tag).body = (startState true true tag).body ∧
    (startState true true tag).balance.val = 1 + 5 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Recovery and attained expected population growth share one actual damaged
program, initial member and the six-unit source transaction. Growth bounds hold
for every finite census; they are not an almost-sure survival assertion. -/
theorem same_program_regenerates_and_attains (p : Parameters) (hp : Valid p)
    (index : ℕ) (tag : Bool) :
    (paidRepair (startState true true tag)).body = encode true false tag ∧
    rawExecute (paidRepair (startState true true tag)).body true = some .care ∧
    (paidRepair (startState true true tag)).balance.val = 3 ∧
    (∀ z : Noise, (programStep (founder index true true tag).body z) =
      step (startState true true tag).body .care z) ∧
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ n,
      lo * growthRate p true ^ n ≤ populationExpectation p bestPolicy
        (commonFounder index tag) n (fun s => (s.population.length : ℝ)) ∧
      populationExpectation p bestPolicy (commonFounder index tag) n
        (fun s => (s.population.length : ℝ)) ≤ hi * growthRate p true ^ n := by
  obtain ⟨hr, ha, hb⟩ := same_program_restores_then_reads true tag
  refine ⟨hr, ha, hb, ?_, damaged_true_founder_growth p hp index tag⟩
  intro z
  change programStep (programBody true true tag) z = step (programBody true true tag) .care z
  rw [programStep_eq_step]
  rfl

theorem positive_source_class_nonempty : ∃ p : Parameters, Valid p :=
  ⟨concreteParameters, concreteParameters_valid⟩

/-- Erasing the silent tag lifts the positive source value without merging
actual identities. The expanded tag matrix has two faithful blocks and is not
claimed to be primitive or to have a unique Perron ray. -/
def liftedSourceValue (p : Parameters) (i : RawKind) : ℝ := sourceValue p i.1

theorem lifted_source_value_pos (p : Parameters) (hp : Valid p) (i : RawKind) :
    0 < liftedSourceValue p i := sourceValue_pos p hp i.1

theorem expanded_source_eigen (p : Parameters) (i : RawKind) :
    (∑ j : RawKind, expanded (programRow p true) i j * liftedSourceValue p j) =
      growthRate p true * liftedSourceValue p i := by
  rcases i with ⟨i, tag⟩
  have h := sourceValue_eigen p i
  simp only [FiniteSourceGrowthControl.selectedMatrix, sourceRows,
    eventMean_eq_row, bestSelector_program] at h
  cases i <;> cases tag <;>
    simpa [expanded, liftedSourceValue, programRow,
      Fintype.sum_prod_type] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreTheoryClosure
