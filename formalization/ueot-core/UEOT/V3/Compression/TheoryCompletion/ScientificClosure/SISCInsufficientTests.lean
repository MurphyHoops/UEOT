import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCObservableLumpability
import Mathlib.Tactic

/-!
# No-go: perfectly matched constant tests do NOT certify Markov lumpability

The observational-span premise is not decorative. Here two microscopic states
have the same output now and equal expected values for *every* registered
constant test, under a normalized deterministic (hence Markov) transition.
Yet their next transition probabilities into the displayed-output classes
are different, so their output partition is NOT strongly lumpable.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.FiniteStablePartition

/-- A finite controlled transition; output is the first Boolean coordinate,
but dynamics promote the hidden second coordinate into the next output. -/
def delayedOutputModel : Model (Bool × Bool) Unit Unit Bool where
  transition := fun _ x y => if y = (x.2, x.2) then 1 else 0
  reward := fun _ _ => Unit.unit
  output := Prod.fst
  transition_nonneg := by
    intro a x y
    split_ifs <;> norm_num
  transition_sum_one := by
    intro a x
    classical
    simp

/-- The tempting but insufficient partition based only on current output. -/
def currentOutputSetoid : Setoid (Bool × Bool) where
  r x y := x.1 = y.1
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

/-- A constant one-step test has expectation exactly 1 under any normalized
finite stochastic model. It contains no information about destination class. -/
theorem every_constant_test_has_same_expectation
    {X A R O : Type*} [Fintype X]
    (M : Model X A R O) (a : A) (x : X) :
    transitionTestExpectation M (fun _ => (1 : ℝ)) a x = 1 := by
  simpa [transitionTestExpectation] using M.transition_sum_one a x

/-- All registered constant-test expectations agree on all candidate fibers. -/
theorem constant_test_evidence_matches :
    SameTestExpectationsOnFibers delayedOutputModel currentOutputSetoid
      (fun (_ : Unit) (_ : Bool × Bool) => (1 : ℝ)) := by
  intro x y _ a i
  rw [every_constant_test_has_same_expectation,
      every_constant_test_has_same_expectation]

/-- Despite matched constant tests, the selected output class is NOT stable
under the true transition. One hidden bit is exposed after one action. -/
theorem current_output_partition_not_lumpable :
    ¬ Stable delayedOutputModel currentOutputSetoid := by
  intro hstable
  have hsame : currentOutputSetoid.r (false, false) (false, true) := rfl
  have heq := hstable hsame Unit.unit (true, true)
  classical
  have hleft : blockMass delayedOutputModel currentOutputSetoid
      Unit.unit (false, false) (true, true) = 0 := by
    unfold blockMass
    apply Finset.sum_eq_zero
    intro v hv
    by_cases hclass : currentOutputSetoid.r v (true, true)
    · have hne : v ≠ (false, false) := by
        intro he
        subst v
        exact Bool.false_ne_true hclass
      simp [hclass, delayedOutputModel, hne]
    · simp [hclass]
  have hright : blockMass delayedOutputModel currentOutputSetoid
      Unit.unit (false, true) (true, true) = 1 := by
    unfold blockMass
    calc
      (∑ v : Bool × Bool,
        if currentOutputSetoid.r v (true, true) then
          delayedOutputModel.transition Unit.unit (false, true) v else 0) =
        ∑ v : Bool × Bool, if v = (true, true) then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : v = (true, true)
          · subst v
            simp [delayedOutputModel]
          · simp [delayedOutputModel, hv]
      _ = 1 := by simp
  rw [hleft, hright] at heq
  norm_num at heq

/-- The precise no-go is *one coherent model* satisfying the observed test
condition but rejecting the stronger controlled-lumpability conclusion. -/
theorem equal_observed_tests_do_not_force_stability :
    ∃ (M : Model (Bool × Bool) Unit Unit Bool)
      (S : Setoid (Bool × Bool)),
      SameTestExpectationsOnFibers M S
        (fun (_ : Unit) (_ : Bool × Bool) => (1 : ℝ)) ∧
      ¬ Stable M S := by
  exact ⟨delayedOutputModel, currentOutputSetoid,
    constant_test_evidence_matches, current_output_partition_not_lumpable⟩

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
