import UEOT.V3.FixedFitnessSelection

/-!
# P-BRG-01 — recurrence determines the fixed-fitness closed form

The frozen Core 3 source states the logical direction from the replicator
recurrence and its initial condition to the explicit closed form.  The base
`FixedFitnessSelection` module proves that the closed form satisfies the
recurrence; this companion module proves the converse uniqueness direction for
an arbitrary trajectory satisfying that same recurrence.
-/

namespace UEOT.V3.FixedFitnessRecurrenceUniqueness

open scoped BigOperators

universe uI

variable {I : Type uI} [Fintype I] [Nonempty I]

open UEOT.V3.FixedFitnessSelection

/-- Any trajectory with the declared initial condition and the frozen
fixed-fitness replicator recurrence is exactly the canonical closed-form
trajectory.  No extra normalization hypothesis on later `q n` is needed: the
induction identifies every previous slice with the already-normalized closed
form before the next recurrence step is compared. -/
theorem recurrence_unique_closedFrequency
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (q : ℕ → I → ℝ)
    (h0 : ∀ i, q 0 i = p i)
    (hrec : ∀ n i,
      q (n + 1) i =
        q n i * R i / (∑ j, q n j * R j)) :
    ∀ n i, q n i = closedFrequency p R n i := by
  intro n
  induction n with
  | zero =>
      intro i
      rw [h0 i]
      exact (closedFrequency_zero p R hpsum i).symm
  | succ n ih =>
      intro i
      have hsum :
          (∑ j, q n j * R j) =
            ∑ j, closedFrequency p R n j * R j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j]
      calc
        q (n + 1) i =
            q n i * R i / (∑ j, q n j * R j) := hrec n i
        _ = closedFrequency p R n i * R i /
            (∑ j, closedFrequency p R n j * R j) := by
              rw [ih i, hsum]
        _ = closedFrequency p R (n + 1) i :=
              (closedFrequency_succ p R hp hpsum hR n i).symm

/-- **P-BRG-01 closed-form implication.** This is the source direction written
literally: initial condition plus recurrence imply
`p_i(n) = p_i(0) R_i^n / ∑_j p_j(0) R_j^n`. -/
theorem p_brg_01_closedForm_of_recurrence
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (q : ℕ → I → ℝ)
    (h0 : ∀ i, q 0 i = p i)
    (hrec : ∀ n i,
      q (n + 1) i =
        q n i * R i / (∑ j, q n j * R j)) :
    ∀ n i,
      q n i = p i * R i ^ n / (∑ j, p j * R j ^ n) := by
  intro n i
  simpa [closedFrequency, weightedDenom] using
    (recurrence_unique_closedFrequency p R hp hpsum hR q h0 hrec n i)

end UEOT.V3.FixedFitnessRecurrenceUniqueness