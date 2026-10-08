import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCObservableLumpability
import Mathlib.Tactic

/-!
# SISC N1.4 — quantitative approximate observational lumpability

Exact class-indicator spanning and exactly equal response expectations can be
too strong for empirical work. Here both assumptions have explicit, separately
auditable error budgets. The conclusion bounds *real* class-transition
probability disagreements. It does NOT manufacture an exact Markov quotient.

If every class-indicator reconstruction has uniform error δ and every
registered test expectation differs by at most ε across a candidate fibre,
the class-mass defect is at most 2δ + ε·sum_i |coefficient_i|.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.FiniteStablePartition

universe uX uA uR uO uI

/-- Uniform approximate reconstruction of every target block indicator. -/
def ApproxSpansPartitionIndicators
    {X : Type uX} {I : Type uI} [Fintype I]
    (S : Setoid X) (test : I → X → ℝ)
    (coeff : X → I → ℝ) (delta : ℝ) : Prop := by
  classical
  exact ∀ z y,
    |(if S.r y z then (1 : ℝ) else 0) -
      ∑ i, coeff z i * test i y| ≤ delta

/-- Uniform experimental discrepancy between one-step test predictions. -/
def ApproxSameTestExpectationsOnFibers
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    {I : Type uI} [Fintype X] [Fintype I]
    (M : Model X A R O) (S : Setoid X)
    (test : I → X → ℝ) (eps : ℝ) : Prop :=
  ∀ ⦃x y⦄, S.r x y → ∀ a i,
    |transitionTestExpectation M (test i) a x -
      transitionTestExpectation M (test i) a y| ≤ eps

/-- With normalized nonnegative transitions, the average reconstruction
error for a destination class cannot exceed the pointwise δ envelope. -/
theorem approx_block_mass_from_tests
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    {I : Type uI} [Fintype X] [Fintype I]
    (M : Model X A R O) (S : Setoid X)
    (test : I → X → ℝ) (coeff : X → I → ℝ)
    (delta : ℝ) (happrox : ApproxSpansPartitionIndicators S test coeff delta)
    (a : A) (x z : X) :
    |blockMass M S a x z -
      ∑ i, coeff z i * transitionTestExpectation M (test i) a x| ≤ delta := by
  classical
  have hblock : blockMass M S a x z =
      ∑ y : X, M.transition a x y * (if S.r y z then (1 : ℝ) else 0) := by
    unfold blockMass
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  have htest : (∑ i, coeff z i * transitionTestExpectation M (test i) a x) =
      ∑ y : X, M.transition a x y * (∑ i, coeff z i * test i y) := by
    calc
      (∑ i, coeff z i * transitionTestExpectation M (test i) a x) =
          ∑ i, ∑ y : X, M.transition a x y * (coeff z i * test i y) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [transitionTestExpectation, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = ∑ y : X, ∑ i, M.transition a x y * (coeff z i * test i y) :=
        Finset.sum_comm
      _ = ∑ y : X, M.transition a x y * (∑ i, coeff z i * test i y) := by
        simp_rw [Finset.mul_sum]
  rw [hblock, htest]
  have hrewrite :
      (∑ y : X, M.transition a x y * (if S.r y z then (1 : ℝ) else 0)) -
        (∑ y : X, M.transition a x y * (∑ i, coeff z i * test i y)) =
      ∑ y : X, M.transition a x y *
        ((if S.r y z then (1 : ℝ) else 0) - ∑ i, coeff z i * test i y) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hrewrite]
  calc
    |∑ y : X, M.transition a x y *
      ((if S.r y z then (1 : ℝ) else 0) - ∑ i, coeff z i * test i y)| ≤
      ∑ y : X, |M.transition a x y *
        ((if S.r y z then (1 : ℝ) else 0) - ∑ i, coeff z i * test i y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : X, M.transition a x y * delta := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul, abs_of_nonneg (M.transition_nonneg a x y)]
      exact mul_le_mul_of_nonneg_left (happrox z y) (M.transition_nonneg a x y)
    _ = delta := by
      rw [← Finset.sum_mul, M.transition_sum_one a x]
      ring

/-- Finite test expectation mismatch, with coefficient amplification. -/
theorem approx_test_linear_combination
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    {I : Type uI} [Fintype X] [Fintype I]
    (M : Model X A R O) (test : I → X → ℝ)
    (coeff : I → ℝ) (eps : ℝ) (a : A) (x y : X)
    (hobs : ∀ i,
      |transitionTestExpectation M (test i) a x -
        transitionTestExpectation M (test i) a y| ≤ eps) :
    |(∑ i, coeff i * transitionTestExpectation M (test i) a x) -
      (∑ i, coeff i * transitionTestExpectation M (test i) a y)| ≤
      eps * ∑ i, |coeff i| := by
  have hdiff :
      (∑ i, coeff i * transitionTestExpectation M (test i) a x) -
        (∑ i, coeff i * transitionTestExpectation M (test i) a y) =
      ∑ i, coeff i * (transitionTestExpectation M (test i) a x -
        transitionTestExpectation M (test i) a y) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiff]
  calc
    |∑ i, coeff i * (transitionTestExpectation M (test i) a x -
      transitionTestExpectation M (test i) a y)| ≤
      ∑ i, |coeff i * (transitionTestExpectation M (test i) a x -
        transitionTestExpectation M (test i) a y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |coeff i| * eps := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hobs i) (abs_nonneg _)
    _ = eps * ∑ i, |coeff i| := by
      rw [← Finset.sum_mul]
      -- after sum_mul each term has `|coeff i| * eps`
      rw [mul_comm]

/-- **Robust central implication.** Approximately spanning experiments plus
bounded response mismatch force approximately equal true class transition
masses. `Stable` is not concluded unless both errors vanish. -/
theorem robust_class_mass_from_approx_observable_tests
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
    {I : Type uI} [Fintype X] [Fintype A] [Fintype I]
    (M : Model X A R O) (S : Setoid X)
    (test : I → X → ℝ) (coeff : X → I → ℝ)
    (delta eps : ℝ)
    (hspan : ApproxSpansPartitionIndicators S test coeff delta)
    (hobs : ApproxSameTestExpectationsOnFibers M S test eps)
    {x y : X} (hxy : S.r x y) (a : A) (z : X) :
    |blockMass M S a x z - blockMass M S a y z| ≤
      2 * delta + eps * ∑ i, |coeff z i| := by
  let Vx := ∑ i, coeff z i * transitionTestExpectation M (test i) a x
  let Vy := ∑ i, coeff z i * transitionTestExpectation M (test i) a y
  have hx : |blockMass M S a x z - Vx| ≤ delta :=
    approx_block_mass_from_tests M S test coeff delta hspan a x z
  have hy : |Vy - blockMass M S a y z| ≤ delta := by
    simpa only [abs_sub_comm] using
      approx_block_mass_from_tests M S test coeff delta hspan a y z
  have hmiddle : |Vx - Vy| ≤ eps * ∑ i, |coeff z i| :=
    approx_test_linear_combination M test (coeff z) eps a x y
      (hobs hxy a)
  have hleft := abs_sub_le (blockMass M S a x z) Vx (blockMass M S a y z)
  have hright := abs_sub_le Vx Vy (blockMass M S a y z)
  linarith

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
