import UEOTQM.RealLocalTomography

/-! Focused consumers of the finite real-sector counterexample. In particular,
the separating joint effect is outside every finite real linear combination
of real product effects, not just outside one chosen finite test family.
The complex-local deletion control remains separate from that real sector. -/

namespace UEOTQM.RealLocalTomography.Examples

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

/-- The hidden coherence has opposite signs in the actual density matrices. -/
theorem hidden_coherence_exact :
    rhoPlus.matrix (0, 0) (1, 1) = (-1 / 4 : ℂ) ∧
      rhoMinus.matrix (0, 0) (1, 1) = (1 / 4 : ℂ) := by
  norm_num [rhoPlus_matrix, rhoMinus_matrix, parity, pauliY, Matrix.one_apply]

/-- Every finite real linear combination of product effects is also blind.
The coefficients are unrestricted real numbers, so convex mixtures are covered. -/
theorem finite_real_product_span_blind {α : Type*} [Fintype α]
    (c : α → ℝ) (E F : α → Effect Qubit)
    (hE : ∀ a, IsReal (E a).matrix) (hF : ∀ a, IsReal (F a).matrix) :
    pairing (∑ a, c a • (productEffect (E a) (F a)).matrix) rhoPlus.matrix =
      pairing (∑ a, c a • (productEffect (E a) (F a)).matrix) rhoMinus.matrix := by
  simp only [pairing_sum_left, pairing_smul_left]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun p : ℝ => c a * p)
    (all_real_product_probabilities_equal (E a) (F a) (hE a) (hF a))

/-- A real joint effect cannot be represented in the real product span. -/
theorem joint_test_not_finite_real_product_sum {α : Type*} [Fintype α]
    (c : α → ℝ) (E F : α → Effect Qubit)
    (hE : ∀ a, IsReal (E a).matrix) (hF : ∀ a, IsReal (F a).matrix) :
    jointTest.matrix ≠ ∑ a, c a • (productEffect (E a) (F a)).matrix := by
  intro heq
  have h := finite_real_product_span_blind c E F hE hF
  rw [← heq] at h
  change jointTest.probability rhoPlus = jointTest.probability rhoMinus at h
  rw [jointTest_probability_plus, jointTest_probability_minus] at h
  norm_num at h

/-- The full complex effect domain cannot silently replace the real domain. -/
theorem reality_restriction_is_necessary :
    ¬ (∀ E F : Effect Qubit,
      (productEffect E F).probability rhoPlus =
        (productEffect E F).probability rhoMinus) := by
  intro h
  exact complex_product_distinguishes (h complexLocalTest complexLocalTest)

/-- The accepted and deletion-control response gaps have different sizes. -/
theorem response_gaps_exact :
    jointTest.probability rhoPlus - jointTest.probability rhoMinus = 1 ∧
      (productEffect complexLocalTest complexLocalTest).probability rhoPlus -
        (productEffect complexLocalTest complexLocalTest).probability rhoMinus = 1 / 2 := by
  rw [jointTest_probability_plus, jointTest_probability_minus,
    complex_product_probability_plus, complex_product_probability_minus]
  norm_num

end
end UEOTQM.RealLocalTomography.Examples

/-! Complete explicit witness declaration audit; generated helpers are excluded. -/
#print axioms UEOTQM.RealLocalTomography.Examples.hidden_coherence_exact
#print axioms UEOTQM.RealLocalTomography.Examples.finite_real_product_span_blind
#print axioms UEOTQM.RealLocalTomography.Examples.joint_test_not_finite_real_product_sum
#print axioms UEOTQM.RealLocalTomography.Examples.reality_restriction_is_necessary
#print axioms UEOTQM.RealLocalTomography.Examples.response_gaps_exact
