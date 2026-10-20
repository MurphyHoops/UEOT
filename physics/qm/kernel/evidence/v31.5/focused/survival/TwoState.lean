import UEOTQM.Survival

/-! Concrete two-state use of the actual quantum/Core bridge. The row sums
are unequal, so constant survival from arbitrary initial laws is a negative
control. All arithmetic and transported conclusions are kernel checked. -/

namespace UEOTQM.SurvivalTwoState

open Matrix
open scoped BigOperators ComplexOrder
open UEOTQM.Survival

noncomputable section

def Q : Matrix (Fin 2) (Fin 2) ℝ := !![1/4, 1/2; 1/8, 1/4]
def q : Fin 2 → ℝ := ![1/3, 2/3]
def h : Fin 2 → ℝ := ![3/2, 3/4]
def u : Fin 2 → ℝ := ![1/2, 1/2]

theorem Q_nonneg : ∀ i j, 0 ≤ Q i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Q]

theorem Q_rows : ∀ i, ∑ j, Q i j ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [Q, Fin.sum_univ_two]

theorem q_nonneg : ∀ i, 0 ≤ q i := by
  intro i
  fin_cases i <;> norm_num [q]

theorem q_sum : ∑ i, q i = 1 := by norm_num [q, Fin.sum_univ_two]

theorem h_pos : ∀ i, 0 < h i := by
  intro i
  fin_cases i <;> norm_num [h]

theorem qh_sum : ∑ i, q i * h i = 1 := by norm_num [q, h, Fin.sum_univ_two]

theorem left_eigen : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = (1/2) * q j := by
  intro j
  fin_cases j <;> norm_num [UEOT.V3.QSDPerron.rowApply, Q, q, Fin.sum_univ_two]

theorem right_eigen : ∀ i, UEOT.V3.QSDPerron.colApply Q h i = (1/2) * h i := by
  intro i
  fin_cases i <;> norm_num [UEOT.V3.QSDPerron.colApply, Q, h, Fin.sum_univ_two]

def I : Instrument (Fin 2) Bool (Fin 2 × Fin 2) := instrument Q Q_nonneg Q_rows
def rho : Density (Fin 2) := diagonalDensity q q_nonneg q_sum

theorem survival_exact (n : ℕ) : survivalMass I rho n = (1/2 : ℝ) ^ n :=
  qsd_survival_pow Q Q_nonneg Q_rows q q_nonneg q_sum (1/2) left_eigen n

theorem survival_positive (n : ℕ) : 0 < survivalMass I rho n :=
  qsd_survival_pos Q Q_nonneg Q_rows q q_nonneg q_sum (1/2) (by norm_num) left_eigen n

theorem quantum_qsd_fixed (n : ℕ) (hp : 0 < survivalMass I rho n) :
    conditionalState I rho n hp = rho :=
  qsd_conditionalState Q Q_nonneg Q_rows q q_nonneg q_sum
    (1/2) (by norm_num) left_eigen n hp

theorem doob_kernel_exact : UEOT.V3.QSDPerron.doobTransform Q h (1/2) =
    (!![1/2, 1/2; 1/2, 1/2] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [UEOT.V3.QSDPerron.doobTransform, Q, h]

theorem doob_law_exact : UEOT.V3.QSDPerron.doobInvariant q h = u := by
  funext i
  fin_cases i <;> norm_num [UEOT.V3.QSDPerron.doobInvariant, q, h, u]

theorem qsd_ne_doob_law : q ≠ UEOT.V3.QSDPerron.doobInvariant q h := by
  intro heq
  have hz := congrArg (fun f : Fin 2 → ℝ => f 0) heq
  norm_num [UEOT.V3.QSDPerron.doobInvariant, q, h] at hz

theorem quantum_doob_survival (n : ℕ) :
    survivalMass (doobInstrument Q Q_nonneg h (1/2) (by norm_num) h_pos right_eigen)
      (doobDensity q h q_nonneg h_pos qh_sum) n = 1 :=
  doob_survivalMass Q Q_nonneg q h q_nonneg (1/2) (by norm_num)
    h_pos qh_sum left_eigen right_eigen n

theorem u_nonneg : ∀ i, 0 ≤ u i := by
  intro i
  fin_cases i <;> norm_num [u]

theorem u_sum : ∑ i, u i = 1 := by norm_num [u, Fin.sum_univ_two]

/-- A normalized non-eigenlaw does not inherit the QSD's one-step rate. -/
theorem uniform_probability_exact :
    I.probability (diagonalDensity u u_nonneg u_sum) true = 9/16 := by
  rw [I, success_probability]
  norm_num [UEOT.V3.QSDPerron.rowApply, Q, u, Fin.sum_univ_two]

theorem uniform_probability_ne_perron :
    I.probability (diagonalDensity u u_nonneg u_sum) true ≠ (1/2 : ℝ) := by
  rw [uniform_probability_exact]
  norm_num

theorem transpose_nonneg : ∀ i j, 0 ≤ Qᵀ i j := by
  intro i j
  exact Q_nonneg j i

theorem transpose_rows : ∀ i, ∑ j, Qᵀ i j ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [Q, Fin.sum_univ_two]

/-- Reversing the matrix direction changes the actual quantum probability. -/
theorem transpose_probability_exact :
    (instrument Qᵀ transpose_nonneg transpose_rows).probability rho true = 5/8 := by
  rw [rho, success_probability]
  norm_num [UEOT.V3.QSDPerron.rowApply, Q, q, Fin.sum_univ_two]

theorem transpose_probability_ne_perron :
    (instrument Qᵀ transpose_nonneg transpose_rows).probability rho true ≠ (1/2 : ℝ) := by
  rw [transpose_probability_exact]
  norm_num

/-- The success Kraus family alone is CP and trace-decreasing, not complete. -/
theorem failure_completion_necessary :
    (∑ ij : Fin 2 × Fin 2, Q ij.1 ij.2 •
      ((matrixUnit ij.2 ij.1)ᴴ * matrixUnit ij.2 ij.1)) ≠ (1 : Operator (Fin 2)) := by
  rw [measurePrepare_gram]
  intro heq
  have hz := congrArg (fun X : Operator (Fin 2) => (X 0 0).re) heq
  norm_num [diagonalOperator, Q, Fin.sum_univ_two] at hz

#print axioms survival_exact
#print axioms quantum_qsd_fixed
#print axioms doob_kernel_exact
#print axioms doob_law_exact
#print axioms qsd_ne_doob_law
#print axioms quantum_doob_survival
#print axioms uniform_probability_exact
#print axioms uniform_probability_ne_perron
#print axioms transpose_probability_exact
#print axioms transpose_probability_ne_perron
#print axioms failure_completion_necessary

end
end UEOTQM.SurvivalTwoState
