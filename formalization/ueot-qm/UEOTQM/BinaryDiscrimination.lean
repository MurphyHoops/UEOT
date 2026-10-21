import UEOTQM.QuantumTraceDistance

/-!
# Optimal binary decisions and exact finite matrix certificates

An equal-prior decision uses one actual effect and its complement. Its
optimal success probability is derived from the existing all-effect distance
and the constructed positive spectral effect. Separate finite matrix
certificates require PSD parts and matrix support identities, never the
desired distance as an input. A supplied unitary diagonalization likewise
gives an exact finite formula without an asserted numerical eigensolver.
-/

namespace UEOTQM.BinaryDiscrimination

open Matrix QuantumTraceDistance
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Guess the first state on E and the second state on I-E, with equal priors. -/
def equalPriorSuccess (E : Effect ι) (ρ σ : Density ι) : ℝ :=
  (E.probability ρ + E.complement.probability σ) / 2

theorem equalPriorSuccess_eq (E : Effect ι) (ρ σ : Density ι) :
    equalPriorSuccess E ρ σ = (1 + (E.probability ρ - E.probability σ)) / 2 := by
  rw [equalPriorSuccess, Effect.probability_complement]
  ring

theorem equalPriorSuccess_le (E : Effect ι) (ρ σ : Density ι) :
    equalPriorSuccess E ρ σ ≤ (1 + effectDistance ρ σ) / 2 := by
  rw [equalPriorSuccess_eq]
  have hg := (le_abs_self (E.probability ρ - E.probability σ)).trans
    (E.probability_sub_le_effectDistance ρ σ)
  linarith

theorem positiveSpectrumEffect_success (ρ σ : Density ι) :
    equalPriorSuccess (positiveSpectrumEffect (ρ.matrix - σ.matrix)
      (ρ.positive.isHermitian.sub σ.positive.isHermitian)) ρ σ =
      (1 + effectDistance ρ σ) / 2 := by
  rw [equalPriorSuccess_eq, positiveSpectrumEffect_attains]

/-- Both the universal upper bound and its actual attaining measurement. -/
theorem exists_optimal_equalPriorDecision (ρ σ : Density ι) :
    ∃ E : Effect ι, equalPriorSuccess E ρ σ = (1 + effectDistance ρ σ) / 2 ∧
      ∀ F : Effect ι, equalPriorSuccess F ρ σ ≤ equalPriorSuccess E ρ σ := by
  refine ⟨positiveSpectrumEffect (ρ.matrix - σ.matrix)
    (ρ.positive.isHermitian.sub σ.positive.isHermitian),
    positiveSpectrumEffect_success ρ σ, ?_⟩
  intro F
  rw [positiveSpectrumEffect_success]
  exact equalPriorSuccess_le F ρ σ

theorem optimal_equalPriorSuccess_traceAbsolute (ρ σ : Density ι) :
    equalPriorSuccess (positiveSpectrumEffect (ρ.matrix - σ.matrix)
      (ρ.positive.isHermitian.sub σ.positive.isHermitian)) ρ σ =
      1 / 2 + traceAbsolute (ρ.matrix - σ.matrix) / 4 := by
  rw [positiveSpectrumEffect_success, effectDistance_eq_half_traceAbsolute]
  ring

/-- All inputs are actual matrix conditions. No distance conclusion is assumed. -/
theorem effectDistance_eq_mass_of_support_certificate (ρ σ : Density ι)
    (P N : Operator ι) (E : Effect ι) (hP : P.PosSemidef) (hN : N.PosSemidef)
    (hsplit : ρ.matrix - σ.matrix = P - N)
    (hEP : E.matrix * P = P) (hEN : E.matrix * N = 0) :
    effectDistance ρ σ = mass P := by
  apply le_antisymm (effectDistance_le_mass_of_psd_split ρ σ P N hP hN hsplit)
  have hg := E.probability_sub_le_effectDistance ρ σ
  have heq : E.probability ρ - E.probability σ = mass P := by
    change pairing E.matrix ρ.matrix - pairing E.matrix σ.matrix = mass P
    rw [← QuantumSeparation.pairing_sub_right, hsplit, QuantumSeparation.pairing_sub_right,
      pairing, pairing, hEP, hEN]
    simp [mass]
  rw [heq, abs_of_nonneg (mass_nonneg hP)] at hg
  exact hg

theorem success_eq_optimum_of_support_certificate (ρ σ : Density ι)
    (P N : Operator ι) (E : Effect ι) (hP : P.PosSemidef) (hN : N.PosSemidef)
    (hsplit : ρ.matrix - σ.matrix = P - N)
    (hEP : E.matrix * P = P) (hEN : E.matrix * N = 0) :
    equalPriorSuccess E ρ σ = (1 + effectDistance ρ σ) / 2 := by
  rw [equalPriorSuccess_eq,
    effectDistance_eq_mass_of_support_certificate ρ σ P N E hP hN hsplit hEP hEN]
  have heq : E.probability ρ - E.probability σ = mass P := by
    change pairing E.matrix ρ.matrix - pairing E.matrix σ.matrix = mass P
    rw [← QuantumSeparation.pairing_sub_right, hsplit, QuantumSeparation.pairing_sub_right,
      pairing, pairing, hEP, hEN]
    simp [mass]
  rw [heq]

/-- A certificate may supply any exact unitary diagonalization, in the displayed direction. -/
theorem effectDistance_eq_sum_positive_of_unitary_data (ρ σ : Density ι)
    (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ)
    (hspectral : ρ.matrix - σ.matrix = unitaryDiagonal U d) :
    effectDistance ρ σ = ∑ i, max (d i) 0 := by
  let P := unitaryDiagonal U (fun i => max (d i) 0)
  let N := unitaryDiagonal U (fun i => max (-d i) 0)
  let E : Effect ι := {
    matrix := unitaryDiagonal U (fun i => if 0 < d i then 1 else 0)
    positive := unitaryDiagonal_posSemidef _ _ (fun i => by split_ifs <;> norm_num)
    complement_positive := by
      rw [← unitaryDiagonal_one U, ← unitaryDiagonal_sub]
      exact unitaryDiagonal_posSemidef _ _ (fun i => by split_ifs <;> norm_num) }
  have hP : P.PosSemidef := unitaryDiagonal_posSemidef _ _ (fun _ => le_max_right _ _)
  have hN : N.PosSemidef := unitaryDiagonal_posSemidef _ _ (fun _ => le_max_right _ _)
  have hs : ρ.matrix - σ.matrix = P - N := by
    rw [hspectral]
    dsimp [P, N]
    rw [← unitaryDiagonal_sub]
    simp only [max_zero_sub_max_neg_zero_eq_self]
  have hEP : E.matrix * P = P := by
    change unitaryDiagonal U _ * unitaryDiagonal U _ = unitaryDiagonal U _
    rw [unitaryDiagonal_mul]
    congr 1
    funext i
    by_cases hi : 0 < d i
    · simp [hi]
    · simp [hi, max_eq_right (le_of_not_gt hi)]
  have hEN : E.matrix * N = 0 := by
    change unitaryDiagonal U _ * unitaryDiagonal U _ = 0
    rw [unitaryDiagonal_mul]
    convert unitaryDiagonal_zero U using 1
    congr 1
    funext i
    by_cases hi : 0 < d i
    · simp [hi, max_eq_right (neg_nonpos.mpr hi.le)]
    · simp [hi]
  rw [effectDistance_eq_mass_of_support_certificate ρ σ P N E hP hN hs hEP hEN]
  exact mass_unitaryDiagonal U _

theorem effectDistance_eq_half_sum_abs_of_unitary_data (ρ σ : Density ι)
    (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℝ)
    (hspectral : ρ.matrix - σ.matrix = unitaryDiagonal U d) :
    effectDistance ρ σ = (∑ i, |d i|) / 2 := by
  have hs : ρ.matrix - σ.matrix =
      unitaryDiagonal U (fun i => max (d i) 0) -
      unitaryDiagonal U (fun i => max (-d i) 0) := by
    rw [hspectral, ← unitaryDiagonal_sub]
    simp only [max_zero_sub_max_neg_zero_eq_self]
  have hm := difference_parts_mass_eq ρ σ _ _ hs
  rw [mass_unitaryDiagonal, mass_unitaryDiagonal] at hm
  have ha : (∑ i, |d i|) = (∑ i, max (d i) 0) + (∑ i, max (-d i) 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ d i
    · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), abs_of_nonneg hi]
    · have hi' := le_of_not_ge hi
      simp [max_eq_right hi', max_eq_left (neg_nonneg.mpr hi'), abs_of_nonpos hi']
  rw [effectDistance_eq_sum_positive_of_unitary_data ρ σ U d hspectral]
  linarith

end

end UEOTQM.BinaryDiscrimination
