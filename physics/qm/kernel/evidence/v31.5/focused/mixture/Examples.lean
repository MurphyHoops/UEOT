import UEOTQM.Mixture

namespace UEOTQM.Mixture.Examples

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

def leftWeights : RationalWeights (Fin 2) where
  weight := ![3 / 4, 1 / 4]
  nonneg b := by fin_cases b <;> norm_num
  sum_one := by norm_num [Fin.sum_univ_two]

def rightWeights : RationalWeights (Fin 2) where
  weight := ![1 / 4, 3 / 4]
  nonneg b := by fin_cases b <;> norm_num
  sum_one := by norm_num [Fin.sum_univ_two]

theorem exact_rational_budget : rationalTV leftWeights rightWeights = 1 / 2 := by
  norm_num [rationalTV, leftWeights, rightWeights, Fin.sum_univ_two]

theorem universal_library_budget {ι O κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype O] [Fintype κ] (I : Fin 2 → Instrument ι O κ) :
    channelDefect (instrument leftWeights.toWeights I).channelState
      (instrument rightWeights.toWeights I).channelState ≤ 1 / 2 := by
  have h := channelDefect_weight_change_le_rational_budget
    leftWeights rightWeights I (1 / 2) (le_of_eq exact_rational_budget)
  norm_num at h ⊢
  exact h

def basisDensity (b : Fin 2) : Density (Fin 2) where
  matrix := Matrix.diagonal (fun i => if i = b then 1 else 0)
  positive := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> simp
  trace_one := by
    fin_cases b <;> norm_num [Matrix.trace, Fin.sum_univ_two]

def firstEffect : Effect (Fin 2) where
  matrix := (basisDensity 0).matrix
  positive := (basisDensity 0).positive
  complement_positive := by
    convert (basisDensity 1).positive using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [basisDensity, Matrix.one_apply, Matrix.diagonal_apply]

theorem firstEffect_basis (b : Fin 2) :
    firstEffect.probability (basisDensity b) = if b = 0 then 1 else 0 := by
  fin_cases b <;> norm_num [firstEffect, basisDensity, Effect.probability,
    pairing, mass, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Orthogonal density states attain the one-half TV bound exactly. -/
theorem density_bound_is_sharp :
    effectDistance (density leftWeights.toWeights basisDensity)
      (density rightWeights.toWeights basisDensity) = 1 / 2 := by
  apply le_antisymm
  · have h := density_weight_change_le_rational_budget leftWeights rightWeights
      basisDensity (1 / 2) (le_of_eq exact_rational_budget)
    norm_num at h ⊢
    exact h
  · have h := firstEffect.probability_sub_le_effectDistance
      (density leftWeights.toWeights basisDensity) (density rightWeights.toWeights basisDensity)
    norm_num [probability_density, firstEffect_basis, leftWeights, rightWeights,
      RationalWeights.toWeights, Fin.sum_univ_two] at h
    exact h

/-- Keeping the weights equal does not control a change of state library. -/
theorem same_library_premise_is_necessary :
    ¬ effectDistance (density leftWeights.toWeights (fun _ => basisDensity 0))
      (density leftWeights.toWeights (fun _ => basisDensity 1)) ≤
        tv leftWeights.toWeights leftWeights.toWeights := by
  intro h
  have hgap := firstEffect.probability_sub_le_effectDistance
    (density leftWeights.toWeights (fun _ => basisDensity 0))
    (density leftWeights.toWeights (fun _ => basisDensity 1))
  norm_num [probability_density, firstEffect_basis, leftWeights,
    RationalWeights.toWeights, Fin.sum_univ_two] at hgap
  change 1 ≤ effectDistance (density leftWeights.toWeights (fun _ => basisDensity 0))
    (density leftWeights.toWeights (fun _ => basisDensity 1)) at hgap
  rw [tv_self] at h
  linarith

end

end UEOTQM.Mixture.Examples
