import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# P-EVO-01 — exact selection/transmission decomposition

The frozen Core 3 source fixes finite parent/offspring type sets and defines
`M = D_b K`, where `b_i` is the mean offspring intensity and `K` is a
row-stochastic transmission kernel (rows with `b_i = 0` may be chosen
arbitrarily because they are annihilated by `D_b`).  For a parent frequency
row vector `p` with `bar b = p b > 0`, the deterministic mean-frequency update
is `p' = p M / bar b`.

This module keeps that source interface explicit and proves the exact Price-type
selection/transmission decomposition.  It does not identify this deterministic
ratio of mean intensities with an expected random population-frequency ratio.
-/

namespace UEOT.V3.EvolutionPrice

open scoped BigOperators

universe uI uJ
variable {I : Type uI} {J : Type uJ}
variable [Fintype I] [Fintype J]

/-- Finite weighted mean with weights `p`. -/
def weightedMean (p f : I → ℝ) : ℝ :=
  ∑ i, p i * f i

/-- Source mean-offspring operator entry `M_ij = b_i K_ij`, i.e. `M=D_b K`. -/
def meanOffspringEntry (b : I → ℝ) (K : I → J → ℝ) (i : I) (j : J) : ℝ :=
  b i * K i j

/-- Expected offspring trait produced by parent type `i`. -/
def transmittedTrait (K : I → J → ℝ) (z' : J → ℝ) (i : I) : ℝ :=
  ∑ j, K i j * z' j

/-- Finite weighted covariance used by the source Price identity. -/
def weightedCov (p b z : I → ℝ) : ℝ :=
  weightedMean p (fun i => b i * z i) - weightedMean p b * weightedMean p z

/-- Deterministic source update `p' = p M / bar b` with `M=D_b K`. -/
noncomputable def nextFrequency (p b : I → ℝ) (K : I → J → ℝ) (j : J) : ℝ :=
  (∑ i, p i * meanOffspringEntry b K i j) / weightedMean p b

/-- Mean offspring trait under a frequency row on the offspring type set. -/
def offspringTraitMean (q z' : J → ℝ) : ℝ :=
  ∑ j, q j * z' j

/-- Equivalent parent-indexed expression for the next-generation trait mean. -/
noncomputable def nextTraitMean (p b : I → ℝ) (K : I → J → ℝ) (z' : J → ℝ) : ℝ :=
  weightedMean p (fun i => b i * transmittedTrait K z' i) / weightedMean p b

/-- The explicit source update `p'=pD_bK/bar b` has the same trait mean as the
parent-indexed expression used in the Price algebra. -/
theorem nextFrequency_trait_mean_eq
    (p b : I → ℝ) (K : I → J → ℝ) (z' : J → ℝ)
    (_hbar : weightedMean p b ≠ 0) :
    offspringTraitMean (nextFrequency p b K) z' =
      nextTraitMean p b K z' := by
  unfold offspringTraitMean nextFrequency meanOffspringEntry nextTraitMean
  unfold weightedMean transmittedTrait
  have hnum :
      (∑ j : J, (∑ i : I, p i * (b i * K i j)) * z' j) =
        ∑ i : I, p i * (b i * ∑ j : J, K i j * z' j) := by
    calc
      (∑ j : J, (∑ i : I, p i * (b i * K i j)) * z' j) =
          ∑ j : J, ∑ i : I, (p i * (b i * K i j)) * z' j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_mul]
      _ = ∑ i : I, ∑ j : J, (p i * (b i * K i j)) * z' j := by
            rw [Finset.sum_comm]
      _ = ∑ i : I, p i * (b i * ∑ j : J, K i j * z' j) := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              (∑ j : J, (p i * (b i * K i j)) * z' j) =
                  ∑ j : J, (p i * b i) * (K i j * z' j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = (p i * b i) * ∑ j : J, K i j * z' j := by
                    rw [Finset.mul_sum]
              _ = p i * (b i * ∑ j : J, K i j * z' j) := by
                    ring
  calc
    (∑ j : J, ((∑ i : I, p i * (b i * K i j)) / (∑ i : I, p i * b i)) * z' j) =
        ∑ j : J, ((∑ i : I, p i * (b i * K i j)) * z' j) /
          (∑ i : I, p i * b i) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = (∑ j : J, (∑ i : I, p i * (b i * K i j)) * z' j) /
          (∑ i : I, p i * b i) := by
            rw [Finset.sum_div]
    _ = (∑ i : I, p i * (b i * ∑ j : J, K i j * z' j)) /
          (∑ i : I, p i * b i) := by
            rw [hnum]

/-- Algebraic core after replacing the source `p'z'` by its equivalent
parent-indexed expression.  Individual `b_i` may vanish; only `bar b > 0` is
required for division, exactly as in the frozen source. -/
theorem p_evo_01_core
    (p b z : I → ℝ) (K : I → J → ℝ) (z' : J → ℝ)
    (_hp0 : ∀ i, 0 ≤ p i)
    (_hpsum : ∑ i, p i = 1)
    (_hb0 : ∀ i, 0 ≤ b i)
    (_hK0 : ∀ i j, 0 ≤ K i j)
    (_hKsum : ∀ i, ∑ j, K i j = 1)
    (hbar : 0 < weightedMean p b) :
    nextTraitMean p b K z' - weightedMean p z =
      weightedCov p b z / weightedMean p b +
      weightedMean p
        (fun i => b i * (transmittedTrait K z' i - z i)) /
        weightedMean p b := by
  have hbar0 : weightedMean p b ≠ 0 := ne_of_gt hbar
  have htrans :
      weightedMean p
          (fun i => b i * (transmittedTrait K z' i - z i)) =
        weightedMean p (fun i => b i * transmittedTrait K z' i) -
          weightedMean p (fun i => b i * z i) := by
    unfold weightedMean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold nextTraitMean weightedCov
  rw [htrans]
  field_simp [hbar0]
  ring

/-- Source-facing P-EVO-01 with the frozen deterministic mean-frequency update
`p'=pM/bar b`, `M=D_bK`, written explicitly through `nextFrequency`. -/
theorem p_evo_01
    (p b z : I → ℝ) (K : I → J → ℝ) (z' : J → ℝ)
    (hp0 : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1)
    (hb0 : ∀ i, 0 ≤ b i)
    (hK0 : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1)
    (hbar : 0 < weightedMean p b) :
    offspringTraitMean (nextFrequency p b K) z' - weightedMean p z =
      weightedCov p b z / weightedMean p b +
      weightedMean p
        (fun i => b i * (transmittedTrait K z' i - z i)) /
        weightedMean p b := by
  rw [nextFrequency_trait_mean_eq p b K z' (ne_of_gt hbar)]
  exact p_evo_01_core p b z K z' hp0 hpsum hb0 hK0 hKsum hbar

end UEOT.V3.EvolutionPrice
