import Mathlib

/-!
# P-BRG-01 — fixed-fitness selection without mutation

This module formalizes the finite fixed-positive-fitness replicator bridge from
Core 3 §26.3.  The source dynamics are

`pᵢ(n+1) = pᵢ(n) Rᵢ / ∑ⱼ pⱼ(n) Rⱼ`.

The first layer below proves the exact closed form, normalization, support
preservation, and preservation of relative proportions for equal-fitness types.
The asymptotic concentration layer is built on top of these exact identities.
No mutation kernel is present in this theorem.
-/

namespace UEOT.V3.FixedFitnessSelection

open scoped BigOperators Topology

universe uI

variable {I : Type uI} [Fintype I] [Nonempty I]

/-- Denominator of the closed-form fixed-fitness replicator trajectory. -/
def weightedDenom (p R : I → ℝ) (n : ℕ) : ℝ :=
  ∑ i, p i * R i ^ n

/-- Closed-form frequency after `n` fixed-fitness selection steps. -/
noncomputable def closedFrequency (p R : I → ℝ) (n : ℕ) (i : I) : ℝ :=
  p i * R i ^ n / weightedDenom p R n

/-- A nonnegative finite frequency vector with total mass one has a point of
strictly positive mass. -/
theorem exists_pos_of_nonneg_sum_one
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    ∃ i, 0 < p i := by
  by_contra h
  push_neg at h
  have hz : ∀ i, p i = 0 := by
    intro i
    exact le_antisymm (h i) (hp i)
  have hsum0 : (∑ i, p i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hz i
  linarith

/-- Under the source assumptions, every closed-form denominator is strictly
positive, so no extra nonzero-denominator hypothesis is needed. -/
theorem weightedDenom_pos
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) (n : ℕ) :
    0 < weightedDenom p R n := by
  obtain ⟨i, hi⟩ := exists_pos_of_nonneg_sum_one p hp hpsum
  have hterm : 0 < p i * R i ^ n :=
    mul_pos hi (pow_pos (hR i) n)
  have hle : p i * R i ^ n ≤ ∑ j, p j * R j ^ n := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun j => p j * R j ^ n)
      (fun j _ => mul_nonneg (hp j) (pow_nonneg (le_of_lt (hR j)) n))
      (Finset.mem_univ i)
  exact hterm.trans_le hle

/-- Convenient nonzero form of `weightedDenom_pos`. -/
theorem weightedDenom_ne_zero
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) (n : ℕ) :
    weightedDenom p R n ≠ 0 :=
  ne_of_gt (weightedDenom_pos p R hp hpsum hR n)

/-- The denominator at the next time is the current weighted numerator after
one further multiplication by fitness. -/
theorem weightedDenom_succ (p R : I → ℝ) (n : ℕ) :
    weightedDenom p R (n + 1) =
      ∑ i, (p i * R i ^ n) * R i := by
  unfold weightedDenom
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

/-- The closed form starts at the declared initial frequency vector. -/
theorem closedFrequency_zero
    (p R : I → ℝ) (hpsum : ∑ i, p i = 1) (i : I) :
    closedFrequency p R 0 i = p i := by
  simp [closedFrequency, weightedDenom, hpsum]

/-- Every closed-form time slice is normalized. -/
theorem sum_closedFrequency_eq_one
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) (n : ℕ) :
    ∑ i, closedFrequency p R n i = 1 := by
  have hD := weightedDenom_ne_zero p R hp hpsum hR n
  unfold closedFrequency
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  change weightedDenom p R n * (weightedDenom p R n)⁻¹ = 1
  simp [hD]

/-- Closed-form frequencies remain nonnegative. -/
theorem closedFrequency_nonneg
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) (n : ℕ) (i : I) :
    0 ≤ closedFrequency p R n i := by
  unfold closedFrequency
  exact div_nonneg
    (mul_nonneg (hp i) (pow_nonneg (le_of_lt (hR i)) n))
    (le_of_lt (weightedDenom_pos p R hp hpsum hR n))

/-- Mean fitness under the closed-form time-`n` frequencies equals the ratio of
successive closed-form denominators. -/
theorem meanFitness_closedFrequency
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) (n : ℕ) :
    (∑ i, closedFrequency p R n i * R i) =
      weightedDenom p R (n + 1) / weightedDenom p R n := by
  have hD := weightedDenom_ne_zero p R hp hpsum hR n
  calc
    (∑ i, closedFrequency p R n i * R i) =
        ∑ i, (p i * R i ^ (n + 1)) / weightedDenom p R n := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold closedFrequency
          rw [pow_succ]
          ring
    _ = (∑ i, p i * R i ^ (n + 1)) * (weightedDenom p R n)⁻¹ := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    _ = weightedDenom p R (n + 1) / weightedDenom p R n := by
          simp [weightedDenom, div_eq_mul_inv]

/-- The closed form obeys exactly the source replicator recurrence. -/
theorem closedFrequency_succ
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) (n : ℕ) (i : I) :
    closedFrequency p R (n + 1) i =
      closedFrequency p R n i * R i /
        (∑ j, closedFrequency p R n j * R j) := by
  rw [meanFitness_closedFrequency p R hp hpsum hR n]
  have hDn := weightedDenom_ne_zero p R hp hpsum hR n
  have hDsn := weightedDenom_ne_zero p R hp hpsum hR (n + 1)
  unfold closedFrequency
  rw [pow_succ]
  field_simp [hDn, hDsn]
  <;> ring

/-- No-mutation support preservation: a type absent initially stays absent at
every time. -/
theorem closedFrequency_eq_zero_of_initial_eq_zero
    (p R : I → ℝ) (n : ℕ) (i : I) (hi : p i = 0) :
    closedFrequency p R n i = 0 := by
  simp [closedFrequency, hi]

/-- Equal-fitness types preserve their initial cross-proportion exactly.  This
cross-multiplied form remains meaningful even when one initial mass vanishes. -/
theorem equalFitness_preserves_crossProportion
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (n : ℕ) (i k : I) (hik : R i = R k) :
    closedFrequency p R n i * p k =
      closedFrequency p R n k * p i := by
  have hD := weightedDenom_ne_zero p R hp hpsum hR n
  unfold closedFrequency
  rw [hik]
  field_simp [hD]

/-- Ratio form of preservation for two initially present equal-fitness types. -/
theorem equalFitness_preserves_relativeProportion
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (n : ℕ) (i k : I) (hik : R i = R k) (hk : p k ≠ 0) :
    closedFrequency p R n i / closedFrequency p R n k = p i / p k := by
  have hD := weightedDenom_ne_zero p R hp hpsum hR n
  have hRkn : R k ^ n ≠ 0 := pow_ne_zero n (ne_of_gt (hR k))
  unfold closedFrequency
  rw [hik]
  field_simp [hD, hk, hRkn]

/-- Source-facing algebraic core of P-BRG-01: the declared initial condition,
exact replicator recurrence, closed form, normalization, support preservation,
and equal-fitness relative-proportion law all hold under only the frozen finite
simplex and positive-fitness assumptions. -/
theorem p_brg_01_algebraic
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) :
    (∀ i, closedFrequency p R 0 i = p i) ∧
    (∀ n i,
      closedFrequency p R (n + 1) i =
        closedFrequency p R n i * R i /
          (∑ j, closedFrequency p R n j * R j)) ∧
    (∀ n, ∑ i, closedFrequency p R n i = 1) ∧
    (∀ n i, p i = 0 → closedFrequency p R n i = 0) ∧
    (∀ n i k, R i = R k →
      closedFrequency p R n i * p k =
        closedFrequency p R n k * p i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact closedFrequency_zero p R hpsum i
  · intro n i
    exact closedFrequency_succ p R hp hpsum hR n i
  · intro n
    exact sum_closedFrequency_eq_one p R hp hpsum hR n
  · intro n i hi
    exact closedFrequency_eq_zero_of_initial_eq_zero p R n i hi
  · intro n i k hik
    exact equalFitness_preserves_crossProportion p R hp hpsum hR n i k hik

end UEOT.V3.FixedFitnessSelection