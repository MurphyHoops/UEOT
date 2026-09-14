import UEOT.V3.FixedFitnessSelection

/-!
# P-BRG-01 — concentration on initially supported fitness maximizers

This layer formalizes the asymptotic part of frozen Core 3 P-BRG-01.  A
maximizer is chosen from the initial positive-mass support.  Every initially
supported strictly suboptimal type admits an explicit geometric envelope with
ratio `R i / R k < 1`; hence the finite total suboptimal mass tends to zero.
Equal-fitness maximizers retain their initial relative proportions by the exact
algebraic theorem from `FixedFitnessSelection`.
-/

namespace UEOT.V3.FixedFitnessConcentration

open Filter
open scoped BigOperators Topology

universe uI

variable {I : Type uI} [Fintype I] [Nonempty I]

open FixedFitnessSelection

/-- Initial positive-mass support. -/
noncomputable def initialSupport (p : I → ℝ) : Finset I :=
  Finset.univ.filter fun i => 0 < p i

/-- The initial support is nonempty for a normalized nonnegative frequency
vector. -/
theorem initialSupport_nonempty
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    (initialSupport p).Nonempty := by
  obtain ⟨i, hi⟩ := exists_pos_of_nonneg_sum_one p hp hpsum
  exact ⟨i, by simp [initialSupport, hi]⟩

/-- Finiteness gives an attained maximum fitness on the initial support. -/
theorem exists_support_maximizer
    (p R : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    ∃ k, 0 < p k ∧ ∀ i, 0 < p i → R i ≤ R k := by
  obtain ⟨k, hk, hmax⟩ :=
    Finset.exists_max_image (initialSupport p) R
      (initialSupport_nonempty p hp hpsum)
  refine ⟨k, ?_, ?_⟩
  · simpa [initialSupport] using hk
  · intro i hi
    apply hmax i
    simp [initialSupport, hi]

/-- Initially supported types strictly below the chosen support maximizer. -/
noncomputable def suboptimalSet (p R : I → ℝ) (k : I) : Finset I :=
  Finset.univ.filter fun i => 0 < p i ∧ R i < R k

/-- Total frequency currently carried by initially supported strictly
suboptimal types. -/
noncomputable def suboptimalMass (p R : I → ℝ) (k : I) (n : ℕ) : ℝ :=
  ∑ i ∈ suboptimalSet p R k, closedFrequency p R n i

/-- Exact factorization of any type against an initially present reference
type.  When the reference is a fitness maximizer, the middle factor is the
source geometric decay factor. -/
theorem closedFrequency_factor_against
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (k : I) (hk : 0 < p k) (i : I) (n : ℕ) :
    closedFrequency p R n i =
      (p i / p k) * (R i / R k) ^ n * closedFrequency p R n k := by
  have hD := weightedDenom_ne_zero p R hp hpsum hR n
  have hpk : p k ≠ 0 := ne_of_gt hk
  have hRk : R k ≠ 0 := ne_of_gt (hR k)
  unfold closedFrequency
  rw [div_pow]
  field_simp [hD, hpk, hRk]

/-- Every closed-form frequency is at most one. -/
theorem closedFrequency_le_one
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) (n : ℕ) (i : I) :
    closedFrequency p R n i ≤ 1 := by
  have hsingle :
      closedFrequency p R n i ≤ ∑ j, closedFrequency p R n j := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun j => closedFrequency p R n j)
      (fun j _ => closedFrequency_nonneg p R hp hpsum hR n j)
      (Finset.mem_univ i)
  rw [sum_closedFrequency_eq_one p R hp hpsum hR n] at hsingle
  exact hsingle

/-- A strictly suboptimal initially supported type has the explicit geometric
envelope promised by the frozen source. -/
theorem closedFrequency_le_geometric
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (k : I) (hk : 0 < p k)
    (i : I) (n : ℕ) :
    closedFrequency p R n i ≤
      (p i / p k) * (R i / R k) ^ n := by
  rw [closedFrequency_factor_against p R hp hpsum hR k hk i n]
  have hcoef : 0 ≤ (p i / p k) * (R i / R k) ^ n := by
    exact mul_nonneg
      (div_nonneg (hp i) (le_of_lt hk))
      (pow_nonneg (div_nonneg (le_of_lt (hR i)) (le_of_lt (hR k))) n)
  calc
    (p i / p k) * (R i / R k) ^ n * closedFrequency p R n k ≤
        (p i / p k) * (R i / R k) ^ n * 1 :=
      mul_le_mul_of_nonneg_left
        (closedFrequency_le_one p R hp hpsum hR n k) hcoef
    _ = (p i / p k) * (R i / R k) ^ n := by ring

/-- Each initially supported type strictly below a support maximizer converges
to zero, with the proof explicitly driven by the geometric ratio `R i/R k`. -/
theorem suboptimal_type_tendsto_zero
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (k : I) (hk : 0 < p k)
    (i : I) (hi : R i < R k) :
    Tendsto (fun n : ℕ => closedFrequency p R n i) atTop (𝓝 0) := by
  have hratio0 : 0 ≤ R i / R k :=
    div_nonneg (le_of_lt (hR i)) (le_of_lt (hR k))
  have hratio1 : R i / R k < 1 :=
    (div_lt_one (hR k)).2 hi
  have hpow :
      Tendsto (fun n : ℕ => (R i / R k) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1
  have hupper :
      Tendsto (fun n : ℕ => (p i / p k) * (R i / R k) ^ n)
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow)
  exact squeeze_zero
    (fun n => closedFrequency_nonneg p R hp hpsum hR n i)
    (fun n => closedFrequency_le_geometric p R hp hpsum hR k hk i n)
    hupper

/-- The total initially supported suboptimal mass is bounded by a finite sum of
explicit geometric terms.  This is the finite-source exponential envelope. -/
theorem suboptimalMass_le_geometricSum
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (k : I) (hk : 0 < p k) (n : ℕ) :
    suboptimalMass p R k n ≤
      ∑ i ∈ suboptimalSet p R k,
        (p i / p k) * (R i / R k) ^ n := by
  unfold suboptimalMass
  apply Finset.sum_le_sum
  intro i hi
  exact closedFrequency_le_geometric p R hp hpsum hR k hk i n

/-- The finite total mass of all initially supported types below the support
maximum tends to zero. -/
theorem suboptimalMass_tendsto_zero
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (k : I) (hk : 0 < p k)
    (hmax : ∀ i, 0 < p i → R i ≤ R k) :
    Tendsto (fun n : ℕ => suboptimalMass p R k n) atTop (𝓝 0) := by
  unfold suboptimalMass
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ i ∈ suboptimalSet p R k,
          closedFrequency p R n i)
        atTop
        (𝓝 (∑ i ∈ suboptimalSet p R k, (0 : ℝ))) := by
    refine tendsto_finsetSum (suboptimalSet p R k) ?_
    intro i hi
    have hisub : 0 < p i ∧ R i < R k := by
      simpa [suboptimalSet] using hi
    exact suboptimal_type_tendsto_zero p R hp hpsum hR k hk i hisub.2
  simpa using hsum

/-- Maximizers in the initial support preserve their initial relative
proportions at every finite time. -/
theorem maximizers_preserve_relativeProportion
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i)
    (k : I) (hk : 0 < p k)
    (i : I) (hi : 0 < p i) (hRi : R i = R k) (n : ℕ) :
    closedFrequency p R n i / closedFrequency p R n k = p i / p k := by
  exact equalFitness_preserves_relativeProportion
    p R hp hpsum hR n i k hRi (ne_of_gt hk)

/-- **P-BRG-01 concentration package.** A support maximizer exists; relative to
one such initially present maximizer, the exact replicator closed form obeys the
source recurrence, never creates initially absent types, every strictly
suboptimal supported type has an explicit geometric envelope and the finite
total suboptimal mass tends to zero, while support maximizers preserve their
initial relative proportions. -/
theorem p_brg_01
    (p R : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hR : ∀ i, 0 < R i) :
    ∃ k,
      0 < p k ∧
      (∀ i, 0 < p i → R i ≤ R k) ∧
      (∀ n i,
        closedFrequency p R (n + 1) i =
          closedFrequency p R n i * R i /
            (∑ j, closedFrequency p R n j * R j)) ∧
      (∀ n i, p i = 0 → closedFrequency p R n i = 0) ∧
      Tendsto (fun n : ℕ => suboptimalMass p R k n) atTop (𝓝 0) ∧
      (∀ i, 0 < p i → R i < R k → ∀ n,
        closedFrequency p R n i ≤
          (p i / p k) * (R i / R k) ^ n) ∧
      (∀ i, 0 < p i → R i = R k → ∀ n,
        closedFrequency p R n i / closedFrequency p R n k = p i / p k) := by
  obtain ⟨k, hk, hmax⟩ := exists_support_maximizer p R hp hpsum
  refine ⟨k, hk, hmax, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i
    exact closedFrequency_succ p R hp hpsum hR n i
  · intro n i hi
    exact closedFrequency_eq_zero_of_initial_eq_zero p R n i hi
  · exact suboptimalMass_tendsto_zero p R hp hpsum hR k hk hmax
  · intro i hi hlt n
    exact closedFrequency_le_geometric p R hp hpsum hR k hk i n
  · intro i hi heq n
    exact maximizers_preserve_relativeProportion p R hp hpsum hR k hk i hi heq n

end UEOT.V3.FixedFitnessConcentration