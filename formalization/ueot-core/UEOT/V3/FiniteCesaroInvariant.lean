import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-!
# P-GOA-01 — finite-chain Cesàro subsequential invariance

Frozen UEOT Core v3 §21.2 fixes a finite stochastic kernel `P` and an initial
probability row `μ₀`.  For positive `N`, its Cesàro average is

`μ̄_N = N⁻¹ ∑_{t=0}^{N-1} μ₀ P^t`.

The source-facing claim is deliberately limited to two facts:

* the Cesàro sequence has a convergent subsequence;
* every convergent subsequential limit is invariant under `P`.

No irreducibility, aperiodicity, mixing, uniqueness, full Cesàro convergence,
or attractivity assumption/conclusion is used here.
-/

namespace UEOT.V3.FiniteCesaroInvariant

noncomputable section

open scoped BigOperators
open Filter Topology

universe uS

variable {S : Type uS} [Fintype S] [DecidableEq S]

/-- Exact `t`-step law `μ₀ P^t`, packaged in the finite probability simplex. -/
def orbit
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) (t : ℕ) : stdSimplex ℝ S := by
  let Pt : Matrix S S ℝ := P ^ t
  have hPt : Pt ∈ Matrix.rowStochastic ℝ S := by
    exact (Matrix.rowStochastic ℝ S).pow_mem hP t
  let q : S → ℝ := Matrix.vecMul μ0.1 Pt
  refine ⟨q, ?_, ?_⟩
  · intro j
    exact Matrix.nonneg_vecMul_of_mem_rowStochastic hPt (fun i => stdSimplex.zero_le μ0 i) j
  · have hmass : μ0.1 ⬝ᵥ (1 : S → ℝ) = 1 := by
      rw [dotProduct_one]
      exact stdSimplex.sum_eq_one μ0
    have hqmass := Matrix.vecMul_dotProduct_one_eq_one_rowStochastic hPt hmass
    simpa [q, dotProduct_one] using hqmass

@[simp] theorem orbit_zero
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) :
    (orbit P hP μ0 0 : S → ℝ) = μ0.1 := by
  change Matrix.vecMul μ0.1 (1 : Matrix S S ℝ) = μ0.1
  exact Matrix.vecMul_one μ0.1

theorem orbit_succ
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) (t : ℕ) :
    (orbit P hP μ0 (t + 1) : S → ℝ) =
      Matrix.vecMul (orbit P hP μ0 t : S → ℝ) P := by
  change Matrix.vecMul μ0.1 (P ^ (t + 1)) =
    Matrix.vecMul (Matrix.vecMul μ0.1 (P ^ t)) P
  rw [pow_succ]
  exact (Matrix.vecMul_vecMul μ0.1 (P ^ t) P).symm

/-- The source Cesàro average with `N = n+1`, so division by zero is impossible. -/
def cesaroRow
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) (n : ℕ) : stdSimplex ℝ S := by
  let N : ℕ := n + 1
  let c : ℝ := (N : ℝ)⁻¹
  let q : S → ℝ := c • ∑ t ∈ Finset.range N, (orbit P hP μ0 t : S → ℝ)
  refine ⟨q, ?_, ?_⟩
  · intro j
    have hc : 0 ≤ c := by
      exact inv_nonneg.mpr (Nat.cast_nonneg N)
    have hsum : 0 ≤ (∑ t ∈ Finset.range N, (orbit P hP μ0 t : S → ℝ)) j := by
      simpa [Finset.sum_apply] using
        (Finset.sum_nonneg fun t (_ : t ∈ Finset.range N) =>
          stdSimplex.zero_le (orbit P hP μ0 t) j)
    simpa [q, Pi.smul_apply, smul_eq_mul] using mul_nonneg hc hsum
  · have hN : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    simp_rw [q, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    simp_rw [Finset.sum_apply]
    rw [Finset.sum_comm]
    simp_rw [stdSimplex.sum_eq_one]
    rw [Finset.sum_const, Finset.card_range]
    simp only [nsmul_eq_mul]
    change (N : ℝ)⁻¹ * ((N : ℝ) * 1) = 1
    rw [mul_one]
    exact inv_mul_cancel₀ hN

@[simp] theorem cesaroRow_coe
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) (n : ℕ) :
    (cesaroRow P hP μ0 n : S → ℝ) =
      ((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ t ∈ Finset.range (n + 1), (orbit P hP μ0 t : S → ℝ) := by
  rfl

private theorem sum_shift_sub_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ t ∈ Finset.range N, f (t + 1)) - (∑ t ∈ Finset.range N, f t) =
      f N - f 0 := by
  have hshift := Finset.sum_range_succ' f N
  have hend := Finset.sum_range_succ f N
  linarith

/-- The exact frozen §21.2 telescope
`μ̄_N P - μ̄_N = (μ₀ P^N - μ₀) / N`, with `N = n+1`. -/
theorem cesaro_residual_eq_boundary
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) (n : ℕ) :
    Matrix.vecMul (cesaroRow P hP μ0 n : S → ℝ) P -
        (cesaroRow P hP μ0 n : S → ℝ) =
      ((n + 1 : ℕ) : ℝ)⁻¹ •
        ((orbit P hP μ0 (n + 1) : S → ℝ) - μ0.1) := by
  ext j
  rw [cesaroRow_coe]
  rw [Matrix.smul_vecMul, Matrix.sum_vecMul]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_apply]
  simp_rw [← orbit_succ P hP μ0]
  rw [← mul_sub]
  have htel :=
    sum_shift_sub_sum (fun t => (orbit P hP μ0 t : S → ℝ) j) (n + 1)
  rw [htel]
  rw [orbit_zero]

private theorem orbit_sub_initial_abs_le_one
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) (t : ℕ) (j : S) :
    |(orbit P hP μ0 t : S → ℝ) j - μ0 j| ≤ 1 := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [stdSimplex.le_one (orbit P hP μ0 t) j, stdSimplex.zero_le μ0 j]
  · linarith [stdSimplex.le_one μ0 j, stdSimplex.zero_le (orbit P hP μ0 t) j]

/-- The boundary term in the frozen telescope vanishes coordinatewise, hence in
the finite product topology. -/
theorem boundary_tendsto_zero
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ)⁻¹ •
          ((orbit P hP μ0 (n + 1) : S → ℝ) - μ0.1))
      atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro j
  change Tendsto
    (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)⁻¹ * ((orbit P hP μ0 (n + 1) : S → ℝ) j - μ0 j))
    atTop (𝓝 0)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero
    (g := fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹)
    (fun n => abs_nonneg _) (fun n => ?_) ?_
  · have hc : 0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹) :=
      inv_nonneg.mpr (Nat.cast_nonneg (n + 1))
    have hdiff := orbit_sub_initial_abs_le_one P hP μ0 (n + 1) j
    change
      |((n + 1 : ℕ) : ℝ)⁻¹ * ((orbit P hP μ0 (n + 1) : S → ℝ) j - μ0 j)| ≤
        ((n + 1 : ℕ) : ℝ)⁻¹
    rw [abs_mul, abs_of_nonneg hc]
    calc
      ((↑(n + 1) : ℝ)⁻¹) * |(orbit P hP μ0 (n + 1)) j - μ0 j| ≤
          ((↑(n + 1) : ℝ)⁻¹) * 1 := mul_le_mul_of_nonneg_left hdiff hc
      _ = ((↑(n + 1) : ℝ)⁻¹) := by ring
  · simpa [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The Cesàro invariance residual tends to zero. -/
theorem cesaro_residual_tendsto_zero
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) :
    Tendsto
      (fun n : ℕ =>
        Matrix.vecMul (cesaroRow P hP μ0 n : S → ℝ) P -
          (cesaroRow P hP μ0 n : S → ℝ))
      atTop (𝓝 0) := by
  simpa only [cesaro_residual_eq_boundary] using boundary_tendsto_zero P hP μ0

/-- **P-GOA-01.** For a fixed finite stochastic kernel, the Cesàro averages
have a convergent subsequence, and every convergent subsequential limit is
invariant.  This is exactly the frozen §21.2 anchor; it does not claim full
Cesàro convergence or uniqueness of the invariant law. -/
theorem p_goa_01
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (μ0 : stdSimplex ℝ S) :
    (∃ ν : stdSimplex ℝ S, ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto (cesaroRow P hP μ0 ∘ φ) atTop (𝓝 ν)) ∧
      (∀ (ν : stdSimplex ℝ S) (φ : ℕ → ℕ),
        StrictMono φ →
        Tendsto (cesaroRow P hP μ0 ∘ φ) atTop (𝓝 ν) →
        Matrix.vecMul ν.1 P = ν.1) := by
  constructor
  · rcases CompactSpace.tendsto_subseq (cesaroRow P hP μ0) with
      ⟨ν, φ, hφ, hlim⟩
    exact ⟨ν, φ, hφ, hlim⟩
  · intro ν φ hφ hlim
    let residual : stdSimplex ℝ S → (S → ℝ) := fun μ =>
      Matrix.vecMul μ.1 P - μ.1
    have hcontinuous : Continuous residual := by
      exact
        (Continuous.matrix_vecMul continuous_subtype_val continuous_const).sub
          continuous_subtype_val
    have hlimResidual :
        Tendsto (residual ∘ (cesaroRow P hP μ0 ∘ φ)) atTop
          (𝓝 (residual ν)) := by
      exact (hcontinuous.tendsto ν).comp hlim
    have hzeroResidual :
        Tendsto (residual ∘ (cesaroRow P hP μ0 ∘ φ)) atTop (𝓝 0) := by
      have hglobal := cesaro_residual_tendsto_zero P hP μ0
      have hsub := hglobal.comp hφ.tendsto_atTop
      change Tendsto
        (fun n =>
          Matrix.vecMul (cesaroRow P hP μ0 (φ n) : S → ℝ) P -
            (cesaroRow P hP μ0 (φ n) : S → ℝ))
        atTop (𝓝 0)
      simpa only [Function.comp_def] using hsub
    have hres : residual ν = 0 :=
      tendsto_nhds_unique hlimResidual hzeroResidual
    exact sub_eq_zero.mp hres

end

end UEOT.V3.FiniteCesaroInvariant
