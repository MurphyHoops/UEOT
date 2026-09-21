import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Tactic

/-!
# P-EVO-03 — Perron mean growth and reproductive value

Frozen Core 3 §25.4 works with one finite primitive nonnegative mean-offspring
matrix `M`.  K-PF-01 is explicitly marked by the source as a standard theorem
(`K`): under primitivity it supplies the positive Perron root `R`, positive
right/left Perron vectors `r,l`, their normalizations, strict spectral
dominance, and the normalized rank-one power asymptotic.

This module does not pretend to reprove Perron--Frobenius inside UEOT.  Instead
`KPF01Certificate M` is a source-facing standard-theorem interface *tied to the
same primitive matrix `M`*.  In particular, normalized power convergence is not
a detached hypothesis and neither population limit from P-EVO-03 is assumed.

From that standard input the module machine-derives, for a nonzero natural
count row `z₀`,

* `R⁻ⁿ z₀ Mⁿ → (z₀ r) l`;
* normalized mean composition `z₀ Mⁿ / (z₀ Mⁿ 1) → l`;
* any positive linear valuation `w` satisfying `(zM)w = ρ zw` for every
  nonnegative row `z` has `ρ = R` and is a positive scalar multiple of `r`.

The final uniqueness is only relative to this fixed positive linear
reproduction mechanism.  No random-population, extinction, almost-sure growth,
or nonlinear/history-dependent valuation claim is made here.
-/

namespace UEOT.V3.EvolutionPerronGrowth

noncomputable section

open Filter Topology
open scoped BigOperators

universe uI

variable {I : Type uI} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Row-vector action used in the source notation `z M`. -/
def rowApply (z : I → ℝ) (M : Matrix I I ℝ) (j : I) : ℝ :=
  ∑ i : I, z i * M i j

/-- Finite linear reproductive-value pairing `z r`. -/
def rowDot (z r : I → ℝ) : ℝ :=
  ∑ i : I, z i * r i

/-- Literal finite count row, embedded into the real mean model. -/
def natRow (z : I → ℕ) : I → ℝ :=
  fun i => (z i : ℝ)

/-- Total mass of a finite real row. -/
def rowMass (z : I → ℝ) : ℝ :=
  ∑ i : I, z i

/--
Full source-designated K-PF-01 standard theorem interface for the one fixed
primitive matrix `M` used by P-EVO-03.

The complex spectral field records the source's strict dominance clause even
though the P-EVO-03 implication layer only needs positivity, normalization,
rank-one power convergence, and positive-eigenvector uniqueness.  No constructor
from `Matrix.IsPrimitive M` is claimed here: doing so would amount to a separate
formalization of the Perron--Frobenius standard theorem itself.
-/
structure KPF01Certificate (M : Matrix I I ℝ) where
  primitive : Matrix.IsPrimitive M
  R : ℝ
  r : I → ℝ
  l : I → ℝ
  R_pos : 0 < R
  r_pos : ∀ i, 0 < r i
  l_pos : ∀ i, 0 < l i
  right_eigen : ∀ i, ∑ j : I, M i j * r j = R * r i
  left_eigen : ∀ j, ∑ i : I, l i * M i j = R * l j
  l_sum : ∑ i : I, l i = 1
  lr_norm : ∑ i : I, l i * r i = 1
  /-- Coordinate form of `R⁻ⁿ Mⁿ → r l`; finite-dimensional coordinate
  convergence is equivalent to the matrix-space convergence used in the source. -/
  power_coord_tendsto : ∀ i j,
    Tendsto (fun n : ℕ => (R ^ n)⁻¹ * (M ^ n) i j) atTop (𝓝 (r i * l j))
  /-- The simple Perron eigendirection / uniqueness of positive right Perron
  vectors, another standard K-PF-01 output. -/
  positive_right_eigen_unique : ∀ (ρ : ℝ) (w : I → ℝ),
    (∀ i, 0 < w i) →
    (∀ i, ∑ j : I, M i j * w j = ρ * w i) →
    ρ = R ∧ ∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * r i
  /-- Source K-PF-01 strict spectral dominance, retained as provenance rather
  than silently discarded. -/
  strict_spectral_dominance : ∀ (μ : ℂ) (v : I → ℂ),
    v ≠ 0 →
    (∀ i, ∑ j : I, (M i j : ℂ) * v j = μ * v i) →
    μ ≠ (R : ℂ) → ‖μ‖ < R

/-- A nonzero finite count row has strictly positive reproductive value against
strictly positive Perron weights. -/
theorem initialReproductiveValue_pos
    (pf : KPF01Certificate M) (z0 : I → ℕ) (hz0 : z0 ≠ 0) :
    0 < rowDot (natRow z0) pf.r := by
  have hex : ∃ i, z0 i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 (funext h)
  obtain ⟨i, hi⟩ := hex
  have hi0 : 0 < (z0 i : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hi
  unfold rowDot natRow
  exact Finset.sum_pos'
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (pf.r_pos j).le)
    ⟨i, Finset.mem_univ i, mul_pos hi0 (pf.r_pos i)⟩

/-- Left multiplication of the K-PF-01 matrix-power limit by the fixed initial
count row gives the first limit in P-EVO-03. -/
theorem scaledMean_tendsto
    (pf : KPF01Certificate M) (z0 : I → ℕ) :
    Tendsto
      (fun n : ℕ => fun j : I =>
        (pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j)
      atTop
      (𝓝 (fun j : I => rowDot (natRow z0) pf.r * pf.l j)) := by
  rw [tendsto_pi_nhds]
  intro j
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ i : I,
          (z0 i : ℝ) * ((pf.R ^ n)⁻¹ * (M ^ n) i j))
        atTop
        (𝓝 (∑ i : I, (z0 i : ℝ) * (pf.r i * pf.l j))) := by
    apply tendsto_finsetSum Finset.univ
    intro i hi
    exact tendsto_const_nhds.mul (pf.power_coord_tendsto i j)
  have hseq :
      (fun n : ℕ => (pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j) =
        fun n : ℕ => ∑ i : I,
          (z0 i : ℝ) * ((pf.R ^ n)⁻¹ * (M ^ n) i j) := by
    funext n
    unfold rowApply natRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hlim :
      (∑ i : I, (z0 i : ℝ) * (pf.r i * pf.l j)) =
        rowDot (natRow z0) pf.r * pf.l j := by
    unfold rowDot natRow
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hlim] at hsum
  rw [hseq]
  exact hsum

/-- Summing the scaled mean-vector limit gives convergence of the scaled total
mean count to the positive initial reproductive value. -/
theorem scaledMass_tendsto
    (pf : KPF01Certificate M) (z0 : I → ℕ) :
    Tendsto
      (fun n : ℕ =>
        (pf.R ^ n)⁻¹ * rowMass (rowApply (natRow z0) (M ^ n)))
      atTop
      (𝓝 (rowDot (natRow z0) pf.r)) := by
  have hvec := scaledMean_tendsto pf z0
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ j : I,
          ((pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j))
        atTop
        (𝓝 (∑ j : I, rowDot (natRow z0) pf.r * pf.l j)) := by
    apply tendsto_finsetSum Finset.univ
    intro j hj
    exact (tendsto_pi_nhds.mp hvec) j
  have hseq :
      (fun n : ℕ =>
        (pf.R ^ n)⁻¹ * rowMass (rowApply (natRow z0) (M ^ n))) =
      fun n : ℕ => ∑ j : I,
        ((pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j) := by
    funext n
    unfold rowMass
    rw [Finset.mul_sum]
  have hlim :
      (∑ j : I, rowDot (natRow z0) pf.r * pf.l j) =
        rowDot (natRow z0) pf.r := by
    rw [← Finset.mul_sum, pf.l_sum, mul_one]
  rw [hlim] at hsum
  rw [hseq]
  exact hsum

/-- The denominator in the normalized composition is eventually strictly
positive.  This prevents Lean's totalized division at zero from hiding the
source's population-composition semantics. -/
theorem eventually_meanMass_pos
    (pf : KPF01Certificate M) (z0 : I → ℕ) (hz0 : z0 ≠ 0) :
    ∀ᶠ n : ℕ in atTop, 0 < rowMass (rowApply (natRow z0) (M ^ n)) := by
  have hlim := scaledMass_tendsto pf z0
  have hzr : 0 < rowDot (natRow z0) pf.r :=
    initialReproductiveValue_pos pf z0 hz0
  have hscaled : ∀ᶠ n : ℕ in atTop,
      0 < (pf.R ^ n)⁻¹ * rowMass (rowApply (natRow z0) (M ^ n)) := by
    exact (tendsto_order.1 hlim).1 _ hzr
  filter_upwards [hscaled] with n hn
  have hscale : 0 < (pf.R ^ n)⁻¹ := inv_pos.mpr (pow_pos pf.R_pos n)
  nlinarith [mul_pos hscale hn]

/-- Division by total mean mass gives the long-run mean type composition `l`. -/
theorem composition_tendsto
    (pf : KPF01Certificate M) (z0 : I → ℕ) (hz0 : z0 ≠ 0) :
    Tendsto
      (fun n : ℕ => fun j : I =>
        rowApply (natRow z0) (M ^ n) j /
          rowMass (rowApply (natRow z0) (M ^ n)))
      atTop
      (𝓝 pf.l) := by
  have hnum := scaledMean_tendsto pf z0
  have hden := scaledMass_tendsto pf z0
  have hzr : 0 < rowDot (natRow z0) pf.r :=
    initialReproductiveValue_pos pf z0 hz0
  rw [tendsto_pi_nhds]
  intro j
  have hj := (tendsto_pi_nhds.mp hnum) j
  have hratio := hj.div hden hzr.ne'
  have hfun :
      (fun n : ℕ =>
        rowApply (natRow z0) (M ^ n) j /
          rowMass (rowApply (natRow z0) (M ^ n))) =
      (fun n : ℕ =>
        ((pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j) /
          ((pf.R ^ n)⁻¹ * rowMass (rowApply (natRow z0) (M ^ n)))) := by
    funext n
    have ha : (pf.R ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n pf.R_pos.ne')
    exact (mul_div_mul_left
      (rowApply (natRow z0) (M ^ n) j)
      (rowMass (rowApply (natRow z0) (M ^ n))) ha).symm
  have hlim :
      rowDot (natRow z0) pf.r * pf.l j / rowDot (natRow z0) pf.r = pf.l j := by
    field_simp [hzr.ne']
  rw [hlim] at hratio
  rw [hfun]
  exact hratio

/-- Testing a linear valuation identity on coordinate unit rows derives the
literal right-eigenvector equation `M w = ρ w`; the eigenrelation is not assumed. -/
theorem valuation_identity_to_eigen
    (M : Matrix I I ℝ) (ρ : ℝ) (w : I → ℝ)
    (hval : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) →
      rowDot (rowApply z M) w = ρ * rowDot z w) :
    ∀ i, ∑ j : I, M i j * w j = ρ * w i := by
  intro i
  let e : I → ℝ := fun j => if j = i then 1 else 0
  have he : ∀ j, 0 ≤ e j := by
    intro j
    unfold e
    split <;> norm_num
  have h := hval e he
  unfold rowDot rowApply at h
  simpa [e, mul_assoc] using h

/-- Perron uniqueness turns the source's all-nonnegative-row linear valuation
identity into uniqueness of the positive reproductive-value weights. -/
theorem valuation_unique
    (pf : KPF01Certificate M) (ρ : ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i)
    (hval : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) →
      rowDot (rowApply z M) w = ρ * rowDot z w) :
    ρ = pf.R ∧ ∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * pf.r i := by
  exact pf.positive_right_eigen_unique ρ w hw
    (valuation_identity_to_eigen M ρ w hval)

/-- **P-EVO-03: mean growth and reproductive value.**

All three conclusions are derived from one primitive-matrix K-PF-01 standard
certificate attached to the exact same mean offspring matrix `M`.
-/
theorem p_evo_03
    (M : Matrix I I ℝ) (pf : KPF01Certificate M)
    (z0 : I → ℕ) (hz0 : z0 ≠ 0)
    (ρ : ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i)
    (hval : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) →
      rowDot (rowApply z M) w = ρ * rowDot z w) :
    Tendsto
      (fun n : ℕ => fun j : I =>
        (pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j)
      atTop
      (𝓝 (fun j : I => rowDot (natRow z0) pf.r * pf.l j))
    ∧ Tendsto
      (fun n : ℕ => fun j : I =>
        rowApply (natRow z0) (M ^ n) j /
          rowMass (rowApply (natRow z0) (M ^ n)))
      atTop
      (𝓝 pf.l)
    ∧ ρ = pf.R
    ∧ ∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * pf.r i := by
  have huniq := valuation_unique pf ρ w hw hval
  exact ⟨scaledMean_tendsto pf z0, composition_tendsto pf z0 hz0,
    huniq.1, huniq.2⟩

end

end UEOT.V3.EvolutionPerronGrowth
