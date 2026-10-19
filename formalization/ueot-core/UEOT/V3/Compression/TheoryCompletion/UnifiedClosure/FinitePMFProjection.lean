import UEOT.V3.PathError
import Mathlib.Tactic

/-!
# Finite PMF projection and conditional disintegration

The conditional row is constructed from the actual microscopic law.  Its
fallback is used only on zero-mass projected histories.  No Markov property
of the projected process is assumed.

Scratch implementation checkpoint; imports only existing source modules.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory
open UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe uX uY uZ

/-- The actual law conditioned on a positive-mass projection fibre. -/
def riskFiberPosterior
    {X : Type uX} {Y : Type uY}
    (p : PMF X) (f : X → Y) (y : Y)
    (hy : y ∈ (p.map f).support) : PMF X :=
  p.filter {x | f x = y} (by
    rcases (PMF.mem_support_map_iff f p y).1 hy with ⟨x, hx, hxy⟩
    exact ⟨x, hxy, hx⟩)

@[simp] theorem riskFiberPosterior_support
    {X : Type uX} {Y : Type uY}
    (p : PMF X) (f : X → Y) (y : Y)
    (hy : y ∈ (p.map f).support) :
    (riskFiberPosterior p f y hy).support = {x | f x = y} ∩ p.support := by
  simp [riskFiberPosterior]

/-- Undo conditioning without dividing on a null fibre. -/
theorem risk_map_mul_fiberPosterior
    {X : Type uX} {Y : Type uY}
    (p : PMF X) (f : X → Y) (y : Y)
    (hy : y ∈ (p.map f).support) (x : X) :
    (p.map f) y * riskFiberPosterior p f y hy x =
      if f x = y then p x else 0 := by
  classical
  have hden :
      (∑' a, ({x | f x = y}.indicator (fun x => p x)) a) = (p.map f) y := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro a
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, eq_comm]
  have hne : (p.map f) y ≠ 0 := (PMF.mem_support_iff _ _).1 hy
  simp only [riskFiberPosterior, PMF.filter_apply, hden]
  rw [mul_left_comm, ENNReal.mul_inv_cancel hne (PMF.apply_ne_top _ _), mul_one]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- A projected conditional successor row, with explicit null-history fallback. -/
def riskConditionedRow
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    (p : PMF X) (f : X → Y) (K : X → PMF Z)
    (fallback : Y → PMF Z) (y : Y) : PMF Z := by
  classical
  exact if hy : y ∈ (p.map f).support then
    (riskFiberPosterior p f y hy).bind K
  else fallback y

/-- The joint microscopic mass factors through the constructed conditional row. -/
theorem risk_conditionedRow_mass
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Fintype X]
    (p : PMF X) (f : X → Y) (K : X → PMF Z)
    (fallback : Y → PMF Z) (y : Y) (z : Z) :
    (p.map f) y * riskConditionedRow p f K fallback y z =
      ∑ x, if f x = y then p x * K x z else 0 := by
  classical
  by_cases hy : y ∈ (p.map f).support
  · rw [riskConditionedRow, dif_pos hy, PMF.bind_apply, tsum_fintype,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_assoc, risk_map_mul_fiberPosterior]
    by_cases hx : f x = y <;> simp [hx]
  · have hm : (p.map f) y = 0 := by
      by_contra hm
      exact hy ((PMF.mem_support_iff _ _).2 hm)
    rw [hm, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : f x = y
    · have hpx : p x = 0 := by
        by_contra hpx
        exact hy ((PMF.mem_support_map_iff f p y).2
          ⟨x, (PMF.mem_support_iff _ _).2 hpx, hx⟩)
      simp [hx, hpx]
    · simp [hx]

/-- Point-mass formula for the actual projected joint law. -/
theorem risk_map_extend_apply
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Fintype X] [Fintype Z]
    (p : PMF X) (f : X → Y) (K : X → PMF Z) (y : Y) (z : Z) :
    ((pmfExtend p K).map (fun hz => (f hz.1, hz.2))) (y, z) =
      ∑ x, if f x = y then p x * K x z else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, ← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f x = y
  · simp [pmfExtend_apply, hx]
  · have hyx : y ≠ f x := Ne.symm hx
    simp [hx, hyx]

/-- The constructed history kernel gives exactly the actual projected law. -/
theorem risk_map_extend_eq
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Fintype X] [Fintype Y] [Fintype Z]
    (p : PMF X) (f : X → Y) (K : X → PMF Z)
    (fallback : Y → PMF Z) :
    (pmfExtend p K).map (fun hz => (f hz.1, hz.2)) =
      pmfExtend (p.map f) (riskConditionedRow p f K fallback) := by
  apply PMF.ext
  rintro ⟨y, z⟩
  rw [risk_map_extend_apply, pmfExtend_apply]
  exact (risk_conditionedRow_mass p f K fallback y z).symm

/-- Mapping only the newly sampled symbol commutes with causal extension. -/
theorem risk_map_extend_right
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    (p : PMF X) (K : X → PMF Y) (g : Y → Z) :
    (pmfExtend p K).map (fun hz => (hz.1, g hz.2)) =
      pmfExtend p (fun x => (K x).map g) := by
  unfold pmfExtend
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp, PMF.map_comp]
  rfl

private theorem risk_sum_toReal
    {X : Type uX} [Fintype X] (p : PMF X) :
    ∑ x, (p x).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [tsum_fintype, ENNReal.toReal_sum
    (fun x _ => PMF.apply_ne_top p x)] at h
  simpa using h

private theorem risk_bind_apply_toReal
    {X : Type uX} {Z : Type uZ} [Fintype X]
    (p : PMF X) (K : X → PMF Z) (z : Z) :
    ((p.bind K) z).toReal = ∑ x, (p x).toReal * (K x z).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (by
    intro x _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top p x) (PMF.apply_ne_top (K x) z))]
  simp only [ENNReal.toReal_mul]

/-- Common mixing weights preserve a uniform overlap bound on their support. -/
theorem risk_commonMass_bind_lower_bound
    {X : Type uX} {Z : Type uZ} [Fintype X] [Fintype Z]
    (p : PMF X) (K L : X → PMF Z) (s : ℝ)
    (hs : ∀ x ∈ p.support, s ≤ pmfCommonMass (K x) (L x)) :
    s ≤ pmfCommonMass (p.bind K) (p.bind L) := by
  classical
  have hweighted : ∀ x,
      (p x).toReal * s ≤ (p x).toReal * pmfCommonMass (K x) (L x) := by
    intro x
    by_cases hx : x ∈ p.support
    · exact mul_le_mul_of_nonneg_left (hs x hx) ENNReal.toReal_nonneg
    · have hz : p x = 0 := by
        by_contra hz
        exact hx ((PMF.mem_support_iff _ _).2 hz)
      simp [hz]
  calc
    s = (∑ x, (p x).toReal) * s := by rw [risk_sum_toReal, one_mul]
    _ = ∑ x, (p x).toReal * s := by rw [Finset.sum_mul]
    _ ≤ ∑ x, (p x).toReal * pmfCommonMass (K x) (L x) :=
      Finset.sum_le_sum (fun x _ => hweighted x)
    _ = ∑ z, ∑ x,
        (p x).toReal * min (K x z).toReal (L x z).toReal := by
      simp only [pmfCommonMass, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ z, min
        (∑ x, (p x).toReal * (K x z).toReal)
        (∑ x, (p x).toReal * (L x z).toReal) := by
      apply Finset.sum_le_sum
      intro z _
      apply le_min
      · exact Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (min_le_left _ _) ENNReal.toReal_nonneg
      · exact Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (min_le_right _ _) ENNReal.toReal_nonneg
    _ = pmfCommonMass (p.bind K) (p.bind L) := by
      simp only [pmfCommonMass, risk_bind_apply_toReal]

/-- TV convexity with the same actual mixing law, requiring bounds only on its support. -/
theorem risk_tv_bind_same_weights
    {X : Type uX} {Z : Type uZ} [Fintype X] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p : PMF X) (K L : X → PMF Z) (ε : ℝ)
    (hrow : ∀ x ∈ p.support,
      tvDist (K x).toMeasure (L x).toMeasure ≤ ε) :
    tvDist (p.bind K).toMeasure (p.bind L).toMeasure ≤ ε := by
  have hcommon := risk_commonMass_bind_lower_bound p K L (1 - ε)
    (fun x hx => pmfCommonMass_ge_one_sub_tvBound (K x) (L x) (hrow x hx))
  rw [tvDist_eq_one_sub_pmfCommonMass]
  linarith

/-- The actual projected conditional row inherits the uniform microscopic row bound.
On a null projected history it is literally the reference row. -/
theorem risk_conditionedRow_tv_le
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Fintype X] [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p : PMF X) (f : X → Y) (K : X → PMF Z) (L : Y → PMF Z)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hrow : ∀ x, tvDist (K x).toMeasure (L (f x)).toMeasure ≤ ε)
    (y : Y) :
    tvDist (riskConditionedRow p f K L y).toMeasure (L y).toMeasure ≤ ε := by
  classical
  by_cases hy : y ∈ (p.map f).support
  · rw [riskConditionedRow, dif_pos hy]
    have hmix := risk_tv_bind_same_weights
      (riskFiberPosterior p f y hy) K (fun _ => L y) ε (by
        intro x hx
        have hxy : f x = y := (riskFiberPosterior_support p f y hy ▸ hx).1
        simpa only [hxy] using hrow x)
    simpa only [PMF.bind_const] using hmix
  · rw [riskConditionedRow, dif_neg hy, tvDist_self_eq_zero]
    exact hε

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
