/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths only.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpHorizon
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalProbability

/-!
# Nontrivial fixed-horizon simplex reference measures

The equality slice `sum τ = T` has zero mass under an ambient product Lebesgue
measure.  This module instead builds the horizon constraint into the path law.
It starts with `n` free holding-time coordinates in the unit cube, conditions
on their sum being at most one, scales them by `T`, and fills the final holding
interval with the residual time.

The resulting probability measure is supported on the horizon by construction.
Averaging it with its time reversal gives an explicitly reversal-invariant,
nonzero reference measure on the fixed-horizon path space.

The chart vocabulary shared by every user of this construction lives here too:
the simplex cut down to an available fraction, the fraction left after the free
coordinates, and the product of per-coordinate exponential survival weights.
These are chart-level notions with no reference to any particular chain, so
neither the general finite-generator development nor any concrete example owns
them.
-/

open MeasureTheory
open scoped ENNReal BigOperators ProbabilityTheory unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump
namespace Simplex

universe u

/-- Regard a point of the unit interval as a nonnegative real. -/
def unitNNReal (x : I) : NNReal :=
  ⟨x, x.2.1⟩

@[simp]
theorem coe_unitNNReal (x : I) : (unitNNReal x : ℝ) = x :=
  rfl

@[fun_prop]
theorem measurable_unitNNReal : Measurable unitNNReal :=
  measurable_subtype_coe.subtype_mk

/-- The standard `n`-simplex in the unit cube, expressed using `n` free
holding-time coordinates. -/
def freeSimplexSet (n : ℕ) : Set (Fin n → I) :=
  {u | ∑ i, (unitNNReal (u i) : ℝ) ≤ 1}

/-- The free-coordinate simplex is measurable. -/
theorem measurableSet_freeSimplexSet (n : ℕ) :
    MeasurableSet (freeSimplexSet n) := by
  unfold freeSimplexSet
  exact measurableSet_le (by fun_prop) measurable_const

/-- The free-coordinate simplex cut down to an available fraction `ρ` of the
horizon.  The chart scale is unchanged, so this expresses a shorter horizon
without rescaling the coordinates; `freeSimplexSet n` is the case `ρ = 1`.

The threshold is an arbitrary real rather than a point of `I` because the
renewal recursion subtracts a coordinate from it: splitting off the first
coordinate leaves the remaining ones in `freeSimplexSetAt n (ρ - u 0)` at the
same scale, and nothing keeps that difference inside `[0, 1]` a priori.  A
negative threshold simply gives the empty set. -/
def freeSimplexSetAt (n : ℕ) (ρ : ℝ) : Set (Fin n → I) :=
  {u | ∑ i, (u i : ℝ) ≤ ρ}

/-- The sub-horizon simplex is measurable. -/
theorem measurableSet_freeSimplexSetAt (n : ℕ) (ρ : ℝ) :
    MeasurableSet (freeSimplexSetAt n ρ) := by
  unfold freeSimplexSetAt
  exact measurableSet_le (by fun_prop) measurable_const

/-- The fraction of the horizon left after the `n` free coordinates. -/
def residualAt {n : ℕ} (ρ : ℝ) (u : Fin n → I) : ℝ :=
  ρ - ∑ i, (u i : ℝ)

@[fun_prop]
theorem measurable_residualAt {n : ℕ} (ρ : ℝ) :
    Measurable (residualAt (n := n) ρ) := by
  unfold residualAt
  fun_prop

/-- The fraction of the full horizon left after the `n` free coordinates. -/
def residual {n : ℕ} (u : Fin n → I) : ℝ :=
  1 - ∑ i, (u i : ℝ)

@[fun_prop]
theorem measurable_residual {n : ℕ} : Measurable (residual (n := n)) := by
  unfold residual
  fun_prop

theorem residualAt_one {n : ℕ} (u : Fin n → I) : residualAt 1 u = residual u :=
  rfl

/-- Product of per-coordinate exponential survival weights in free cube
coordinates.  Coordinate `i` carries rate `r i` over the scaled holding time
`T * u i`. -/
noncomputable def cubeExpWeight {n : ℕ} (r : Fin n → NNReal) (T : NNReal)
    (u : Fin n → I) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (Real.exp (-((r i : ℝ) * (T : ℝ) * (u i : ℝ))))

@[fun_prop]
theorem measurable_cubeExpWeight {n : ℕ} (r : Fin n → NNReal) (T : NNReal) :
    Measurable (cubeExpWeight r T) := by
  unfold cubeExpWeight
  fun_prop

private theorem freeSimplexSection {n : ℕ} (t x : I) :
    (fun v : Fin n → I => (x, v)) ⁻¹'
        {p : I × (Fin n → I) |
          (p.1 : ℝ) + ∑ i, (p.2 i : ℝ) ≤ (t : ℝ)} =
      if _hx : x ≤ t then
        freeSimplexSetAt n ((t : ℝ) - (x : ℝ))
      else ∅ := by
  split_ifs with hx
  · ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, freeSimplexSetAt]
    constructor <;> intro h <;> linarith
  · ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    have hsum : 0 ≤ ∑ i, (v i : ℝ) :=
      Finset.sum_nonneg fun _ _ => (v _).2.1
    intro h
    apply hx
    exact_mod_cast (show (x : ℝ) ≤ (t : ℝ) by linarith)

private theorem lintegral_freeSimplexSection (n : ℕ) (t : I) :
    ∫⁻ x : I in Set.Iic t,
        ENNReal.ofReal (((t : ℝ) - (x : ℝ)) ^ n / (n.factorial : ℝ)) =
      ENNReal.ofReal ((t : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
  let f : ℝ → ℝ := fun x =>
    ((t : ℝ) - x) ^ n / (n.factorial : ℝ)
  have hpre :
      ((fun x : I => (x : ℝ)) ⁻¹' Set.Icc (0 : ℝ) (t : ℝ)) =
        Set.Iic t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Iic]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨x.2.1, h⟩
  rw [← hpre]
  change (∫⁻ x : I in
      (fun x : I => (x : ℝ)) ⁻¹' Set.Icc (0 : ℝ) (t : ℝ),
      ENNReal.ofReal (f (x : ℝ))) =
    ENNReal.ofReal ((t : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ))
  rw [unitInterval.measurePreserving_coe.setLIntegral_comp_preimage_emb
    unitInterval.measurableEmbedding_coe
    (fun x : ℝ => ENNReal.ofReal (f x)) (Set.Icc 0 (t : ℝ))]
  change (∫⁻ x : ℝ, ENNReal.ofReal (f x)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).restrict
        (Set.Icc 0 (t : ℝ)))) =
    ENNReal.ofReal ((t : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ))
  rw [Measure.restrict_restrict measurableSet_Icc]
  have hsubset : Set.Icc (0 : ℝ) (t : ℝ) ⊆ Set.Icc (0 : ℝ) 1 :=
    Set.Icc_subset_Icc le_rfl t.2.2
  rw [Set.inter_eq_left.mpr hsubset]
  have hfcont : Continuous f := by
    fun_prop
  have hfint : Integrable f (volume.restrict (Set.Icc 0 (t : ℝ))) :=
    hfcont.integrableOn_Icc
  have hfnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    dsimp [f]
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) n)
      (Nat.cast_nonneg n.factorial)
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn]
  congr 1
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le t.2.1]
  simp only [f, div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  have hcomp :
      (∫ x : ℝ in 0..(t : ℝ), ((t : ℝ) - x) ^ n) =
        ∫ x : ℝ in 0..(t : ℝ), x ^ n := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => x ^ n) (d := (t : ℝ))
        (a := 0) (b := (t : ℝ)))
  rw [hcomp, integral_pow, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **The sub-horizon simplex has volume `t^n / n!`.**  The induction splits off
the first coordinate with `piFinSuccAbove` and recurses on the remaining
sub-horizon `t - u 0`, which is the same peeling the horizon-direction renewal
argument needs; the `t^n` here is the Jacobian such a rescaling would carry. -/
theorem volume_freeSimplexSetAt (n : ℕ) (t : I) :
    (volume : Measure (Fin n → I)) (freeSimplexSetAt n t) =
      ENNReal.ofReal ((t : ℝ) ^ n / (n.factorial : ℝ)) := by
  induction n generalizing t with
    | zero =>
        have hset : freeSimplexSetAt 0 t = Set.univ := by
          ext u
          simp [freeSimplexSetAt, t.2.1]
        simp [hset]
    | succ n ih =>
        let e :=
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => I) 0
        let s : Set (I × (Fin n → I)) :=
          {p | (p.1 : ℝ) + ∑ i, (p.2 i : ℝ) ≤ (t : ℝ)}
        have hs : MeasurableSet s := by
          dsimp [s]
          exact measurableSet_le (by fun_prop) measurable_const
        have hpre : e ⁻¹' s = freeSimplexSetAt (n + 1) t := by
          ext u
          change
            (u 0 : ℝ) + ∑ i : Fin n, (u i.succ : ℝ) ≤ (t : ℝ) ↔
              ∑ i : Fin (n + 1), (u i : ℝ) ≤ (t : ℝ)
          rw [Fin.sum_univ_succ]
        rw [← hpre,
          (volume_preserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => I) 0).measure_preimage
              hs.nullMeasurableSet]
        change ((volume : Measure I).prod
          (volume : Measure (Fin n → I))) s = _
        rw [Measure.prod_apply hs]
        dsimp [s]
        have hsection : ∀ x : I,
            (volume : Measure (Fin n → I))
                {a | (x : ℝ) + ∑ i, (a i : ℝ) ≤ (t : ℝ)} =
              if hx : x ≤ t then
                ENNReal.ofReal
                  (((t : ℝ) - (x : ℝ)) ^ n / (n.factorial : ℝ))
              else 0 := by
          intro x
          rw [show {a : Fin n → I |
              (x : ℝ) + ∑ i, (a i : ℝ) ≤ (t : ℝ)} =
                if hx : x ≤ t then
                  freeSimplexSetAt n ((t : ℝ) - (x : ℝ))
                else ∅ from freeSimplexSection t x]
          split_ifs with hx
          · exact ih ⟨(t : ℝ) - (x : ℝ), sub_nonneg.mpr hx,
              by linarith [t.2.2, x.2.1]⟩
          · simp
        simp_rw [hsection]
        have hind :
            (fun x : I =>
              if hx : x ≤ t then
                ENNReal.ofReal
                  (((t : ℝ) - (x : ℝ)) ^ n / (n.factorial : ℝ))
              else 0) =
            (Set.Iic t).indicator (fun x : I =>
              ENNReal.ofReal
                (((t : ℝ) - (x : ℝ)) ^ n / (n.factorial : ℝ))) := by
          funext x
          simp only [Set.indicator_apply, Set.mem_Iic]
          split_ifs <;> rfl
        rw [hind, MeasureTheory.lintegral_indicator measurableSet_Iic,
          lintegral_freeSimplexSection]

/-- The standard free-coordinate `n`-simplex has volume `1 / n!`.  It is the
sub-horizon simplex at full horizon. -/
theorem volume_freeSimplexSet (n : ℕ) :
    (volume : Measure (Fin n → I)) (freeSimplexSet n) =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  simpa [freeSimplexSet, freeSimplexSetAt] using
    volume_freeSimplexSetAt n (1 : I)

/-- A bounded measurable function is integrable on a bounded interval.  The
transfer below wants integrability, and a renewal argument supplies exactly
this: its solution is known to be bounded and measurable long before it is
known to be continuous. -/
theorem integrableOn_Icc_of_bound {f : ℝ → ℝ} {a b : ℝ}
    (hm : Measurable f) {M : ℝ} (hM : ∀ w ∈ Set.Icc a b, |f w| ≤ M) :
    IntegrableOn f (Set.Icc a b) := by
  refine Measure.integrableOn_of_bounded (M := M)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    hm.aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with w hw
  rw [Real.norm_eq_abs]
  exact hM w hw

/-- Convert a nonnegative Lebesgue integral over an initial segment of the unit
interval into an ordinary interval integral.

This is the one-dimensional transfer between the unit-interval chart and the
real line.  Renewal arguments in the horizon direction peel a single holding
coordinate, which lands in the chart, while the analytic side works with
interval integrals; this is the only place the two have to be reconciled. -/
theorem lintegral_unitInterval_Iic_of_integrableOn
    (f : ℝ → ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) ρ))
    (hfnn : ∀ z ∈ Set.Icc (0 : ℝ) ρ, 0 ≤ f z) :
    ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ}, ENNReal.ofReal (f (a : ℝ)) =
      ENNReal.ofReal (∫ z : ℝ in (0 : ℝ)..ρ, f z) := by
  have hpre :
      ((fun a : I => (a : ℝ)) ⁻¹' Set.Icc (0 : ℝ) ρ) =
        {a : I | (a : ℝ) ≤ ρ} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨a.2.1, h⟩⟩
  rw [← hpre]
  rw [unitInterval.measurePreserving_coe.setLIntegral_comp_preimage_emb
    unitInterval.measurableEmbedding_coe
    (fun z : ℝ => ENNReal.ofReal (f z)) (Set.Icc 0 ρ)]
  change (∫⁻ z : ℝ, ENNReal.ofReal (f z)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).restrict
        (Set.Icc 0 ρ))) = _
  rw [Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (Set.Icc_subset_Icc le_rfl hρ1)]
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) ρ)] f := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with z hz
    exact hfnn z hz
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnn,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hρ0]

/-- The transfer for a continuous integrand.  Continuity is only used to get
integrability, which is why the general form above asks for that directly: a
renewal argument produces a bounded measurable integrand before it knows the
solution is continuous. -/
theorem lintegral_unitInterval_Iic_of_continuous_nonneg
    (f : ℝ → ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hf : Continuous f)
    (hfnn : ∀ z ∈ Set.Icc (0 : ℝ) ρ, 0 ≤ f z) :
    ∫⁻ a : I in {a : I | (a : ℝ) ≤ ρ}, ENNReal.ofReal (f (a : ℝ)) =
      ENNReal.ofReal (∫ z : ℝ in (0 : ℝ)..ρ, f z) :=
  lintegral_unitInterval_Iic_of_integrableOn f ρ hρ0 hρ1 hf.integrableOn_Icc hfnn

/-- The simplex event has strictly positive product volume, so conditioning on
it is nondegenerate for every jump count, including `n = 0`. -/
theorem volume_freeSimplexSet_pos (n : ℕ) :
    0 < (volume : Measure (Fin n → I)) (freeSimplexSet n) := by
  rw [volume_freeSimplexSet]
  exact ENNReal.ofReal_pos.2 (by positivity)

/-- The uniform probability law on the free-coordinate simplex.  It is the
finite product of unit-interval Lebesgue measures conditioned on `sum u ≤ 1`. -/
noncomputable def freeSimplexProbability (n : ℕ) : Measure (Fin n → I) :=
  (volume : Measure (Fin n → I))[|freeSimplexSet n]

noncomputable instance instIsProbabilityMeasureFreeSimplexProbability (n : ℕ) :
    IsProbabilityMeasure (freeSimplexProbability n) := by
  unfold freeSimplexProbability
  exact ProbabilityTheory.cond_isProbabilityMeasure
    (ne_of_gt (volume_freeSimplexSet_pos n))

/-- Fill the last holding interval with the residual time after scaling the
`n` free simplex coordinates by the physical horizon `T`. -/
def holdingTimesOfFree {n : ℕ} (T : NNReal) (u : Fin n → I) :
    Fin (n + 1) → NNReal :=
  Fin.snoc (fun i => T * unitNNReal (u i))
    (T - ∑ i, T * unitNNReal (u i))

@[fun_prop]
theorem measurable_holdingTimesOfFree {n : ℕ} (T : NNReal) :
    Measurable (holdingTimesOfFree (n := n) T) := by
  unfold holdingTimesOfFree
  fun_prop

/-- On the simplex event, the completed holding-time vector has total duration
exactly `T`. -/
theorem sum_holdingTimesOfFree {n : ℕ} (T : NNReal) (u : Fin n → I)
    (hu : u ∈ freeSimplexSet n) :
    ∑ i, holdingTimesOfFree T u i = T := by
  have hsum : (∑ i, unitNNReal (u i)) ≤ (1 : NNReal) := by
    change (∑ i, (unitNNReal (u i) : ℝ)) ≤ 1 at hu
    exact_mod_cast hu
  have hscaled : (∑ i, T * unitNNReal (u i)) ≤ T := by
    rw [← Finset.mul_sum]
    simpa using mul_le_mul_right hsum T
  rw [Fin.sum_univ_castSucc]
  simp only [holdingTimesOfFree, Fin.snoc_castSucc, Fin.snoc_last]
  exact add_tsub_cancel_of_le hscaled

/-- Assemble a state sequence and free simplex coordinates into a fixed-horizon
jump path. -/
def assemblePath {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (T : NNReal) :
    (Fin (n + 1) → Ω) × (Fin n → I) → JumpPath Ω n :=
  fun p => (p.1, holdingTimesOfFree T p.2)

@[fun_prop]
theorem measurable_assemblePath {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) : Measurable (assemblePath (Ω := Ω) (n := n) T) := by
  unfold assemblePath
  fun_prop

/-- A raw fixed-horizon path probability obtained from an arbitrary probability
law on state sequences and the uniform free-coordinate simplex law. -/
noncomputable def rawPathProbability {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    Measure (JumpPath Ω n) :=
  (stateLaw.prod (freeSimplexProbability n)).map
    (assemblePath (Ω := Ω) (n := n) T)

noncomputable instance instIsProbabilityMeasureRawPathProbability
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (T : NNReal)
    (stateLaw : Measure (Fin (n + 1) → Ω)) [IsProbabilityMeasure stateLaw] :
    IsProbabilityMeasure (rawPathProbability T stateLaw) := by
  unfold rawPathProbability
  exact Measure.isProbabilityMeasure_map
    (measurable_assemblePath (Ω := Ω) (n := n) T).aemeasurable

/-- Average a path measure with its time reversal.  This construction is useful
when the underlying simplex volume is known mathematically to be symmetric but
one wants reversal invariance to be definitional at the measure level. -/
noncomputable def symmetrizePathMeasure {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure (JumpPath Ω n)) : Measure (JumpPath Ω n) :=
  (2 : ℝ≥0∞)⁻¹ • (μ + μ.map JumpPath.reverse)

/-- Symmetrization is invariant under path reversal. -/
theorem map_symmetrizePathMeasure_reverse
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure (JumpPath Ω n)) :
    (symmetrizePathMeasure μ).map JumpPath.reverse =
      symmetrizePathMeasure μ := by
  ext s hs
  rw [Measure.map_apply JumpPath.measurable_reverse hs]
  simp only [symmetrizePathMeasure, Measure.smul_apply, Measure.add_apply]
  rw [Measure.map_apply JumpPath.measurable_reverse
    (JumpPath.measurable_reverse hs)]
  have hpre : JumpPath.reverse ⁻¹' (JumpPath.reverse ⁻¹' s) = s := by
    ext γ
    simp
  rw [hpre, Measure.map_apply JumpPath.measurable_reverse hs]
  ac_rfl

/-- Symmetrizing a probability measure preserves normalization. -/
theorem isProbabilityMeasure_symmetrizePathMeasure
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure (JumpPath Ω n)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetrizePathMeasure μ) := by
  letI : IsProbabilityMeasure (μ.map JumpPath.reverse) :=
    Measure.isProbabilityMeasure_map JumpPath.measurable_reverse.aemeasurable
  constructor
  simp [symmetrizePathMeasure]
  calc
    (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 2⁻¹ * 2 := by ring
    _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The nontrivial, reversal-invariant fixed-horizon path probability used as a
canonical simplex reference. -/
noncomputable def pathProbability {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    Measure (JumpPath Ω n) :=
  symmetrizePathMeasure (rawPathProbability T stateLaw)

noncomputable instance instIsProbabilityMeasurePathProbability
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (T : NNReal)
    (stateLaw : Measure (Fin (n + 1) → Ω)) [IsProbabilityMeasure stateLaw] :
    IsProbabilityMeasure (pathProbability T stateLaw) :=
  isProbabilityMeasure_symmetrizePathMeasure _

/-- The simplex path probability is reversal invariant. -/
theorem map_pathProbability_reverse
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    (pathProbability T stateLaw).map JumpPath.reverse =
      pathProbability T stateLaw :=
  map_symmetrizePathMeasure_reverse _

/-- The raw simplex construction is supported on paths of total duration `T`. -/
theorem rawPathProbability_ae_horizon
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    ∀ᵐ γ ∂rawPathProbability T stateLaw,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
  have hf : Measurable (assemblePath (Ω := Ω) (n := n) T) :=
    measurable_assemblePath T
  change ∀ᵐ γ ∂rawPathProbability T stateLaw,
    JumpPath.totalHoldingTime γ = T
  unfold rawPathProbability
  rw [ae_map_iff hf.aemeasurable (by
    simpa [JumpPath.horizonSet] using
      (JumpPath.measurableSet_horizonSet (Ω := Ω) (n := n) T))]
  have hmeas : MeasurableSet
      {p : (Fin (n + 1) → Ω) × (Fin n → I) |
        JumpPath.totalHoldingTime
          (assemblePath (Ω := Ω) (n := n) T p) = T} := by
    simpa [Function.comp_def] using
      (((JumpPath.measurable_totalHoldingTime (Ω := Ω) (n := n)).comp hf).eq_const T |>.setOf)
  apply (Measure.ae_prod_iff_ae_ae
    (μ := stateLaw) (ν := freeSimplexProbability n) hmeas).2
  refine ae_of_all stateLaw fun states => ?_
  have hmem : ∀ᵐ u ∂freeSimplexProbability n, u ∈ freeSimplexSet n := by
    unfold freeSimplexProbability
    exact ProbabilityTheory.ae_cond_mem (measurableSet_freeSimplexSet n)
  exact hmem.mono fun u hu => by
    change ∑ i, holdingTimesOfFree T u i = T
    exact sum_holdingTimesOfFree T u hu

/-- Symmetrization preserves concentration on the reversal-invariant horizon. -/
theorem pathProbability_ae_horizon
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω)) :
    ∀ᵐ γ ∂pathProbability T stateLaw,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
  have hraw := rawPathProbability_ae_horizon T stateLaw
  have hraw' :
      ∀ᵐ γ ∂rawPathProbability T stateLaw,
        JumpPath.totalHoldingTime γ = T := by
    simpa [JumpPath.horizonSet] using hraw
  have hreverse :
      ∀ᵐ γ ∂(rawPathProbability T stateLaw).map JumpPath.reverse,
        γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
    change ∀ᵐ γ ∂(rawPathProbability T stateLaw).map JumpPath.reverse,
      JumpPath.totalHoldingTime γ = T
    rw [ae_map_iff JumpPath.measurable_reverse.aemeasurable (by
      simpa [JumpPath.horizonSet] using
        (JumpPath.measurableSet_horizonSet (Ω := Ω) (n := n) T))]
    exact hraw'.mono fun γ hγ => by
      simpa using hγ
  unfold pathProbability symmetrizePathMeasure
  exact Measure.ae_smul_measure
    ((ae_add_measure_iff).2 ⟨hraw, hreverse⟩) _

/-- Scale the canonical horizon probability to obtain a reference measure of a
prescribed finite mass. -/
noncomputable def reference {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    (mass : ℝ≥0∞) : Measure (JumpPath Ω n) :=
  mass • pathProbability T stateLaw

/-- Every scaled simplex reference is reversal invariant. -/
theorem map_reference_reverse
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    (mass : ℝ≥0∞) :
    (reference T stateLaw mass).map JumpPath.reverse =
      reference T stateLaw mass := by
  simp [reference, map_pathProbability_reverse]

/-- The total mass of the scaled reference is the requested scalar. -/
theorem reference_univ
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    [IsProbabilityMeasure stateLaw] (mass : ℝ≥0∞) :
    reference T stateLaw mass Set.univ = mass := by
  simp [reference]

/-- Positive mass gives a genuinely nonzero fixed-horizon reference measure. -/
theorem reference_ne_zero
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    [IsProbabilityMeasure stateLaw] {mass : ℝ≥0∞} (hmass : mass ≠ 0) :
    reference T stateLaw mass ≠ 0 := by
  unfold reference
  intro hzero
  rcases Measure.ennreal_smul_eq_zero.mp hzero with h | h
  · exact hmass h
  · exact IsProbabilityMeasure.ne_zero _ h

/-- The scaled reference remains concentrated on the physical horizon. -/
theorem reference_ae_horizon
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (stateLaw : Measure (Fin (n + 1) → Ω))
    (mass : ℝ≥0∞) :
    ∀ᵐ γ ∂reference T stateLaw mass,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T :=
  Measure.ae_smul_measure (pathProbability_ae_horizon T stateLaw) mass

end Simplex
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
