/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the original source LICENSE.
Adapted for UEOT from Causalean/Mathlib/Probability/BernoulliMeasure.lean.
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact Bernoulli KL formula

Minimal P-INFO-04 support layer.  This is an attributed adaptation of the
machine-checked two-point KL calculation from CausalSmith/Causalean.  Only the
exact formula needed by the error-indicator Fano proof is retained.
-/

namespace UEOT.V3.InformationBernoulliKL

open MeasureTheory InformationTheory

/-- Real-valued Bernoulli law supported on `0` and `1`. -/
noncomputable def bernoulliLaw (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)

lemma bernoulliLaw_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂(bernoulliLaw p) = p * f 1 + (1 - p) * f 0 := by
  unfold bernoulliLaw
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [hp0, sub_nonneg.mpr hp1, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac (1 : ℝ))
      (c := ENNReal.ofReal p)
      (integrable_dirac (f := f) (a := (1 : ℝ)) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac (0 : ℝ))
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac (f := f) (a := (0 : ℝ)) (by simp [enorm])) (by simp)

lemma bernoulliLaw_isProbabilityMeasure {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliLaw p) := by
  rw [isProbabilityMeasure_iff]
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  norm_num

lemma bernoulliLaw_ac_of_reference_interior {p q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliLaw p ≪ bernoulliLaw q := by
  have hq_ne0 : ENNReal.ofReal q ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have h1q_ne0 : ENNReal.ofReal (1 - q) ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  unfold bernoulliLaw at hzero ⊢
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hzero ⊢
  by_cases h1 : (1 : ℝ) ∈ s
  · exfalso
    by_cases h0 : (0 : ℝ) ∈ s
    · simp [h1, h0, hq_ne0] at hzero
    · simp [h1, h0, hq_ne0] at hzero
  · by_cases h0 : (0 : ℝ) ∈ s
    · exfalso
      simp [h1, h0, h1q_ne0] at hzero
    · simp [h1, h0]

@[fun_prop]
lemma bernoulliLaw_llr_integrable {p q : ℝ} :
    Integrable (llr (bernoulliLaw p) (bernoulliLaw q)) (bernoulliLaw p) := by
  unfold bernoulliLaw
  rw [integrable_add_measure]
  constructor
  · exact Integrable.smul_measure (μ := Measure.dirac (1 : ℝ))
      (c := ENNReal.ofReal p)
      (integrable_dirac
        (f := llr (ENNReal.ofReal p • Measure.dirac (1 : ℝ)
          + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) (bernoulliLaw q))
        (a := (1 : ℝ)) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac (0 : ℝ))
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac
        (f := llr (ENNReal.ofReal p • Measure.dirac (1 : ℝ)
          + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) (bernoulliLaw q))
        (a := (0 : ℝ)) (by simp [enorm])) (by simp)

/-- Exact two-point KL formula.  The reference probability is required to lie
strictly inside `(0,1)`; the source application uses `q = 1/K`, `K ≥ 2`. -/
lemma bernoulliLaw_klDiv_toReal {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (klDiv (bernoulliLaw p) (bernoulliLaw q)).toReal =
      p * Real.log (p / q) +
        (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  classical
  haveI hp_prob : IsProbabilityMeasure (bernoulliLaw p) :=
    bernoulliLaw_isProbabilityMeasure hp0 hp1
  haveI hq_prob : IsProbabilityMeasure (bernoulliLaw q) :=
    bernoulliLaw_isProbabilityMeasure hq0.le hq1.le
  let g : ℝ → ENNReal := fun x =>
    if x = 1 then ENNReal.ofReal (p / q)
    else ENNReal.ofReal ((1 - p) / (1 - q))
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const
  have hq_ne0 : ENNReal.ofReal q ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have h1q_ne0 : ENNReal.ofReal (1 - q) ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have hwd : bernoulliLaw p = (bernoulliLaw q).withDensity g := by
    ext s hs
    rw [withDensity_apply _ hs]
    rw [← lintegral_indicator hs g]
    unfold bernoulliLaw
    dsimp [g]
    rw [lintegral_add_measure]
    rw [lintegral_smul_measure, lintegral_smul_measure]
    simp only [lintegral_dirac]
    by_cases h1 : (1 : ℝ) ∈ s
    · by_cases h0 : (0 : ℝ) ∈ s
      · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top,
          ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
      · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top]
    · by_cases h0 : (0 : ℝ) ∈ s
      · simp [h1, h0, ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
      · simp [h1, h0]
  have hac : bernoulliLaw p ≪ bernoulliLaw q := by
    rw [hwd]
    exact withDensity_absolutelyContinuous (bernoulliLaw q) g
  have hrn : (bernoulliLaw p).rnDeriv (bernoulliLaw q) =ᵐ[bernoulliLaw q] g := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity (bernoulliLaw q) hg
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun hac]
  trans ∫ x, klFun (g x).toReal ∂(bernoulliLaw q)
  · exact integral_congr_ae <| by
      filter_upwards [hrn] with x hx
      rw [hx]
  rw [bernoulliLaw_integral hq0.le hq1.le]
  dsimp [g]
  have hpq_nonneg : 0 ≤ p / q := div_nonneg hp0 hq0.le
  have hcp_nonneg : 0 ≤ (1 - p) / (1 - q) :=
    div_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1.le)
  simp only [↓reduceIte, zero_ne_one]
  rw [ENNReal.toReal_ofReal hpq_nonneg, ENNReal.toReal_ofReal hcp_nonneg]
  have hqne : q ≠ 0 := hq0.ne'
  have h1qne : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have hA :
      q * klFun (p / q) = p * Real.log (p / q) + q - p := by
    rw [klFun_apply]
    field_simp [hqne]
  have hB :
      (1 - q) * klFun ((1 - p) / (1 - q)) =
        (1 - p) * Real.log ((1 - p) / (1 - q)) +
          (1 - q) - (1 - p) := by
    rw [klFun_apply]
    field_simp [h1qne]
  rw [hA, hB]
  ring

end UEOT.V3.InformationBernoulliKL
