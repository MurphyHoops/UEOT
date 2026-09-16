import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

/-!
# P-COMP-02 — intervention irreducibility via Jensen-Shannon divergence

The frozen Core 3 source compares an original record probability law `P` with
an implementable cut record law `Q = P_cut^π` on the same measurable record
space.  It permits the Jensen-Shannon divergence

`JS(P,Q) = 1/2 KL(P || M) + 1/2 KL(Q || M)`, `M = (P+Q)/2`,

and requires the source-strength facts `0 ≤ JS ≤ log 2`, `JS = 0 ↔ P = Q`,
and the exact finite-cut minimum criterion.

This module deliberately works with general probability measures.  It does not
replace the record laws by a finite/discrete surrogate.
-/

namespace UEOT.V3.CompositionInterventionJS

open MeasureTheory InformationTheory Set
open scoped ENNReal NNReal

universe uX uI

variable {X : Type uX} [MeasurableSpace X]

/-- The actual mixture law `M=(P+Q)/2` from the frozen P-COMP-02 source. -/
noncomputable def midpoint (P Q : Measure X) : Measure X :=
  (2 : ℝ≥0∞)⁻¹ • (P + Q)

/-- Jensen-Shannon divergence in `ℝ≥0∞`, using Mathlib's genuine KL divergence. -/
noncomputable def jsDiv (P Q : Measure X) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * klDiv P (midpoint P Q) +
    (2 : ℝ≥0∞)⁻¹ * klDiv Q (midpoint P Q)

/-- The source-facing `log 2` bound, embedded in `ℝ≥0∞`. -/
noncomputable def logTwo : ℝ≥0∞ := ENNReal.ofReal (Real.log 2)

lemma midpoint_univ (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    midpoint P Q univ = 1 := by
  rw [midpoint, Measure.smul_apply, Measure.add_apply,
    measure_univ, measure_univ, smul_eq_mul, ← two_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

lemma midpoint_isProbabilityMeasure (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (midpoint P Q) :=
  ⟨midpoint_univ P Q⟩

@[simp]
lemma midpoint_self (P : Measure X) : midpoint P P = P := by
  ext s hs
  rw [midpoint, Measure.smul_apply, Measure.add_apply, smul_eq_mul, ← two_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

lemma le_two_smul_midpoint_left (P Q : Measure X) :
    P ≤ (2 : ℝ≥0∞) • midpoint P Q := by
  rw [midpoint, smul_smul,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_smul]
  exact Measure.le_add_right le_rfl

lemma le_two_smul_midpoint_right (P Q : Measure X) :
    Q ≤ (2 : ℝ≥0∞) • midpoint P Q := by
  rw [midpoint, smul_smul,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_smul]
  exact Measure.le_add_left le_rfl

lemma absolutelyContinuous_midpoint_left (P Q : Measure X) :
    P ≪ midpoint P Q :=
  Measure.absolutelyContinuous_of_le_smul (le_two_smul_midpoint_left P Q)

lemma absolutelyContinuous_midpoint_right (P Q : Measure X) :
    Q ≪ midpoint P Q :=
  Measure.absolutelyContinuous_of_le_smul (le_two_smul_midpoint_right P Q)

/-- A real-variable bound used first to establish integrability of the KL
integrand.  It is deliberately coarse; the exact `log 2` bound is proved next. -/
lemma klFun_le_one_of_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    klFun r ≤ 1 := by
  by_cases hr : r = 0
  · subst r
    simp [klFun_apply]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hlog := Real.log_le_sub_one_of_pos hrpos
    have hmul := mul_le_mul_of_nonneg_left hlog hr0
    have hprod : r * (r - 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hr0 (sub_nonpos.mpr hr2)
    rw [klFun_apply]
    nlinarith

/-- Exact secant-line estimate behind the binary Jensen-Shannon bound. -/
lemma klFun_le_logTwo_affine {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    klFun r ≤ r * Real.log 2 + 1 - r := by
  by_cases hr : r = 0
  · subst r
    simp [klFun_apply]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hlog : Real.log r ≤ Real.log 2 := Real.log_le_log hrpos hr2
    have hmul := mul_le_mul_of_nonneg_left hlog hr0
    rw [klFun_apply]
    linarith

/-- If a finite measure is dominated by twice another finite measure, its
Radon--Nikodym derivative is at most two almost everywhere. -/
lemma rnDeriv_le_two_of_le_two_smul (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hle : μ ≤ (2 : ℝ≥0∞) • ν) :
    μ.rnDeriv ν ≤ᵐ[ν] (fun _ => (2 : ℝ≥0∞)) := by
  letI : IsFiniteMeasure ((2 : ℝ≥0∞) • ν) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top ν univ)
  have hhalf := Measure.rnDeriv_le_one_of_le hle
  have hhalf' := hhalf
  rw [Measure.ae_ennreal_smul_measure_eq (by norm_num) ν] at hhalf'
  have hscale :=
    Measure.rnDeriv_smul_right_of_ne_top μ ν (r := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)
  filter_upwards [hhalf', hscale] with x hx hscale_x
  have hx' : (2 : ℝ≥0∞)⁻¹ * μ.rnDeriv ν x ≤ 1 := by
    simpa only [hscale_x, Pi.smul_apply, Pi.one_apply, smul_eq_mul] using hx
  have h := (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).mp hx'
  simpa using h

/-- General-measure KL bound needed for Jensen-Shannon: for probability laws,
`μ ≤ 2ν` implies `KL(μ || ν) ≤ log 2`.

The proof first establishes finiteness using `klFun ≤ 1` on the RN-density
range, then uses the exact affine bound.  This avoids any unsound inference
through `ENNReal.toReal ⊤ = 0`. -/
theorem klDiv_le_logTwo_of_le_two_smul (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hle : μ ≤ (2 : ℝ≥0∞) • ν) :
    klDiv μ ν ≤ logTwo := by
  have h_ac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul hle
  have hRN := rnDeriv_le_two_of_le_two_smul μ ν hle
  have hRNreal :
      (fun x => (μ.rnDeriv ν x).toReal) ≤ᵐ[ν] (fun _ => (2 : ℝ)) := by
    filter_upwards [hRN] with x hx
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hx)
  have h_int_kl :
      Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [hRNreal] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg ENNReal.toReal_nonneg)]
    exact klFun_le_one_of_le_two ENNReal.toReal_nonneg hx
  have h_llr : Integrable (llr μ ν) μ :=
    (integrable_klFun_rnDeriv_iff h_ac).mp h_int_kl
  have hAffine :
      (fun x => klFun (μ.rnDeriv ν x).toReal) ≤ᵐ[ν]
        (fun x => (μ.rnDeriv ν x).toReal * Real.log 2 + 1 -
          (μ.rnDeriv ν x).toReal) := by
    filter_upwards [hRNreal] with x hx
    exact klFun_le_logTwo_affine ENNReal.toReal_nonneg hx
  have h_rn_int : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv
  have h_rhs_int :
      Integrable (fun x => (μ.rnDeriv ν x).toReal * Real.log 2 + 1 -
        (μ.rnDeriv ν x).toReal) ν :=
    ((h_rn_int.mul_const _).add (integrable_const (1 : ℝ))).sub h_rn_int
  have hReal : (klDiv μ ν).toReal ≤ Real.log 2 := by
    rw [toReal_klDiv_eq_integral_klFun h_ac]
    calc
      (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν) ≤
          ∫ x, ((μ.rnDeriv ν x).toReal * Real.log 2 + 1 -
            (μ.rnDeriv ν x).toReal) ∂ν :=
        integral_mono_ae h_int_kl h_rhs_int hAffine
      _ = Real.log 2 := by
        rw [integral_sub
              (f := fun x => (μ.rnDeriv ν x).toReal * Real.log 2 + 1)
              (g := fun x => (μ.rnDeriv ν x).toReal)
              ((h_rn_int.mul_const _).add (integrable_const (1 : ℝ))) h_rn_int,
          integral_add
              (f := fun x => (μ.rnDeriv ν x).toReal * Real.log 2)
              (g := fun _ : X => (1 : ℝ))
              (h_rn_int.mul_const _) (integrable_const (1 : ℝ)),
          integral_mul_const, Measure.integral_toReal_rnDeriv h_ac, integral_const]
        simp
  unfold logTwo
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top h_ac h_llr)]
  exact ENNReal.ofReal_le_ofReal hReal

lemma jsDiv_nonneg (P Q : Measure X) : 0 ≤ jsDiv P Q := bot_le

/-- Universal binary Jensen-Shannon upper bound on the actual record laws. -/
theorem jsDiv_le_logTwo (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    jsDiv P Q ≤ logTwo := by
  letI : IsProbabilityMeasure (midpoint P Q) := midpoint_isProbabilityMeasure P Q
  have hP : klDiv P (midpoint P Q) ≤ logTwo :=
    klDiv_le_logTwo_of_le_two_smul P (midpoint P Q)
      (le_two_smul_midpoint_left P Q)
  have hQ : klDiv Q (midpoint P Q) ≤ logTwo :=
    klDiv_le_logTwo_of_le_two_smul Q (midpoint P Q)
      (le_two_smul_midpoint_right P Q)
  unfold jsDiv
  calc
    (2 : ℝ≥0∞)⁻¹ * klDiv P (midpoint P Q) +
        (2 : ℝ≥0∞)⁻¹ * klDiv Q (midpoint P Q) ≤
      (2 : ℝ≥0∞)⁻¹ * logTwo + (2 : ℝ≥0∞)⁻¹ * logTwo := by
        gcongr
    _ = logTwo := by
      rw [← add_mul]
      have hhalf : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
        rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      rw [hhalf, one_mul]

/-- Source-strength two-sided Jensen-Shannon bound. -/
theorem jsDiv_mem_Icc_logTwo (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    jsDiv P Q ∈ Set.Icc 0 logTwo :=
  ⟨jsDiv_nonneg P Q, jsDiv_le_logTwo P Q⟩

/-- Converse-Gibbs part of P-COMP-02: JS vanishes exactly for equal record laws. -/
theorem jsDiv_eq_zero_iff (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    jsDiv P Q = 0 ↔ P = Q := by
  letI : IsProbabilityMeasure (midpoint P Q) := midpoint_isProbabilityMeasure P Q
  constructor
  · intro h
    have hadd :
        (2 : ℝ≥0∞)⁻¹ * klDiv P (midpoint P Q) = 0 ∧
          (2 : ℝ≥0∞)⁻¹ * klDiv Q (midpoint P Q) = 0 := by
      exact add_eq_zero.mp h
    have hP : klDiv P (midpoint P Q) = 0 := by
      exact (mul_eq_zero.mp hadd.1).resolve_left (by norm_num)
    have hQ : klDiv Q (midpoint P Q) = 0 := by
      exact (mul_eq_zero.mp hadd.2).resolve_left (by norm_num)
    have hPM : P = midpoint P Q := (klDiv_eq_zero_iff.mp hP)
    have hQM : Q = midpoint P Q := (klDiv_eq_zero_iff.mp hQ)
    exact hPM.trans hQM.symm
  · rintro rfl
    simp [jsDiv]

variable {I : Type uI} [Fintype I] [Nonempty I]

/-- Finite declared-cut Jensen-Shannon margin from the source. -/
noncomputable def cutJSMargin (P : Measure X) (Pcut : I → Measure X) : ℝ≥0∞ :=
  Finset.univ.inf' Finset.univ_nonempty (fun π => jsDiv P (Pcut π))

/-- The finite-cut minimum is positive exactly when every declared cut changes
its declared record law.  This is an observational statement only; it does not
assert absence of microscopic coupling when the margin vanishes. -/
theorem cutJSMargin_pos_iff (P : Measure X) (Pcut : I → Measure X)
    [IsProbabilityMeasure P] [∀ π, IsProbabilityMeasure (Pcut π)] :
    0 < cutJSMargin P Pcut ↔ ∀ π, Pcut π ≠ P := by
  constructor
  · intro h π hEq
    have hzero : jsDiv P (Pcut π) = 0 :=
      (jsDiv_eq_zero_iff P (Pcut π)).2 hEq.symm
    have hle : cutJSMargin P Pcut ≤ jsDiv P (Pcut π) := by
      unfold cutJSMargin
      exact Finset.inf'_le _ (Finset.mem_univ π)
    rw [hzero] at hle
    exact (not_lt_of_ge hle) h
  · intro hcuts
    obtain ⟨π0, _hπ0, hmin⟩ :=
      Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
        (fun π => jsDiv P (Pcut π))
    change cutJSMargin P Pcut = jsDiv P (Pcut π0) at hmin
    rw [hmin]
    exact pos_iff_ne_zero.mpr (fun hzero =>
      hcuts π0 ((jsDiv_eq_zero_iff P (Pcut π0)).mp hzero).symm)

end UEOT.V3.CompositionInterventionJS
