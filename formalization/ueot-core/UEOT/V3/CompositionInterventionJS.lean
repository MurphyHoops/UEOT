import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic.NormNum

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

lemma midpoint_univ (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    midpoint P Q univ = 1 := by
  simp [midpoint]
  norm_num

lemma midpoint_isProbabilityMeasure (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (midpoint P Q) :=
  ⟨midpoint_univ P Q⟩

@[simp]
lemma midpoint_self (P : Measure X) : midpoint P P = P := by
  ext s hs
  simp [midpoint, Measure.add_apply, hs]
  by_cases h : P s = ∞
  · simp [h]
  · rw [← ENNReal.ofReal_toReal h]
    simp only [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    rw [← ENNReal.ofReal_mul zero_le_two]
    congr
    ring

lemma le_two_smul_midpoint_left (P Q : Measure X) :
    P ≤ (2 : ℝ≥0∞) • midpoint P Q := by
  rw [midpoint, smul_smul]
  norm_num
  exact Measure.le_add_right le_rfl

lemma le_two_smul_midpoint_right (P Q : Measure X) :
    Q ≤ (2 : ℝ≥0∞) • midpoint P Q := by
  rw [midpoint, smul_smul]
  norm_num
  exact Measure.le_add_left le_rfl

lemma absolutelyContinuous_midpoint_left (P Q : Measure X) :
    P ≪ midpoint P Q :=
  Measure.absolutelyContinuous_of_le_smul (le_two_smul_midpoint_left P Q)

lemma absolutelyContinuous_midpoint_right (P Q : Measure X) :
    Q ≪ midpoint P Q :=
  Measure.absolutelyContinuous_of_le_smul (le_two_smul_midpoint_right P Q)

lemma jsDiv_nonneg (P Q : Measure X) : 0 ≤ jsDiv P Q := bot_le

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
