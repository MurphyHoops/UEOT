import UEOT.V3.InformationBernoulliKL
import UEOT.V3.InformationEventBernoulli
import UEOT.V3.InformationStatistic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Exact KL coding for `Fin 2`

This module isolates the finite-binary algebra needed by the conditional
P-INFO-04 bridge.  A `Fin 2` law is encoded by the measurable `0/1` indicator
of the event `{1}`.  The encoding admits a measurable left inverse, so KL is
preserved exactly rather than merely decreased by data processing.
-/

namespace UEOT.V3.InformationFin2KL

open MeasureTheory InformationTheory
open UEOT.V3.InformationBernoulliKL
open UEOT.V3.InformationEventBernoulli
open UEOT.V3.InformationStatistic

/-- Decode the real `0/1` Bernoulli representation back into `Fin 2`.  Values
outside the support are sent to `0`; only the left-inverse property on encoded
bits is needed. -/
noncomputable def realToBit : ℝ → Fin 2 := by
  classical
  exact fun x => if x = 1 then 1 else 0

lemma measurable_realToBit : Measurable realToBit := by
  classical
  unfold realToBit
  exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const

lemma realToBit_leftInverse :
    Function.LeftInverse realToBit
      (eventIndicator ({1} : Set (Fin 2))) := by
  intro b
  fin_cases b <;> simp [realToBit, eventIndicator]

/-- Encoding a binary law by its `0/1` indicator preserves KL exactly. -/
theorem klDiv_fin2_eq_bernoulliLaw
    (μ ν : Measure (Fin 2))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv μ ν =
      klDiv (bernoulliLaw (μ.real ({1} : Set (Fin 2))))
        (bernoulliLaw (ν.real ({1} : Set (Fin 2)))) := by
  have h := klDiv_map_eq_of_measurable_leftInverse
    μ ν
    (eventIndicator ({1} : Set (Fin 2))) realToBit
    (measurable_eventIndicator (measurableSet_singleton (1 : Fin 2)))
    measurable_realToBit realToBit_leftInverse
  rw [map_eventIndicator_eq_bernoulliLaw μ ({1} : Set (Fin 2))
      (measurableSet_singleton (1 : Fin 2)),
    map_eventIndicator_eq_bernoulliLaw ν ({1} : Set (Fin 2))
      (measurableSet_singleton (1 : Fin 2))] at h
  exact h.symm

/-- Interior-reference specialization of binary KL to the exact scalar formula.
The source probability may lie on the boundary; only the reference success
probability is required to be strictly between `0` and `1`. -/
theorem fin2_klDiv_toReal_of_reference_interior
    (μ ν : Measure (Fin 2))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq0 : 0 < ν.real ({1} : Set (Fin 2)))
    (hq1 : ν.real ({1} : Set (Fin 2)) < 1) :
    (klDiv μ ν).toReal =
      μ.real ({1} : Set (Fin 2)) *
          Real.log (μ.real ({1} : Set (Fin 2)) /
            ν.real ({1} : Set (Fin 2))) +
        (1 - μ.real ({1} : Set (Fin 2))) *
          Real.log ((1 - μ.real ({1} : Set (Fin 2))) /
            (1 - ν.real ({1} : Set (Fin 2)))) := by
  rw [klDiv_fin2_eq_bernoulliLaw μ ν]
  exact bernoulliLaw_klDiv_toReal
    measureReal_nonneg measureReal_le_one hq0 hq1

/-- Absolute continuity transfers a zero binary-success probability from the
reference law to the source law. -/
theorem fin2_successProb_eq_zero_of_ac
    (μ ν : Measure (Fin 2))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν)
    (hq0 : ν.real ({1} : Set (Fin 2)) = 0) :
    μ.real ({1} : Set (Fin 2)) = 0 := by
  have hν : ν ({1} : Set (Fin 2)) = 0 := by
    rwa [← measureReal_eq_zero_iff]
  have hμ : μ ({1} : Set (Fin 2)) = 0 := hμν hν
  rwa [measureReal_eq_zero_iff]

/-- Absolute continuity transfers a unit binary-success probability from the
reference law to the source law. -/
theorem fin2_successProb_eq_one_of_ac
    (μ ν : Measure (Fin 2))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν)
    (hq1 : ν.real ({1} : Set (Fin 2)) = 1) :
    μ.real ({1} : Set (Fin 2)) = 1 := by
  have hνc : ν.real ({1} : Set (Fin 2))ᶜ = 0 := by
    rw [probReal_compl_eq_one_sub (measurableSet_singleton (1 : Fin 2)), hq1]
    norm_num
  have hνc' : ν ({1} : Set (Fin 2))ᶜ = 0 := by
    rwa [← measureReal_eq_zero_iff]
  have hμc' : μ ({1} : Set (Fin 2))ᶜ = 0 := hμν hνc'
  have hμc : μ.real ({1} : Set (Fin 2))ᶜ = 0 := by
    rwa [measureReal_eq_zero_iff]
  have hsum := probReal_add_probReal_compl (μ := μ)
    (measurableSet_singleton (1 : Fin 2))
  linarith

/-- If the reference binary law is degenerate at `0`, absolute continuity
forces the source law to have the same Bernoulli parameter, hence KL is zero. -/
theorem fin2_klDiv_eq_zero_of_reference_zero
    (μ ν : Measure (Fin 2))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν)
    (hq0 : ν.real ({1} : Set (Fin 2)) = 0) :
    klDiv μ ν = 0 := by
  have hp0 := fin2_successProb_eq_zero_of_ac μ ν hμν hq0
  rw [klDiv_fin2_eq_bernoulliLaw μ ν, hp0, hq0]
  haveI : IsProbabilityMeasure (bernoulliLaw (0 : ℝ)) :=
    bernoulliLaw_isProbabilityMeasure (by norm_num) (by norm_num)
  exact klDiv_self _

/-- If the reference binary law is degenerate at `1`, absolute continuity
forces the source law to have the same Bernoulli parameter, hence KL is zero. -/
theorem fin2_klDiv_eq_zero_of_reference_one
    (μ ν : Measure (Fin 2))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν)
    (hq1 : ν.real ({1} : Set (Fin 2)) = 1) :
    klDiv μ ν = 0 := by
  have hp1 := fin2_successProb_eq_one_of_ac μ ν hμν hq1
  rw [klDiv_fin2_eq_bernoulliLaw μ ν, hp1, hq1]
  haveI : IsProbabilityMeasure (bernoulliLaw (1 : ℝ)) :=
    bernoulliLaw_isProbabilityMeasure (by norm_num) (by norm_num)
  exact klDiv_self _

/-- **Exact scalar KL formula for arbitrary binary probability laws under
absolute continuity.**  Unlike the interior theorem, this statement covers
both degenerate reference laws `q=0` and `q=1`; no nondegeneracy assumption is
introduced at the source-facing layer. -/
theorem fin2_klDiv_toReal_of_ac
    (μ ν : Measure (Fin 2))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal =
      μ.real ({1} : Set (Fin 2)) *
          Real.log (μ.real ({1} : Set (Fin 2)) /
            ν.real ({1} : Set (Fin 2))) +
        (1 - μ.real ({1} : Set (Fin 2))) *
          Real.log ((1 - μ.real ({1} : Set (Fin 2))) /
            (1 - ν.real ({1} : Set (Fin 2)))) := by
  by_cases hq0 : ν.real ({1} : Set (Fin 2)) = 0
  · have hp0 : μ.real ({1} : Set (Fin 2)) = 0 :=
      fin2_successProb_eq_zero_of_ac μ ν hμν hq0
    have hkl := fin2_klDiv_eq_zero_of_reference_zero μ ν hμν hq0
    rw [hkl, hp0, hq0]
    simp
  · by_cases hq1 : ν.real ({1} : Set (Fin 2)) = 1
    · have hp1 : μ.real ({1} : Set (Fin 2)) = 1 :=
        fin2_successProb_eq_one_of_ac μ ν hμν hq1
      have hkl := fin2_klDiv_eq_zero_of_reference_one μ ν hμν hq1
      rw [hkl, hp1, hq1]
      simp
    · have hq0' : 0 < ν.real ({1} : Set (Fin 2)) :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hq0)
      have hq1' : ν.real ({1} : Set (Fin 2)) < 1 :=
        lt_of_le_of_ne measureReal_le_one hq1
      exact fin2_klDiv_toReal_of_reference_interior μ ν hq0' hq1'

/-- Binary KL is always finite under absolute continuity.  This theorem closes
the `ENNReal` boundary issue needed when converting the fiberwise KL integral
back to an ordinary real integral. -/
theorem fin2_klDiv_ne_top_of_ac
    (μ ν : Measure (Fin 2))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    klDiv μ ν ≠ ∞ := by
  by_cases hq0 : ν.real ({1} : Set (Fin 2)) = 0
  · rw [fin2_klDiv_eq_zero_of_reference_zero μ ν hμν hq0]
    simp
  · by_cases hq1 : ν.real ({1} : Set (Fin 2)) = 1
    · rw [fin2_klDiv_eq_zero_of_reference_one μ ν hμν hq1]
      simp
    · have hp0 : 0 ≤ μ.real ({1} : Set (Fin 2)) := measureReal_nonneg
      have hp1 : μ.real ({1} : Set (Fin 2)) ≤ 1 := measureReal_le_one
      have hq0' : 0 < ν.real ({1} : Set (Fin 2)) :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hq0)
      have hq1' : ν.real ({1} : Set (Fin 2)) < 1 :=
        lt_of_le_of_ne measureReal_le_one hq1
      rw [klDiv_fin2_eq_bernoulliLaw μ ν]
      letI : IsProbabilityMeasure
          (bernoulliLaw (μ.real ({1} : Set (Fin 2)))) :=
        bernoulliLaw_isProbabilityMeasure hp0 hp1
      letI : IsProbabilityMeasure
          (bernoulliLaw (ν.real ({1} : Set (Fin 2)))) :=
        bernoulliLaw_isProbabilityMeasure hq0'.le hq1'.le
      exact InformationTheory.klDiv_ne_top
        (bernoulliLaw_ac_of_reference_interior hq0' hq1')
        bernoulliLaw_llr_integrable

end UEOT.V3.InformationFin2KL
