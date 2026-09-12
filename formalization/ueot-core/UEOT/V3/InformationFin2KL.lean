import UEOT.V3.InformationBernoulliKL
import UEOT.V3.InformationEventBernoulli
import UEOT.V3.InformationStatistic
import Mathlib.Tactic.FinCases

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

end UEOT.V3.InformationFin2KL
