import UEOT.V3.InformationBernoulliKL
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith

/-!
# Event indicator as a Bernoulli information statistic

A measurable event is a deterministic binary statistic.  Pushing a probability
law through its `0/1` indicator gives the Bernoulli law with success parameter
equal to the event probability.  KL data processing therefore lower-bounds the
original KL divergence by the corresponding Bernoulli KL divergence.
-/

namespace UEOT.V3.InformationEventBernoulli

open MeasureTheory InformationTheory
open UEOT.V3.InformationBernoulliKL

universe uX

variable {X : Type uX} [MeasurableSpace X]

noncomputable def eventIndicator (A : Set X) : X → ℝ :=
  fun x => if x ∈ A then 1 else 0

lemma measurable_eventIndicator {A : Set X} (hA : MeasurableSet A) :
    Measurable (eventIndicator A) := by
  unfold eventIndicator
  exact Measurable.ite hA measurable_const measurable_const

/-- The pushforward of a probability law by an event indicator is exactly the
real two-point Bernoulli law with success probability `μ.real A`. -/
theorem map_eventIndicator_eq_bernoulliLaw
    (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Set X) (hA : MeasurableSet A) :
    μ.map (eventIndicator A) = bernoulliLaw (μ.real A) := by
  ext s hs
  rw [Measure.map_apply (measurable_eventIndicator hA) hs]
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  have hcoefA : ENNReal.ofReal (μ.real A) = μ A := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ A)]
  have hrealCompl : 1 - μ.real A = μ.real Aᶜ := by
    have h := probReal_add_probReal_compl (μ := μ) hA
    linarith
  have hcoefAc : ENNReal.ofReal (1 - μ.real A) = μ Aᶜ := by
    rw [hrealCompl, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ Aᶜ)]
  rw [hcoefA, hcoefAc]
  by_cases h1 : (1 : ℝ) ∈ s
  · by_cases h0 : (0 : ℝ) ∈ s
    · have hpre : eventIndicator A ⁻¹' s = Set.univ := by
        ext x
        by_cases hx : x ∈ A <;> simp [eventIndicator, hx, h1, h0]
      rw [hpre]
      simp [Measure.dirac_apply, hs, h1, h0]
    · have hpre : eventIndicator A ⁻¹' s = A := by
        ext x
        by_cases hx : x ∈ A <;> simp [eventIndicator, hx, h1, h0]
      rw [hpre]
      simp [Measure.dirac_apply, hs, h1, h0]
  · by_cases h0 : (0 : ℝ) ∈ s
    · have hpre : eventIndicator A ⁻¹' s = Aᶜ := by
        ext x
        by_cases hx : x ∈ A <;> simp [eventIndicator, hx, h1, h0]
      rw [hpre]
      simp [Measure.dirac_apply, hs, h1, h0]
    · have hpre : eventIndicator A ⁻¹' s = (∅ : Set X) := by
        ext x
        by_cases hx : x ∈ A <;> simp [eventIndicator, hx, h1, h0]
      rw [hpre]
      simp [Measure.dirac_apply, hs, h1, h0]

/-- Event-level KL data processing. -/
theorem bernoulliKL_event_le
    (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    klDiv (bernoulliLaw (μ.real A)) (bernoulliLaw (ν.real A)) ≤
      klDiv μ ν := by
  have h := klDiv_map_le μ ν (measurable_eventIndicator hA)
  rw [map_eventIndicator_eq_bernoulliLaw μ A hA,
    map_eventIndicator_eq_bernoulliLaw ν A hA] at h
  exact h

end UEOT.V3.InformationEventBernoulli
