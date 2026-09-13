import UEOT.V3.PathEventIProjectionExact
import UEOT.V3.BernoulliKLMonotone

/-!
# P-KL-02 — global event I-projection

This file types the frozen §22.2 minimization literally over every probability
law `Q ≪ P0` with `Q(A) ≥ p`, proves the inactive baseline branch, proves the
active Bernoulli lower bound using P-KL-01 plus one-dimensional monotonicity,
and matches it with the explicit two-region event tilt.
-/

namespace UEOT.V3.PathEventIProjection

noncomputable section

open MeasureTheory InformationTheory
open UEOT.V3.PathEventKL
open UEOT.V3.BernoulliKLMonotone

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- A law feasible for the frozen P-KL-02 constrained optimization problem. -/
structure EventFeasibleLaw (P0 : Measure X) (A : Set X) (p : ℝ) where
  law : Measure X
  isProbability : IsProbabilityMeasure law
  ac : law ≪ P0
  eventLower : p ≤ law.real A

/-- The literal constrained KL infimum from frozen §22.2. -/
noncomputable def eventKLIInf (P0 : Measure X) (A : Set X) (p : ℝ) : ENNReal :=
  ⨅ Q : EventFeasibleLaw P0 A p, klDiv Q.law P0

/-- The baseline law is feasible whenever the constraint is inactive. -/
noncomputable def baselineFeasible
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hpq : p ≤ P0.real A) :
    EventFeasibleLaw P0 A p where
  law := P0
  isProbability := inferInstance
  ac := Measure.AbsolutelyContinuous.rfl
  eventLower := hpq

theorem baselineFeasible_cost_zero
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hpq : p ≤ P0.real A) :
    klDiv (baselineFeasible P0 A p hpq).law P0 = 0 := by
  simp [baselineFeasible]

/-- Frozen inactive branch: the global infimum is zero and is attained by
`P0`. -/
theorem eventKLIInf_eq_zero_of_le_baseline
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hpq : p ≤ P0.real A) :
    eventKLIInf P0 A p = 0 := by
  apply le_antisymm
  · unfold eventKLIInf
    refine iInf_le_of_le (baselineFeasible P0 A p hpq) ?_
    exact (baselineFeasible_cost_zero P0 A p hpq).le
  · exact bot_le

/-- Active-case sharp lower bound for every feasible law. -/
theorem dBern_le_klDiv_of_feasible_active
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1)
    (hqp : P0.real A < p)
    (Q : EventFeasibleLaw P0 A p) :
    dBern p (P0.real A) ≤ klDiv Q.law P0 := by
  letI : IsProbabilityMeasure Q.law := Q.isProbability
  have hmono :
      dBern p (P0.real A) ≤ dBern (Q.law.real A) (P0.real A) :=
    dBern_mono_active hq0 hq1 hqp.le Q.eventLower measureReal_le_one
  exact hmono.trans (p_kl_01 Q.law P0 A hA Q.ac)

theorem dBern_le_eventKLIInf_of_active
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1)
    (hqp : P0.real A < p) :
    dBern p (P0.real A) ≤ eventKLIInf P0 A p := by
  unfold eventKLIInf
  refine le_iInf ?_
  intro Q
  exact dBern_le_klDiv_of_feasible_active P0 A p hA hq0 hq1 hqp Q

/-- The explicit event tilt has event probability exactly `p` in real-valued
measure notation. -/
theorem eventIProjection_real_event
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hq0 : 0 < P0.real A) :
    (eventIProjection P0 A p).real A = p := by
  rw [measureReal_def]
  rw [eventIProjection_apply_event P0 A p hA hp0 hq0]
  rw [ENNReal.toReal_ofReal hp0]

/-- The explicit active I-projection is an element of the literal global
feasible set. -/
noncomputable def activeOptimizerFeasible
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1) :
    EventFeasibleLaw P0 A p where
  law := eventIProjection P0 A p
  isProbability := eventIProjection_isProbability P0 A p hA hp0 hp1 hq0 hq1
  ac := eventIProjection_ac P0 A p
  eventLower := by
    rw [eventIProjection_real_event P0 A p hA hp0 hq0]

/-- Matching upper bound supplied by the explicit optimizer. -/
theorem eventKLIInf_le_dBern_of_active
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1) :
    eventKLIInf P0 A p ≤ dBern p (P0.real A) := by
  unfold eventKLIInf
  refine iInf_le_of_le
    (activeOptimizerFeasible P0 A p hA hp0 hp1 hq0 hq1) ?_
  change klDiv (eventIProjection P0 A p) P0 ≤ dBern p (P0.real A)
  exact (eventIProjection_klDiv_eq_dBern P0 A p hA hp0 hp1 hq0 hq1).le

/-- Frozen active branch: the global constrained infimum is exactly the
Bernoulli event KL and is attained by the explicit two-region tilt. -/
theorem eventKLIInf_eq_dBern_of_active
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1)
    (hqp : P0.real A < p) :
    eventKLIInf P0 A p = dBern p (P0.real A) := by
  apply le_antisymm
  · exact eventKLIInf_le_dBern_of_active P0 A p hA hp0 hp1 hq0 hq1
  · exact dBern_le_eventKLIInf_of_active P0 A p hA hq0 hq1 hqp

/-- Exact piecewise value of the frozen constrained optimization problem. -/
theorem p_kl_02_value
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1) :
    eventKLIInf P0 A p =
      if p ≤ P0.real A then 0 else dBern p (P0.real A) := by
  by_cases hpq : p ≤ P0.real A
  · rw [if_pos hpq]
    exact eventKLIInf_eq_zero_of_le_baseline P0 A p hpq
  · rw [if_neg hpq]
    exact eventKLIInf_eq_dBern_of_active P0 A p hA hp0 hp1 hq0 hq1
      (lt_of_not_ge hpq)

/-- Explicit active optimizer certificate, including the frozen RN density,
probability normalization, exact event mass, and exact KL cost. -/
theorem p_kl_02_active_optimizer
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1)
    (hqp : P0.real A < p) :
    eventKLIInf P0 A p = dBern p (P0.real A) ∧
      IsProbabilityMeasure (eventIProjection P0 A p) ∧
      eventIProjection P0 A p ≪ P0 ∧
      (eventIProjection P0 A p).real A = p ∧
      ((eventIProjection P0 A p).rnDeriv P0 =ᵐ[P0]
        eventTiltDensity P0 A p) ∧
      klDiv (eventIProjection P0 A p) P0 = dBern p (P0.real A) := by
  refine ⟨eventKLIInf_eq_dBern_of_active P0 A p hA hp0 hp1 hq0 hq1 hqp, ?_⟩
  refine ⟨eventIProjection_isProbability P0 A p hA hp0 hp1 hq0 hq1, ?_⟩
  refine ⟨eventIProjection_ac P0 A p, ?_⟩
  refine ⟨eventIProjection_real_event P0 A p hA hp0 hq0, ?_⟩
  refine ⟨eventIProjection_rnDeriv P0 A p hA, ?_⟩
  exact eventIProjection_klDiv_eq_dBern P0 A p hA hp0 hp1 hq0 hq1

/-- Source-facing P-KL-02.  Both frozen branches are exposed together with
attainment: the baseline law in the inactive branch and the exact event tilt in
the active branch. -/
theorem p_kl_02
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1) :
    (p ≤ P0.real A →
      eventKLIInf P0 A p = 0 ∧ klDiv P0 P0 = 0) ∧
    (P0.real A < p →
      eventKLIInf P0 A p = dBern p (P0.real A) ∧
        IsProbabilityMeasure (eventIProjection P0 A p) ∧
        eventIProjection P0 A p ≪ P0 ∧
        (eventIProjection P0 A p).real A = p ∧
        ((eventIProjection P0 A p).rnDeriv P0 =ᵐ[P0]
          eventTiltDensity P0 A p) ∧
        klDiv (eventIProjection P0 A p) P0 = dBern p (P0.real A)) := by
  constructor
  · intro hpq
    refine ⟨eventKLIInf_eq_zero_of_le_baseline P0 A p hpq, ?_⟩
    simpa [baselineFeasible] using baselineFeasible_cost_zero P0 A p hpq
  · intro hqp
    exact p_kl_02_active_optimizer P0 A p hA hp0 hp1 hq0 hq1 hqp

end

end UEOT.V3.PathEventIProjection
