import UEOTQM.Mixture

/-!
# Exact event characterization of finite record total variation

The distributions are actual normalized finite weights.  Every event difference
is bounded by total variation, and the event where the first probability exceeds
the second attains that bound.  This supplies the sharp passage from actual
quantum record-event effects to a bound on the complete classical record law.
No finite sample of events or sum of singleton error bounds is substituted for
the all-event statement.
-/

namespace UEOTQM.RecordProbability

open scoped BigOperators

noncomputable section

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Probability of an actual finite record event. -/
def eventProbability (p : Mixture.Weights β) (s : Finset β) : ℝ :=
  ∑ b ∈ s, p.weight b

/-- The event attaining the signed variation of two normalized record laws. -/
def positiveEvent (p q : Mixture.Weights β) : Finset β :=
  Finset.univ.filter (fun b => q.weight b ≤ p.weight b)

@[simp] theorem eventProbability_empty (p : Mixture.Weights β) :
    eventProbability p ∅ = 0 := by simp [eventProbability]

@[simp] theorem eventProbability_univ (p : Mixture.Weights β) :
    eventProbability p Finset.univ = 1 := by
  simpa [eventProbability] using p.sum_one

theorem eventProbability_nonneg (p : Mixture.Weights β) (s : Finset β) :
    0 ≤ eventProbability p s := by
  exact Finset.sum_nonneg (fun b _ => p.nonneg b)

theorem eventProbability_le_one (p : Mixture.Weights β) (s : Finset β) :
    eventProbability p s ≤ 1 := by
  calc
    eventProbability p s ≤ ∑ b, p.weight b :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun b _ _ => p.nonneg b)
    _ = 1 := p.sum_one

theorem eventProbability_eq_indicator (p : Mixture.Weights β) (s : Finset β) :
    eventProbability p s = ∑ b, p.weight b * (if b ∈ s then 1 else 0) := by
  simp [eventProbability]

theorem eventProbability_abs_sub_le_tv (p q : Mixture.Weights β) (s : Finset β) :
    |eventProbability p s - eventProbability q s| ≤ Mixture.tv p q := by
  rw [eventProbability_eq_indicator, eventProbability_eq_indicator]
  apply Mixture.expectation_sub_le_tv
  · intro b
    split_ifs <;> norm_num
  · intro b
    split_ifs <;> norm_num

theorem positiveEvent_sub_eq_tv (p q : Mixture.Weights β) :
    eventProbability p (positiveEvent p q) -
      eventProbability q (positiveEvent p q) = Mixture.tv p q := by
  have hzero : (∑ b, (p.weight b - q.weight b)) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_one, q.sum_one, sub_self]
  have hpoint (b : β) : |p.weight b - q.weight b| =
      2 * (if q.weight b ≤ p.weight b then p.weight b - q.weight b else 0) -
        (p.weight b - q.weight b) := by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
      ring
  have hsum : (∑ b, |p.weight b - q.weight b|) =
      2 * ∑ b, (if q.weight b ≤ p.weight b then p.weight b - q.weight b else 0) := by
    calc
      (∑ b, |p.weight b - q.weight b|) =
          ∑ b, (2 * (if q.weight b ≤ p.weight b then p.weight b - q.weight b else 0) -
            (p.weight b - q.weight b)) := Finset.sum_congr rfl (fun b _ => hpoint b)
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, sub_zero]
  have hgap : eventProbability p (positiveEvent p q) -
      eventProbability q (positiveEvent p q) =
        ∑ b, (if q.weight b ≤ p.weight b then p.weight b - q.weight b else 0) := by
    simp only [eventProbability, positiveEvent, ← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> ring
  rw [hgap, Mixture.tv, hsum]
  ring

theorem positiveEvent_abs_sub_eq_tv (p q : Mixture.Weights β) :
    |eventProbability p (positiveEvent p q) -
      eventProbability q (positiveEvent p q)| = Mixture.tv p q := by
  rw [positiveEvent_sub_eq_tv, abs_of_nonneg (Mixture.tv_nonneg p q)]

/-- A bound on every actual event is exactly a bound on the full record TV. -/
theorem tv_le_iff_events (p q : Mixture.Weights β) (ε : ℝ) :
    Mixture.tv p q ≤ ε ↔
      ∀ s : Finset β, |eventProbability p s - eventProbability q s| ≤ ε := by
  constructor
  · intro h s
    exact (eventProbability_abs_sub_le_tv p q s).trans h
  · intro h
    simpa only [positiveEvent_abs_sub_eq_tv] using h (positiveEvent p q)

end

end UEOTQM.RecordProbability
