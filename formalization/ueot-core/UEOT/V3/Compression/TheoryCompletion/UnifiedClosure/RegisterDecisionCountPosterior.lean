import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserver
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionBelief

/-!
# Exact count posterior for the registered persistent source

The counts include only modes distinguished by the actual receipt protocol.
Rates may be zero or one and prior weights may vanish.  A zero normalizer has
the original prior as a total off-path default; all source-supported updates
below prove a strictly positive normalizer before using Bayes division.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionCountPosterior

open scoped BigOperators
open RegisterJointDecisionSource RegisterDecisionObserver
open FiniteJointDecisionBelief (Belief)

variable {Theta : Type} [Fintype Theta]

def countWeight (r prior : Theta → ℚ) (s f : ℕ) (theta : Theta) : ℚ :=
  prior theta * r theta ^ s * (1-r theta) ^ f

def normalizer (r prior : Theta → ℚ) (s f : ℕ) : ℚ :=
  ∑ theta, countWeight r prior s f theta

def posteriorWeight (r prior : Theta → ℚ) (s f : ℕ) (theta : Theta) : ℚ :=
  if normalizer r prior s f = 0 then prior theta
  else countWeight r prior s f theta / normalizer r prior s f

def observationMass (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs) : ℚ :=
  ∑ theta, posteriorWeight r prior s f theta * likelihood (r theta) goal q a o

theorem countWeight_nonneg (r prior : Theta → ℚ)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1) (hn : ∀ t, 0 ≤ prior t)
    (s f : ℕ) (theta : Theta) : 0 ≤ countWeight r prior s f theta :=
  mul_nonneg (mul_nonneg (hn theta) (pow_nonneg (hr theta).1 s))
    (pow_nonneg (sub_nonneg.mpr (hr theta).2) f)

theorem normalizer_nonneg (r prior : Theta → ℚ)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1) (hn : ∀ t, 0 ≤ prior t) (s f : ℕ) :
    0 ≤ normalizer r prior s f :=
  Finset.sum_nonneg fun theta _ => countWeight_nonneg r prior hr hn s f theta

@[simp] theorem countWeight_zero_zero (r prior : Theta → ℚ) (theta : Theta) :
    countWeight r prior 0 0 theta = prior theta := by simp [countWeight]

theorem normalizer_zero_zero (r prior : Theta → ℚ) (ht : ∑ theta, prior theta = 1) :
    normalizer r prior 0 0 = 1 := by simp [normalizer, ht]

theorem posterior_nonneg (r prior : Theta → ℚ)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1) (hn : ∀ t, 0 ≤ prior t)
    (s f : ℕ) (theta : Theta) : 0 ≤ posteriorWeight r prior s f theta := by
  unfold posteriorWeight
  split
  · exact hn theta
  · exact div_nonneg (countWeight_nonneg r prior hr hn s f theta)
      (normalizer_nonneg r prior hr hn s f)

theorem posterior_total (r prior : Theta → ℚ)
    (ht : ∑ theta, prior theta = 1) (s f : ℕ) :
    ∑ theta, posteriorWeight r prior s f theta = 1 := by
  by_cases hz : normalizer r prior s f = 0
  · simp [posteriorWeight, hz, ht]
  · simp only [posteriorWeight, if_neg hz]
    rw [← Finset.sum_div]
    exact div_self hz

theorem posterior_zero_zero (r prior : Theta → ℚ)
    (ht : ∑ theta, prior theta = 1) (theta : Theta) :
    posteriorWeight r prior 0 0 theta = prior theta := by
  simp [posteriorWeight, normalizer_zero_zero r prior ht]

theorem prior_zero_remains_zero (r prior : Theta → ℚ) (s f : ℕ) (theta : Theta)
    (hz : prior theta = 0) : posteriorWeight r prior s f theta = 0 := by
  simp [posteriorWeight, countWeight, hz]

def countBelief (r prior : Theta → ℚ)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1) (hn : ∀ t, 0 ≤ prior t)
    (ht : ∑ theta, prior theta = 1) (s f : ℕ) : Belief Theta where
  Atom := Theta
  atoms := inferInstance
  state := id
  weight := posteriorWeight r prior s f
  nonneg := posterior_nonneg r prior hr hn s f
  total := posterior_total r prior ht s f

/-- One actual compatible receipt multiplies the old unnormalized count
weight by its actual marginal source likelihood. -/
theorem countWeight_update (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hc : compatible goal q a o) (theta : Theta) :
    countWeight r prior (s + successIncrement goal q a o)
      (f + failureIncrement goal q a o) theta =
      countWeight r prior s f theta * likelihood (r theta) goal q a o := by
  rw [likelihood_counts, if_pos hc]
  simp only [countWeight, pow_add]
  ring

theorem normalizer_update (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs) (hc : compatible goal q a o) :
    normalizer r prior (s + successIncrement goal q a o) (f + failureIncrement goal q a o) =
      ∑ theta, countWeight r prior s f theta * likelihood (r theta) goal q a o := by
  unfold normalizer
  apply Finset.sum_congr rfl
  intro theta htheta
  exact countWeight_update r prior s f goal q a o hc theta

theorem observationMass_nonneg (r prior : Theta → ℚ)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1) (hn : ∀ t, 0 ≤ prior t)
    (s f : ℕ) (goal : Bool) (q : Local) (a : Act) (o : Obs) :
    0 ≤ observationMass r prior s f goal q a o :=
  Finset.sum_nonneg fun theta _ =>
    mul_nonneg (posterior_nonneg r prior hr hn s f theta)
      (likelihood_nonneg (r theta) (hr theta) goal q a o)

theorem observationMass_total (r prior : Theta → ℚ)
    (ht : ∑ theta, prior theta = 1) (s f : ℕ) (goal : Bool) (q : Local) (a : Act) :
    ∑ o : Obs, observationMass r prior s f goal q a o = 1 := by
  unfold observationMass
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, likelihood_total, mul_one]
  exact posterior_total r prior ht s f

theorem observationMass_compatible (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hm : 0 < observationMass r prior s f goal q a o) : compatible goal q a o := by
  by_contra hc
  have hz : observationMass r prior s f goal q a o = 0 := by
    simp [observationMass, likelihood_counts, hc]
  rw [hz] at hm
  exact lt_irrefl 0 hm

theorem observationMass_ratio (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hz : normalizer r prior s f ≠ 0) (hc : compatible goal q a o) :
    observationMass r prior s f goal q a o =
      normalizer r prior (s + successIncrement goal q a o) (f + failureIncrement goal q a o) /
        normalizer r prior s f := by
  rw [normalizer_update r prior s f goal q a o hc]
  simp only [observationMass, posteriorWeight, if_neg hz, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro theta htheta
  ring

/-- Positive source-supported receipt mass propagates a strictly positive
count denominator. No open-interval rate or positive-prior assumption is used. -/
theorem positive_update (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hz : 0 < normalizer r prior s f)
    (hm : 0 < observationMass r prior s f goal q a o) :
    compatible goal q a o ∧
      0 < normalizer r prior (s + successIncrement goal q a o) (f + failureIncrement goal q a o) := by
  have hc := observationMass_compatible r prior s f goal q a o hm
  refine ⟨hc, ?_⟩
  have he : observationMass r prior s f goal q a o * normalizer r prior s f =
      normalizer r prior (s + successIncrement goal q a o) (f + failureIncrement goal q a o) := by
    rw [observationMass_ratio r prior s f goal q a o (ne_of_gt hz) hc]
    exact div_mul_cancel₀ _ (ne_of_gt hz)
  rw [← he]
  exact mul_pos hm hz

/-- Exact Bayes recursion for each source index, including zero-prior atoms
and endpoint rates; division is used only after positivity has been derived. -/
theorem posterior_update (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hz : 0 < normalizer r prior s f)
    (hm : 0 < observationMass r prior s f goal q a o) (theta : Theta) :
    posteriorWeight r prior (s + successIncrement goal q a o)
      (f + failureIncrement goal q a o) theta =
      posteriorWeight r prior s f theta * likelihood (r theta) goal q a o /
        observationMass r prior s f goal q a o := by
  obtain ⟨hc, hz'⟩ := positive_update r prior s f goal q a o hz hm
  rw [posteriorWeight, if_neg (ne_of_gt hz'),
    countWeight_update r prior s f goal q a o hc theta]
  rw [posteriorWeight, if_neg (ne_of_gt hz),
    observationMass_ratio r prior s f goal q a o (ne_of_gt hz) hc]
  field_simp [ne_of_gt hz, ne_of_gt hz']

theorem posterior_joint_identity (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hz : 0 < normalizer r prior s f)
    (hm : 0 < observationMass r prior s f goal q a o) (theta : Theta) :
    observationMass r prior s f goal q a o *
      posteriorWeight r prior (s + successIncrement goal q a o)
        (f + failureIncrement goal q a o) theta =
      posteriorWeight r prior s f theta * likelihood (r theta) goal q a o := by
  rw [posterior_update r prior s f goal q a o hz hm theta]
  field_simp [ne_of_gt hm]

theorem posterior_test_identity (r prior : Theta → ℚ) (s f : ℕ)
    (goal : Bool) (q : Local) (a : Act) (o : Obs)
    (hz : 0 < normalizer r prior s f)
    (hm : 0 < observationMass r prior s f goal q a o) (test : Theta → ℚ) :
    observationMass r prior s f goal q a o *
      (∑ theta, posteriorWeight r prior (s + successIncrement goal q a o)
        (f + failureIncrement goal q a o) theta * test theta) =
      ∑ theta, posteriorWeight r prior s f theta * likelihood (r theta) goal q a o * test theta := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro theta htheta
  rw [← mul_assoc, posterior_joint_identity r prior s f goal q a o hz hm theta]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionCountPosterior
