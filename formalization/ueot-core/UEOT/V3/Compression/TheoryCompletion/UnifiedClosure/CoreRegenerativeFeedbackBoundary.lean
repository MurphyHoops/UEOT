import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeOneStep
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourceCohortFeedback

/-! Exact finite-population boundaries from two actual independent founder
executions of the same regenerative source.  The higher-growth lineage can be
lost while the lower-growth lineage is still nonzero.  No permanent survival
claim for the latter is made.  Random proportions and normalized expected counts
are calculated separately, including the actual zero-population event. -/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedbackBoundary

open scoped BigOperators
open CoreRegenerativeSource SourceCohortFeedback

def actualCount (theta : Bool) (z : Noise) : ℕ :=
  outputCapital (programStep (programBody theta false false) z)

private theorem count_expect_three (p : Parameters) (theta : Bool) (f : ℕ → ℝ) :
    (∑ z : Noise, noiseWeight p z * f (actualCount theta z)) =
      actualCountProbability p theta false false 0 * f 0 +
      actualCountProbability p theta false false 1 * f 1 +
      actualCountProbability p theta false false 2 * f 2 := by
  simp only [actualCountProbability, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hle : actualCount theta z ≤ 2 := outputCapital_le_two _
  have hcases : actualCount theta z = 0 ∨ actualCount theta z = 1 ∨ actualCount theta z = 2 := by
    omega
  change noiseWeight p z * f (actualCount theta z) =
    noiseWeight p z * (if actualCount theta z = 0 then 1 else 0) * f 0 +
      noiseWeight p z * (if actualCount theta z = 1 then 1 else 0) * f 1 +
      noiseWeight p z * (if actualCount theta z = 2 then 1 else 0) * f 2
  rcases hcases with h | h | h <;> simp [h]

def twoFounderMean (p : Parameters) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ z : Noise × Noise, productWeight (noiseWeight p) (noiseWeight p) z *
    f (actualCount false z.1) (actualCount true z.2)

private theorem twoFounderMean_nine (p : Parameters) (f : ℕ → ℕ → ℝ) :
    twoFounderMean p f =
      actualCountProbability p false false false 0 *
        (actualCountProbability p true false false 0 * f 0 0 +
          actualCountProbability p true false false 1 * f 0 1 +
          actualCountProbability p true false false 2 * f 0 2) +
      actualCountProbability p false false false 1 *
        (actualCountProbability p true false false 0 * f 1 0 +
          actualCountProbability p true false false 1 * f 1 1 +
          actualCountProbability p true false false 2 * f 1 2) +
      actualCountProbability p false false false 2 *
        (actualCountProbability p true false false 0 * f 2 0 +
          actualCountProbability p true false false 1 * f 2 1 +
          actualCountProbability p true false false 2 * f 2 2) := by
  unfold twoFounderMean
  rw [Fintype.sum_prod_type]
  calc
    (∑ z₀ : Noise, ∑ z₁ : Noise,
      productWeight (noiseWeight p) (noiseWeight p) (z₀, z₁) *
        f (actualCount false z₀) (actualCount true z₁)) =
      ∑ z₀ : Noise, noiseWeight p z₀ *
        (∑ z₁ : Noise, noiseWeight p z₁ * f (actualCount false z₀) (actualCount true z₁)) := by
      apply Finset.sum_congr rfl
      intro z₀ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z₁ _
      simp only [productWeight]
      ring
    _ = ∑ z₀ : Noise, noiseWeight p z₀ *
        (actualCountProbability p true false false 0 * f (actualCount false z₀) 0 +
          actualCountProbability p true false false 1 * f (actualCount false z₀) 1 +
          actualCountProbability p true false false 2 * f (actualCount false z₀) 2) := by
      apply Finset.sum_congr rfl
      intro z₀ _
      rw [count_expect_three p true (f (actualCount false z₀))]
    _ = _ := count_expect_three p false (fun a =>
      actualCountProbability p true false false 0 * f a 0 +
        actualCountProbability p true false false 1 * f a 1 +
        actualCountProbability p true false false 2 * f a 2)

theorem concrete_twoFounderMean (f : ℕ → ℕ → ℝ) :
    twoFounderMean concreteParameters f =
      (5/32) * ((9/64) * f 0 0 + (15/32) * f 0 1 + (25/64) * f 0 2) +
      (9/16) * ((9/64) * f 1 0 + (15/32) * f 1 1 + (25/64) * f 1 2) +
      (9/32) * ((9/64) * f 2 0 + (15/32) * f 2 1 + (25/64) * f 2 2) := by
  rw [twoFounderMean_nine,
    (concrete_care_count_law false).1, (concrete_care_count_law false).2.1,
    (concrete_care_count_law false).2.2,
    (concrete_bloom_count_law false).1, (concrete_bloom_count_law false).2.1,
    (concrete_bloom_count_law false).2.2]

theorem twoFounder_event (p : Parameters) (E : ℕ → ℕ → Prop) [DecidableRel E] :
    eventMass (productWeight (noiseWeight p) (noiseWeight p))
      (fun z => E (actualCount false z.1) (actualCount true z.2)) =
      twoFounderMean p (fun a b => if E a b then 1 else 0) := by
  classical
  unfold eventMass twoFounderMean
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : E (actualCount false z.1) (actualCount true z.2) <;> simp [h]

theorem concrete_zero_population :
    eventMass (productWeight (noiseWeight concreteParameters) (noiseWeight concreteParameters))
      (fun z => actualCount false z.1 + actualCount true z.2 = 0) = 45/2048 := by
  rw [twoFounder_event concreteParameters (fun a b => a + b = 0), concrete_twoFounderMean]
  norm_num

theorem concrete_best_extinct_inferior_nonzero :
    eventMass (productWeight (noiseWeight concreteParameters) (noiseWeight concreteParameters))
      (fun z => actualCount true z.2 = 0 ∧ 0 < actualCount false z.1) = 243/2048 := by
  rw [twoFounder_event concreteParameters (fun a b => b = 0 ∧ 0 < a), concrete_twoFounderMean]
  norm_num

/-- Lean's real division makes the ratio zero when both counts are zero.  The
separate theorem above records precisely how much mass this convention covers. -/
theorem concrete_expected_ratio_zero_extension :
    twoFounderMean concreteParameters (fun a b => (b : ℝ) / ((a : ℝ) + b)) = 2095/4096 := by
  rw [concrete_twoFounderMean]
  norm_num

theorem concrete_expected_ratio_given_nonzero :
    twoFounderMean concreteParameters (fun a b => (b : ℝ) / ((a : ℝ) + b)) /
      (1 - eventMass (productWeight (noiseWeight concreteParameters) (noiseWeight concreteParameters))
        (fun z => actualCount false z.1 + actualCount true z.2 = 0)) = 2095/4006 := by
  rw [concrete_expected_ratio_zero_extension, concrete_zero_population]
  norm_num

theorem concrete_ratio_expected_counts :
    twoFounderMean concreteParameters (fun _ b => (b : ℝ)) /
      twoFounderMean concreteParameters (fun a b => (a : ℝ) + b) = 10/19 := by
  rw [concrete_twoFounderMean, concrete_twoFounderMean]
  norm_num

theorem expected_ratio_ne_ratio_expected_counts :
    twoFounderMean concreteParameters (fun a b => (b : ℝ) / ((a : ℝ) + b)) ≠
      twoFounderMean concreteParameters (fun _ b => (b : ℝ)) /
        twoFounderMean concreteParameters (fun a b => (a : ℝ) + b) := by
  rw [concrete_expected_ratio_zero_extension, concrete_ratio_expected_counts]
  norm_num

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedbackBoundary
