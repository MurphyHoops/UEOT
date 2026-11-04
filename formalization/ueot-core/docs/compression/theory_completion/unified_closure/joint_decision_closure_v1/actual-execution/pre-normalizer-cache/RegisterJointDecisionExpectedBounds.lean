import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionValueBounds
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionConsumer

/-!
# Expected bounds for the same registered primitive

These lemmas lift the source-specific damaged-state argument to the exact
primitive expansion used by the finite optimizer. They apply to every table,
not merely the proposed small-case table, and retain the original complete
mode/label source without conditioning away failures.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExpectedBounds

open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionExecution
open RegisterJointDecisionValueBounds RegisterJointDecisionConsumer
open FiniteJointDecisionSolver (Table)
open FiniteJointDecisionBelief (Belief expect)
open FiniteJointDecisionFilteredModel (sourceValue)

theorem gain_eq_receipt {Theta : Type} (P : Family Theta) (a : Act) (o : Obs) :
    gain P a o = receiptBirth o - (P.price * P.tariff) * receiptFee o := by
  cases ho : o.2 <;> simp [gain, charge, receiptBirth, receiptFee, ho]

/-- Uniform bound on the exact primitive expectation from any population. -/
theorem source_payoff_le_geometric {Theta : Type} (P : Family Theta) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta),
      sourceValue (source P) (gain P) P.discount table w ≤ geometric P.discount H := by
  intro H
  induction H with
  | zero => intro table w; cases table; rfl
  | succ H ih =>
      intro table w
      cases table with
      | node a children =>
          have hbnd (z : Noise) :
              gain P a (observe P.goal w a z) + P.discount *
                sourceValue (source P) (gain P) P.discount
                  (children (observe P.goal w a z)) (step P.goal w a z) ≤
                geometric P.discount (H+1) := by
            have ht := mul_le_mul_of_nonneg_left
              (ih (children (observe P.goal w a z)) (step P.goal w a z)) P.discount_bounds.1
            have hb := receiptBirth_le_one (observe P.goal w a z)
            have hc := mul_nonneg (mul_nonneg P.price_nonneg P.tariff_pos.le)
              (receiptFee_nonneg (observe P.goal w a z))
            rw [gain_eq_receipt, geometric]
            linarith
          calc
            sourceValue (source P) (gain P) P.discount (.node a children) w ≤
                ∑ z : Noise, primitiveWeight P.normal w z * geometric P.discount (H+1) := by
              apply Finset.sum_le_sum
              intro z hz
              exact mul_le_mul_of_nonneg_left (hbnd z)
                (primitiveWeight_nonneg P.normal P.normal_bounds w z)
            _ = geometric P.discount (H+1) := by
              rw [← Finset.sum_mul, primitiveWeight_sum_one, one_mul]

/-- The high-price no-go for the optimizer's ACTUAL primitive value, at every
finite horizon and for every permitted or even unbudgeted outer table. -/
theorem source_allDamaged_nonpos {Theta : Type} (P : Family Theta) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta),
      AllDamaged P.goal w.store → geometric P.discount H ≤ P.price * P.tariff →
      sourceValue (source P) (gain P) P.discount table w ≤ 0 := by
  intro H
  induction H with
  | zero => intro table w hw hp; cases table; rfl
  | succ H ih =>
      intro table w hw hp
      cases table with
      | node a children =>
          apply Finset.sum_nonpos
          intro z hz
          apply mul_nonpos_of_nonneg_of_nonpos
            (primitiveWeight_nonneg P.normal P.normal_bounds w z)
          let o := observe P.goal w a z
          change gain P a o + P.discount * sourceValue (source P) (gain P) P.discount
            (children o) (step P.goal w a z) ≤ 0
          by_cases hf : feeUnit P.goal w a z = 0
          · have hk := no_fee_preserves_damaged P.goal w a z hw hf
            have ht := ih (children o) (step P.goal w a z) hk.2
              ((geometric_mono P.discount P.discount_bounds.1 H).trans hp)
            have hb : receiptBirth o = 0 := hk.1
            have hc : receiptFee o = 0 := hf
            rw [gain_eq_receipt, hb, hc]
            simpa using mul_nonpos_of_nonneg_of_nonpos P.discount_bounds.1 ht
          · have hc : receiptFee o = 1 := by
              unfold feeUnit at hf
              unfold receiptFee o
              cases ho : (observe P.goal w a z).2 <;> simp_all
            have ht := mul_le_mul_of_nonneg_left
              (source_payoff_le_geometric P (children o) (step P.goal w a z)) P.discount_bounds.1
            have hb := receiptBirth_le_one o
            rw [gain_eq_receipt, hc]
            simp only [geometric] at hp
            linarith

/-- Stopping means the registered remaining root-idle protocol. Its exact
primitive value on a damaged population is zero, with every tick still present. -/
theorem source_stop_zero {Theta : Type} (P : Family Theta) :
    ∀ (H : ℕ) (w : World Theta), AllDamaged P.goal w.store →
      sourceValue (source P) (gain P) P.discount (stopTable H) w = 0 := by
  intro H
  induction H with
  | zero => intros; rfl
  | succ H ih =>
      intro w hw
      change (∑ z : Noise, primitiveWeight P.normal w z *
        (gain P none (observe P.goal w none z) + P.discount *
          sourceValue (source P) (gain P) P.discount (stopTable H) (step P.goal w none z))) = 0
      apply Finset.sum_eq_zero
      intro z hz
      have hf : feeUnit P.goal w none z = 0 := by
        have h := feeUnit_le_cap P.goal w none z
        have hn := feeUnit_nonneg P.goal w none z
        simp [cap, effective] at h
        linarith
      have hk := no_fee_preserves_damaged P.goal w none z hw hf
      have hg : gain P none (observe P.goal w none z) = 0 := by
        rw [gain_eq_receipt,
          show receiptBirth (observe P.goal w none z) = 0 from hk.1,
          show receiptFee (observe P.goal w none z) = 0 from hf]
        ring
      rw [hg, ih (step P.goal w none z) hk.2]
      ring

/-- Averaging over the one public prior cannot overturn the source-specific
no-go. The hypothesis is required only on actual positive-mass hidden atoms. -/
theorem prior_allDamaged_nonpos {Theta : Type} (P : Family Theta)
    {H : ℕ} (table : Table Act Obs H) (b : Belief (World Theta))
    (hb : ∀ x, b.weight x ≠ 0 → AllDamaged P.goal (b.state x).store)
    (hp : geometric P.discount H ≤ P.price * P.tariff) :
    expect b (sourceValue (source P) (gain P) P.discount table) ≤ 0 := by
  apply Finset.sum_nonpos
  intro x hx
  by_cases hz : b.weight x = 0
  · simp [hz]
  · exact mul_nonpos_of_nonneg_of_nonpos (b.nonneg x)
      (source_allDamaged_nonpos P table (b.state x) (hb x hz) hp)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExpectedBounds
