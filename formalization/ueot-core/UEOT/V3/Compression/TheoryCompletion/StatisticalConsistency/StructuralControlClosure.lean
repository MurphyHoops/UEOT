import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.ControlEstimatorBridge

/-!
# P3.5 — exact structural/control closure from estimator consistency

P3.4 derives vanishing source structural defects and produces the existing
`FixedSourceApproximation` certificates.  This module performs no new quotient
proof: it feeds those certificates into `StructuralDefectControlLimit` and then
reuses frozen P-QUO-01 consequences.
-/

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.ApproximateHistoryEncoder
open UEOT.V3.Compression.StructuralDefectControlLimit

universe uH uS uA

/-- A consistent realized estimator makes the fixed candidate encoder an exact
control quotient. -/
noncomputable def exactControlQuotient_of_realizedEstimator
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (E : RealizedControlEstimator C micro) :
    ExactControlQuotient H S (fun _ => Act) := by
  apply exactControlQuotient_of_fixedSourceApproximation
    C hC micro (representativeMacroModel C hC micro)
    (fun n => 2 * E.rewardRadius n)
    (fun n => 2 * E.transitionRadius n)
    (fun n => E.toCanonicalFixedSourceApproximation hC n)
  · intro n
    rfl
  · exact E.reward_defect_radius_tendsto_zero
  · exact E.transition_defect_radius_tendsto_zero

/-- Frozen exact-control consequences of the statistically exactified quotient:
exact value descent, exact optimal action-value descent, and exact lifting of a
macro greedy selector against the full causal policy class. -/
theorem p_quo_01_of_realizedEstimator
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (E : RealizedControlEstimator C micro) :
    let Q := exactControlQuotient_of_realizedEstimator C hC micro E
    (∀ h : H, Q.micro.optimalValue h =
        Q.macroModel.optimalValue (Q.f h)) ∧
    (∀ (h : H) (a : Act),
      Q.micro.qValue Q.micro.optimalValue h a =
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f h) a) ∧
    (∀ {t : ℕ} (h : H),
      CausalPolicy.infiniteValue
        (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
        Q.micro (t := t) h = Q.micro.optimalValue h) ∧
    (∀ (π : CausalPolicy H (fun _ => Act)) {t : ℕ} (h : π.Memory t),
      CausalPolicy.infiniteValue π Q.micro h ≤
        Q.micro.optimalValue (π.current h)) := by
  dsimp only
  exact (exactControlQuotient_of_realizedEstimator C hC micro E).p_quo_01

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
