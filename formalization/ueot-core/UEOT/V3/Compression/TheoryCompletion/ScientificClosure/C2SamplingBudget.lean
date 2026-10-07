import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Scientific Closure C2 — correlated-sampling budget adapter

The β-mixing concentration theorem is *not* manufactured here.  This file only
records the auditable arithmetic layer used once a sampling theorem supplies an
independent-block tail term and a dependence penalty.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

/-- Registered failure-probability budget for `blocks` separated blocks. -/
structure CorrelatedSamplingBudget where
  blocks : ℕ
  independentFailure : ℝ
  betaAtGap : ℝ
  alpha : ℝ
  independentFailure_nonneg : 0 ≤ independentFailure
  betaAtGap_nonneg : 0 ≤ betaAtGap

namespace CorrelatedSamplingBudget

/-- Standard blocking-shaped arithmetic upper budget:
independent tail + `(m-1) * beta(gap)`. -/
def failureUpper (B : CorrelatedSamplingBudget) : ℝ :=
  B.independentFailure + ((B.blocks - 1 : ℕ) : ℝ) * B.betaAtGap

@[simp] theorem failureUpper_nonneg (B : CorrelatedSamplingBudget) :
    0 ≤ B.failureUpper := by
  unfold failureUpper
  exact add_nonneg B.independentFailure_nonneg
    (mul_nonneg (Nat.cast_nonneg _) B.betaAtGap_nonneg)

/-- Once an external sampling theorem proves failure ≤ `failureUpper`, a
preregistered budget check transfers it to the global alpha bound. -/
theorem failure_le_alpha
    (B : CorrelatedSamplingBudget)
    {actualFailure : ℝ}
    (hsampling : actualFailure ≤ B.failureUpper)
    (hbudget : B.failureUpper ≤ B.alpha) :
    actualFailure ≤ B.alpha :=
  hsampling.trans hbudget

end CorrelatedSamplingBudget

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
