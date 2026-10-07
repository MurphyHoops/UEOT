/-!
# Scientific Closure C7 — evidence failure attribution

This module formalizes the governance distinction used by the C7 evidence
package.  Only a mathematical/source-semantics mismatch is evidence for reopening
a Core theorem.  Measurement, domain-bridge rejection, and insufficient coverage
remain scientifically important failures but do not logically refute the generic
theorem by themselves.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

/-- Four mutually exclusive first-level failure attributions. -/
inductive FailureClass
  | mathematicsOrSourceSemanticsMismatch
  | measurementOrEstimationAssumptionFailure
  | domainBridgeOrMechanismRejected
  | coverageOrPowerInsufficient
  deriving DecidableEq, Repr

/-- Governance trigger for Core-theorem re-review. -/
def RequiresCoreTheoremReview : FailureClass → Prop
  | .mathematicsOrSourceSemanticsMismatch => True
  | _ => False

@[simp] theorem requiresCoreReview_iff_mathMismatch (f : FailureClass) :
    RequiresCoreTheoremReview f ↔
      f = .mathematicsOrSourceSemanticsMismatch := by
  cases f <;> simp [RequiresCoreTheoremReview]

@[simp] theorem measurementFailure_does_not_requireCoreReview :
    ¬ RequiresCoreTheoremReview
      .measurementOrEstimationAssumptionFailure := by
  simp [RequiresCoreTheoremReview]

@[simp] theorem domainBridgeRejection_does_not_requireCoreReview :
    ¬ RequiresCoreTheoremReview .domainBridgeOrMechanismRejected := by
  simp [RequiresCoreTheoremReview]

@[simp] theorem insufficientCoverage_does_not_requireCoreReview :
    ¬ RequiresCoreTheoremReview .coverageOrPowerInsufficient := by
  simp [RequiresCoreTheoremReview]

/-- Evidence outcomes intentionally retain an unresolved state. -/
inductive EvidenceDisposition
  | supportedLocal
  | rejectedLocal
  | unresolved
  deriving DecidableEq, Repr

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
