import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCertificate
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataGeneralRoute
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataLiteral
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataJoint

/-! Universal endpoint consumed by the generated certificate. It concerns the
same literal preparation/table and the true source's own conditioned path.
The scalar calibration event is a mathematical condition, never an input bit
read by the selector. Sampling confidence and joint risk are proved separately
by FiniteDataCalibration and FiniteDataJoint. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCertifiedConsumer
open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open FiniteDataSource FiniteDataLiteral FiniteActionCertificateCheck
open scoped BigOperators
noncomputable section

/-- Exact verification of the returned coordinates entails the approximate
path guarantee for that same table, uniformly over true calibrated sources. -/
theorem literal_statistical_certificate
    (p : Param) (hp : Admissible p) (estimate : Param) (he : Admissible estimate)
    (prep : Action → ℚ) (hprep : ValidRow prep)
    (T : ℕ) (hT : 0 < T) (w : Fin T → Unit → Action → ℚ) (hw : ∀ t y, ValidRow (w t y))
    (hpreparation : ∀ a, (prep a : ℝ) = ![0,tilt estimate,1-tilt estimate] a)
    (hweights : ∀ t a, (w t () a : ℝ) = if t.val+1<T then
      ![0,tilt estimate,1-tilt estimate] a else ![0,1/2,1/2] a)
    (hg : Good p estimate (1/250)) :
    tvDist (literalDeployment p hp prep hprep T w hw).toMeasure
      (SameSourceFiniteWindowCheck.actualConditionedPrefix (model p hp) observe baseline initial
        FiniteDataConditioned.safe T 0 (FiniteDataConditioned.source_positive p hp T)).toMeasure ≤
      budget estimate T := by
  rw [literal_deployment_eq_direct p hp estimate he prep hprep T w hw hpreparation hweights]
  exact statistical_actual_conditioned_path p hp estimate he T hT hg

/-- The same guarantee for the projection of the full actual T+1-operation
experiment, including its unfiltered noisy preparation and all action records. -/
theorem full_record_statistical_certificate
    (p : Param) (hp : Admissible p) (estimate : Param) (he : Admissible estimate)
    (prep : Action → ℚ) (hprep : ValidRow prep)
    (T : ℕ) (hT : 0 < T) (w : Fin T → Unit → Action → ℚ) (hw : ∀ t y, ValidRow (w t y))
    (hpreparation : ∀ a, (prep a : ℝ) = ![0,tilt estimate,1-tilt estimate] a)
    (hweights : ∀ t a, (w t () a : ℝ) = if t.val+1<T then
      ![0,tilt estimate,1-tilt estimate] a else ![0,1/2,1/2] a)
    (hg : Good p estimate (1/250)) :
    tvDist ((fullLiteralExperiment p hp prep hprep T w hw).map
      (postPreparationStateWindow T)).toMeasure
      (SameSourceFiniteWindowCheck.actualConditionedPrefix (model p hp) observe baseline initial
        FiniteDataConditioned.safe T 0 (FiniteDataConditioned.source_positive p hp T)).toMeasure ≤
      budget estimate T := by
  rw [full_experiment_window_eq_literal]
  exact literal_statistical_certificate p hp estimate he prep hprep T hT w hw hpreparation hweights hg
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCertifiedConsumer
