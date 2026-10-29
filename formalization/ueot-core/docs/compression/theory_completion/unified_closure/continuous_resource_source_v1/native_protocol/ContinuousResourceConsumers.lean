import UEOT
namespace ContinuousResourceConsumers
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianMartingaleSource BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralMartingale BrownianIntegralContinuousVersion
open scoped ENNReal NNReal
noncomputable section
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    Martingale (continuousIntegralProcess T f) naturalFiltration sourceLaw :=
  continuousIntegralProcess_martingale T f
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    ∀ᵐ omega ∂sourceLaw, Continuous (fun u => continuousIntegralProcess T f u omega) :=
  continuousIntegralProcess_continuous T f
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    IsStronglyProgressive naturalFiltration (continuousIntegralProcess T f) :=
  continuousIntegralProcess_isStronglyProgressive T f
example (f : fullPredictableL2 0) : continuousIntegralProcess 0 f 0 =ᵐ[sourceLaw] fun _ => 0 :=
  continuousIntegralProcess_zero 0 f
example : (∫ omega, continuousIntegralProcess 1
    (literalPredictableInput (BrownianIntegralClosure.unitInput 1)) 1 omega ^ 2 ∂sourceLaw) = 1 := by
  simpa using continuousIntegralProcess_unit_energy 1
#check RegisterFaultFeedbackResource.returned_positive_funded_actual_infinite
#check RegisterFaultFeedbackResource.closed_finite_reserve_failure
#check RegisterFaultFeedbackResource.closed_not_ae_infinite_viable
#print axioms BrownianIntegralMartingale.integral_projection_identity
#print axioms BrownianIntegralContinuousVersion.continuousIntegralProcess_continuous
#print axioms BrownianIntegralContinuousVersion.continuousIntegralProcess_eq_actual
#print axioms BrownianIntegralContinuousVersion.continuousIntegralProcess_martingale
#print axioms BrownianIntegralContinuousVersion.continuousIntegralProcess_isStronglyProgressive
#print axioms RegisterFaultFeedbackResource.returned_positive_funded_actual_infinite
#print axioms RegisterFaultFeedbackResource.closed_not_ae_infinite_viable
end
end ContinuousResourceConsumers
