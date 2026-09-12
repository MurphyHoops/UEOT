import UEOT.V3.HilbertMeanSourceConditionalMGF
import UEOT.V3.HilbertMeanSourceIncrementIdentification
import UEOT.V3.HilbertMeanPrefixPredecessor
import UEOT.V3.HilbertMeanDoobStatisticBridge
import UEOT.V3.HilbertMeanSourceFiberHoeffding
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# P-STAT-06 — actual noninitial Doob increments are conditionally sub-Gaussian

The probability-theory work has already been completed for the clipped
filtration-native source increment. Here we remove that proof device under the
frozen unit-ball source assumption, identify the resulting raw centered source
increment with the actual Doob increment, and rewrite the strict-past sigma
algebra as the predecessor prefix filtration.
-/

namespace UEOT.V3.HilbertMeanSourceDoobConditionalMGF

open MeasureTheory ProbabilityTheory
open scoped NNReal
open UEOT.V3.HilbertMeanAzuma
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobCore
open UEOT.V3.HilbertMeanDoobStatisticBridge
open UEOT.V3.HilbertMeanPastActiveClippedFiber
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanPrefixPredecessor
open UEOT.V3.HilbertMeanSourceCenteredFiber
open UEOT.V3.HilbertMeanSourceClippedIncrement
open UEOT.V3.HilbertMeanSourceConditionalMGF
open UEOT.V3.HilbertMeanSourceFiberHoeffding
open UEOT.V3.HilbertMeanSourceIncrementIdentification
open UEOT.V3.HilbertMeanSourceRationalMGF
open UEOT.V3.HilbertMeanSplitStatistic
open UEOT.V3.HilbertMeanUnitClip

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The clipped filtration-native source increment agrees almost everywhere
with the raw centered source continuation. -/
theorem sourceClippedIncrement_ae_eq_rawCentered
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    sourceClippedIncrement μ i μH =ᵐ[Measure.pi μ]
      fun ω => sourceContinuation μ i μH ω -
        ∫ a, sourceActiveSection μ i μH ω a ∂μ i := by
  have hall : ∀ᵐ ω ∂Measure.pi μ, ∀ j, ‖ω j‖ ≤ 1 :=
    ae_unit_all_of_marginals μ hunit
  filter_upwards [hall] with ω hω
  have hobs :
      sourceClippedIncrement μ i μH ω =
        centeredClippedActiveSection μ i μH ω (ω i) := by
    exact pastCenteredClippedActiveSection_blockProjection μ i μH ω
  rw [hobs]
  unfold centeredClippedActiveSection
  rw [unitClip_eq_of_norm_le _ (hω i)]
  rw [integral_unitClip_eq (μ i) (sourceActiveSection μ i μH ω) (hunit i)]
  simp [sourceActiveSection]

/-- Every genuine noninitial source Doob increment has the exact conditional
sub-Gaussian proxy `1/N²` relative to its predecessor prefix filtration. -/
theorem hasCondSubgaussianMGF_doobIncrement_invSqParam
    [BorelSpace H] [StandardBorelSpace H] [Nonempty H]
    [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (hi : 0 < i.1)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    HasCondSubgaussianMGF
      (prefixFiltration (H := H) (N := N) (i.1 - 1))
      (by exact (prefixFiltration (H := H) (N := N)).le (i.1 - 1))
      (doobIncrement
        (Measure.pi μ)
        (prefixFiltration (H := H) (N := N))
        (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
        i.1)
      (invSqParam N)
      (Measure.pi μ) := by
  have hclip := hasCondSubgaussianMGF_sourceClippedIncrement_invSqParam
    hN μ i μH hμH hunit
  have hclipraw := sourceClippedIncrement_ae_eq_rawCentered
    μ i μH hunit
  have hdoob := doobIncrement_meanError_ae_eq_centeredActiveSection
    hN μ i hi μH hμH hunit
  have hclipdoob :
      sourceClippedIncrement μ i μH =ᵐ[Measure.pi μ]
        doobIncrement
          (Measure.pi μ)
          (prefixFiltration (H := H) (N := N))
          (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
          i.1 :=
    hclipraw.trans hdoob.symm
  have hsigma := prefixFiltration_pred_eq_pastComap (H := H) i hi
  have hsigma' :
      sourcePastSigma (H := H) i =
        prefixFiltration (H := H) (N := N) (i.1 - 1) := by
    simpa [sourcePastSigma] using hsigma.symm
  rw [hsigma'] at hclip
  exact (ProbabilityTheory.Kernel.HasSubgaussianMGF_congr hclipdoob).mp hclip

end UEOT.V3.HilbertMeanSourceDoobConditionalMGF
