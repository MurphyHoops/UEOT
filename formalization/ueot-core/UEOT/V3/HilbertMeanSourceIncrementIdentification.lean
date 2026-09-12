import UEOT.V3.HilbertMeanDoobTower
import UEOT.V3.HilbertMeanDoobStatisticBridge
import UEOT.V3.HilbertMeanPrefixPredecessor
import UEOT.V3.HilbertMeanPastActiveContinuation
import UEOT.V3.HilbertMeanPastActiveIndependence
import UEOT.V3.HilbertMeanSourceCenteredFiber

/-!
# P-STAT-06 — source noninitial Doob increment identification

For a genuine noninitial coordinate `i`, the Doob increment is the explicit
future continuation at the observed active coordinate minus the same
continuation averaged over the original active marginal `μ i`, with the strict
past frozen.  This is the exact centered-fiber representation needed by the
conditional Hoeffding layer.
-/

namespace UEOT.V3.HilbertMeanSourceIncrementIdentification

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobCore
open UEOT.V3.HilbertMeanDoobTower
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanPrefixPredecessor
open UEOT.V3.HilbertMeanDoobStatisticBridge
open UEOT.V3.HilbertMeanPastActiveContinuation
open UEOT.V3.HilbertMeanPastActiveIndependence
open UEOT.V3.HilbertMeanSourceCenteredFiber

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Every noninitial source Doob increment is almost everywhere the active
continuation section centered by its `μ i`-average. -/
theorem doobIncrement_meanError_ae_eq_centeredActiveSection
    [BorelSpace H] [StandardBorelSpace H] [Nonempty H]
    [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (hi : 0 < i.1)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1) :
    doobIncrement
        (Measure.pi μ)
        (prefixFiltration (H := H) (N := N))
        (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
        i.1
      =ᵐ[Measure.pi μ]
      fun ω =>
        sourceContinuation μ i μH ω -
          ∫ a, sourceActiveSection μ i μH ω a ∂μ i := by
  let P := Measure.pi μ
  let ℱ := prefixFiltration (H := H) (N := N)
  let F : (Fin N → H) → ℝ := fun ω => ‖empiricalMean ω - μH‖
  let C : (Fin N → H) → ℝ := sourceContinuation μ i μH
  have hsucc : i.1 - 1 + 1 = i.1 := by omega
  have hC :
      doobValue P ℱ F i.1 =ᵐ[P] C := by
    dsimp [P, ℱ, F, C]
    exact doobValue_meanError_ae_eq_sourceContinuation_of_unit
      hN μ i μH hμH hunit
  have hCint : Integrable C P := by
    have hdoob : Integrable (doobValue P ℱ F i.1) P := by
      dsimp [doobValue]
      exact integrable_condExp
    exact hdoob.congr hC
  have hrep :
      (fun ω : Fin N → H =>
        pastActiveContinuation μ i μH (blockProjection (past i) ω, ω i)) = C := by
    funext ω
    dsimp [C]
    exact pastActiveContinuation_blockProjection μ i μH ω
  have hPAint : Integrable
      (fun ω : Fin N → H =>
        pastActiveContinuation μ i μH (blockProjection (past i) ω, ω i)) P := by
    rw [hrep]
    exact hCint
  have hpast := condExp_past_active_ae_eq_integral_active
    (H := H) μ i (pastActiveContinuation μ i μH)
    (stronglyMeasurable_pastActiveContinuation μ i μH) hPAint
  have hsigma := prefixFiltration_pred_eq_pastComap (H := H) i hi
  have hpast' :
      P[C | ℱ (i.1 - 1)] =ᵐ[P]
        fun ω => ∫ a, sourceActiveSection μ i μH ω a ∂μ i := by
    dsimp [P, ℱ, C]
    rw [hsigma]
    rw [hrep] at hpast
    simpa [sourceActiveSection] using hpast
  have hinc :
      doobIncrement P ℱ F i.1 =ᵐ[P]
        fun ω => C ω - P[C | ℱ (i.1 - 1)] ω := by
    have hbase := doobIncrement_succ_ae_eq_explicitCentered
      P ℱ F C (i.1 - 1) (by simpa [hsucc] using hC)
    simpa [hsucc] using hbase
  filter_upwards [hinc, hpast'] with ω hincω hpastω
  dsimp [P, ℱ, F, C] at hincω ⊢
  rw [hincω, hpastω]

end UEOT.V3.HilbertMeanSourceIncrementIdentification
