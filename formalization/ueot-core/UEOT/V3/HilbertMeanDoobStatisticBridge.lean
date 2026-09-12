import UEOT.V3.HilbertMeanDoobPrefixBridge
import UEOT.V3.HilbertMeanSplitStatistic

/-!
# P-STAT-06 — explicit Doob continuation for the source Hilbert mean error

This module specializes the generic Doob prefix bridge to the actual source
statistic `‖empiricalMean ω - μH‖`.  The finite block reconstruction is exact,
so the only analytic inputs left explicit here are strong measurability of the
split statistic and integrability of the source statistic under the canonical
product law.
-/

namespace UEOT.V3.HilbertMeanDoobStatisticBridge

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobCore
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanDoobPrefixBridge
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanSplitStatistic

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Source-facing continuation value at sample index `i`: average the Hilbert
mean-error statistic over the unconditional law of the strict future block,
with the revealed prefix held fixed. -/
noncomputable def sourceContinuation {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) : ℝ :=
  ∫ y,
    splitMeanError i μH (blockProjection (prefixBlock i.1) ω, y)
    ∂blockLaw μ (future i)

/-- The source Doob value at time `i` is almost everywhere the explicit future
continuation integral. -/
theorem doobValue_meanError_ae_eq_sourceContinuation
    [StandardBorelSpace H] [Nonempty H]
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H)
    (hsm : StronglyMeasurable (splitMeanError i μH))
    (hint : Integrable
      (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
      (Measure.pi μ)) :
    doobValue
        (Measure.pi μ)
        (prefixFiltration (H := H) (N := N))
        (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
        i.1
      =ᵐ[Measure.pi μ]
      sourceContinuation μ i μH := by
  have hintSplit : Integrable
      (fun (ω : Fin N → H) =>
        splitMeanError i μH
          (blockProjection (prefixBlock i.1) ω, blockProjection (future i) ω))
      (Measure.pi μ) := by
    simpa using hint
  have h := doobValue_prefix_ae_eq_integral
    (H := H) μ i (splitMeanError i μH) hsm hintSplit
  simpa [sourceContinuation] using h

end UEOT.V3.HilbertMeanDoobStatisticBridge
