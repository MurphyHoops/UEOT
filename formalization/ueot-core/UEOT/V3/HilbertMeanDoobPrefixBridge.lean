import UEOT.V3.HilbertMeanDoobCore
import UEOT.V3.HilbertMeanPrefixFiltration
import Mathlib.Tactic

/-!
# P-STAT-06 — Doob value as an explicit prefix/future continuation integral

This module is the source-facing composition layer between the generic Doob
martingale and the canonical product-space prefix filtration.  For a statistic
factored through the revealed prefix and strict future blocks, the Doob value at
a genuine sample index is almost everywhere the explicit integral over the
unconditional future-block law.
-/

namespace UEOT.V3.HilbertMeanDoobPrefixBridge

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanDoobCore
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanPrefixFiltration

universe uH

variable {H : Type uH} [MeasurableSpace H]

/-- At sample index `i`, the Doob conditional expectation with respect to the
explicit prefix filtration is exactly the future-block continuation integral. -/
theorem doobValue_prefix_ae_eq_integral
    [StandardBorelSpace H] [Nonempty H]
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N)
    (f : (prefixBlock i.1 → H) × (future i → H) → ℝ)
    (hf : StronglyMeasurable f)
    (hf_int : Integrable
      (fun (ω : Fin N → H) =>
        f (blockProjection (prefixBlock i.1) ω, blockProjection (future i) ω))
      (Measure.pi μ)) :
    doobValue
        (Measure.pi μ)
        (prefixFiltration (H := H) (N := N))
        (fun (ω : Fin N → H) =>
          f (blockProjection (prefixBlock i.1) ω, blockProjection (future i) ω))
        i.1
      =ᵐ[Measure.pi μ]
      fun ω => ∫ y,
        f (blockProjection (prefixBlock i.1) ω, y) ∂blockLaw μ (future i) := by
  simpa [doobValue] using
    (condExp_prefix_future_ae_eq_integral
      (H := H) μ i f hf hf_int)

end UEOT.V3.HilbertMeanDoobPrefixBridge
