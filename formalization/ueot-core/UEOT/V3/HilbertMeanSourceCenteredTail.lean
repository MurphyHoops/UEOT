import UEOT.V3.HilbertMeanSourceAzumaAssembly
import UEOT.V3.HilbertMeanSourceTerminalDoob
import Mathlib.Tactic

/-!
# P-STAT-06 — centered source Hilbert-mean tail

The Doob increments telescope exactly to the terminal Doob value minus the
unconditional source mean.  The terminal value is the original Hilbert
mean-error statistic almost everywhere.  Transporting the Azuma event through
that a.e. identity gives the source-facing centered concentration inequality.
-/

namespace UEOT.V3.HilbertMeanSourceCenteredTail

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobCore
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanSourceAzumaAssembly
open UEOT.V3.HilbertMeanSourceTerminalDoob

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Exact centered source tail:
`P(F - E F ≥ ε) ≤ exp (-N ε² / 2)`. -/
theorem source_meanError_centered_tail
    [BorelSpace H] [StandardBorelSpace H] [Nonempty H]
    [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real
      {ω | ε ≤
        ‖empiricalMean ω - μH‖ -
          ∫ x, ‖empiricalMean x - μH‖ ∂Measure.pi μ}
      ≤ Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  let P : Measure (Fin N → H) := Measure.pi μ
  let ℱ := prefixFiltration (H := H) (N := N)
  let F : (Fin N → H) → ℝ := fun ω => ‖empiricalMean ω - μH‖
  let Y : ℕ → (Fin N → H) → ℝ := doobIncrement P ℱ F
  let m : ℝ := ∫ x, F x ∂P
  have hterminal :
      doobValue P ℱ F (N - 1) =ᵐ[P] F := by
    simpa [P, ℱ, F] using
      doobValue_last_ae_eq_meanError hN μ μH hμH hunit
  have hevent :
      P {ω | ε ≤ F ω - m} =
        P {ω | ε ≤ ∑ k ∈ Finset.range N, Y k ω} := by
    apply measure_congr
    filter_upwards [hterminal] with ω hterm
    have hsum := sum_doobIncrement_range_succ P ℱ F (N - 1) ω
    have hNsplit : N - 1 + 1 = N := by omega
    have hsum' :
        (∑ k ∈ Finset.range N, Y k ω) =
          doobValue P ℱ F (N - 1) ω - m := by
      simpa [Y, m, hNsplit] using hsum
    change (ε ≤ F ω - m) ↔
      (ε ≤ ∑ k ∈ Finset.range N, Y k ω)
    rw [hsum', hterm]
  have htail := source_doob_increment_sum_tail
    hN μ μH hμH hunit hε
  have hreal :
      P.real {ω | ε ≤ F ω - m} =
        P.real {ω | ε ≤ ∑ k ∈ Finset.range N, Y k ω} := by
    unfold Measure.real
    rw [hevent]
  calc
    (Measure.pi μ).real
        {ω | ε ≤
          ‖empiricalMean ω - μH‖ -
            ∫ x, ‖empiricalMean x - μH‖ ∂Measure.pi μ}
        = P.real {ω | ε ≤ F ω - m} := by
            rfl
    _ = P.real {ω | ε ≤ ∑ k ∈ Finset.range N, Y k ω} := hreal
    _ ≤ Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
      simpa [P, ℱ, F, Y] using htail

end UEOT.V3.HilbertMeanSourceCenteredTail
