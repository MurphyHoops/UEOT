import UEOT.V3.HilbertMeanDoobStatisticBridge
import Mathlib.Tactic

/-!
# P-STAT-06 — terminal source Doob value

At the final sample coordinate there is no strict future left to average over.
Consequently the explicit source continuation equals the original Hilbert
mean-error statistic pointwise, and the final Doob value equals that statistic
almost everywhere.
-/

namespace UEOT.V3.HilbertMeanSourceTerminalDoob

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanDoobCore
open UEOT.V3.HilbertMeanDoobStatisticBridge
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanSplitStatistic

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The final valid sample index. -/
def lastIndex {N : ℕ} (hN : 0 < N) : Fin N := ⟨N - 1, by omega⟩

/-- The final sample index has no strict-future coordinates. -/
theorem future_lastIndex_eq_empty {N : ℕ} (hN : 0 < N) :
    future (lastIndex hN) = ∅ := by
  ext j
  simp only [mem_future_iff, Finset.not_mem_empty, iff_false]
  intro hlt
  have hj : j.1 < N := j.2
  change N - 1 < j.1 at hlt
  omega

/-- Every function on the strict-future block of the final coordinate is the
same, since that block is empty. -/
theorem subsingleton_future_lastIndex_fun
    {N : ℕ} (hN : 0 < N) :
    Subsingleton (future (lastIndex hN) → H) := by
  constructor
  intro y z
  funext j
  have hj : (j : Fin N) ∈ future (lastIndex hN) := j.2
  rw [future_lastIndex_eq_empty (H := H) hN] at hj
  exact (Finset.not_mem_empty _ hj).elim

/-- At the final coordinate, the source continuation is exactly the original
Hilbert mean-error statistic: the strict-future integral is an integral of a
constant under a probability law. -/
theorem sourceContinuation_last_eq_meanError
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (ω : Fin N → H) :
    sourceContinuation μ (lastIndex hN) μH ω =
      ‖empiricalMean ω - μH‖ := by
  let i : Fin N := lastIndex hN
  letI : IsProbabilityMeasure (blockLaw μ (future i)) :=
    blockLaw_isProbability μ (future i)
  letI : Subsingleton (future i → H) := by
    simpa [i] using subsingleton_future_lastIndex_fun (H := H) hN
  unfold sourceContinuation
  have hpoint : ∀ y : future i → H,
      splitMeanError i μH
          (blockProjection (prefixBlock (N := N) i.1) ω, y) =
        ‖empiricalMean ω - μH‖ := by
    intro y
    have hy : y = blockProjection (future i) ω := Subsingleton.elim _ _
    rw [hy]
    exact splitMeanError_blockProjections i μH ω
  change (∫ y : future i → H,
      splitMeanError i μH
        (blockProjection (prefixBlock (N := N) i.1) ω, y)
      ∂blockLaw μ (future i)) = ‖empiricalMean ω - μH‖
  simp_rw [hpoint]
  simp

/-- The terminal Doob value is the source statistic itself almost everywhere. -/
theorem doobValue_last_ae_eq_meanError
    [BorelSpace H] [StandardBorelSpace H] [Nonempty H]
    [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1) :
    doobValue
        (Measure.pi μ)
        (prefixFiltration (H := H) (N := N))
        (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
        (N - 1)
      =ᵐ[Measure.pi μ]
      fun ω => ‖empiricalMean ω - μH‖ := by
  let i : Fin N := lastIndex hN
  have hdoob :=
    doobValue_meanError_ae_eq_sourceContinuation_of_unit
      hN μ i μH hμH hunit
  have hival : i.1 = N - 1 := by rfl
  have hdoob' :
      doobValue
          (Measure.pi μ)
          (prefixFiltration (H := H) (N := N))
          (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
          (N - 1)
        =ᵐ[Measure.pi μ]
        sourceContinuation μ i μH := by
    simpa [hival] using hdoob
  refine hdoob'.trans (Filter.Eventually.of_forall ?_)
  intro ω
  simpa [i] using sourceContinuation_last_eq_meanError hN μ μH ω

end UEOT.V3.HilbertMeanSourceTerminalDoob
