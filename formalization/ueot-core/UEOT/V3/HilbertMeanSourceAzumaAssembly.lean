import UEOT.V3.HilbertMeanSourceFirstIncrement
import UEOT.V3.HilbertMeanSourceDoobConditionalMGF
import UEOT.V3.HilbertMeanAzuma
import Mathlib.Tactic

/-!
# P-STAT-06 — source Doob increments into Azuma

This module is the probability-theory convergence point.  The first increment
has the ordinary `1/N²` sub-Gaussian proxy, every later increment has the same
conditional proxy relative to its predecessor prefix filtration, and the whole
increment process is strongly adapted.  Therefore the sum of the first `N`
source Doob increments has the exact frozen tail `exp (-N ε² / 2)`.
-/

namespace UEOT.V3.HilbertMeanSourceAzumaAssembly

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open UEOT.V3.HilbertMeanAzuma
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobCore
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanSourceDoobConditionalMGF
open UEOT.V3.HilbertMeanSourceFirstIncrement

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Exact Azuma tail for the actual source Doob increment sum. -/
theorem source_doob_increment_sum_tail
    [BorelSpace H] [StandardBorelSpace H] [Nonempty H]
    [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi μ).real
      {ω | ε ≤ ∑ k ∈ Finset.range N,
        doobIncrement
          (Measure.pi μ)
          (prefixFiltration (H := H) (N := N))
          (fun x : Fin N → H => ‖empiricalMean x - μH‖)
          k ω}
      ≤ Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  let P : Measure (Fin N → H) := Measure.pi μ
  let ℱ := prefixFiltration (H := H) (N := N)
  let F : (Fin N → H) → ℝ := fun ω => ‖empiricalMean ω - μH‖
  let Y : ℕ → (Fin N → H) → ℝ := doobIncrement P ℱ F
  have hadapt : StronglyAdapted ℱ Y := by
    exact doobIncrement_stronglyAdapted P ℱ F
  have hzero : HasSubgaussianMGF (Y 0) (invSqParam N) P := by
    simpa [P, ℱ, F, Y] using
      hasSubgaussianMGF_doobIncrement_zero_invSqParam
        hN μ μH hμH hunit
  have hstep : ∀ (n : ℕ), n < N - 1 →
      HasCondSubgaussianMGF
        (ℱ n) (ℱ.le n) (Y (n + 1)) (invSqParam N) P := by
    intro n hn
    let j : Fin N := ⟨n + 1, by omega⟩
    have hjpos : 0 < j.1 := by
      dsimp [j]
      omega
    have hs := hasCondSubgaussianMGF_doobIncrement_invSqParam
      hN μ j hjpos μH hμH hunit
    have hjval : j.1 = n + 1 := rfl
    have hpred : j.1 - 1 = n := by
      rw [hjval]
      omega
    simpa [P, ℱ, F, Y, hjval, hpred] using hs
  have htail := azuma_invSqParam_tail
    P N hN hadapt hzero hstep hε
  simpa [P, ℱ, F, Y] using htail

end UEOT.V3.HilbertMeanSourceAzumaAssembly
