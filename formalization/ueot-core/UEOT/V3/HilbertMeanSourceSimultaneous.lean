import UEOT.V3.HilbertMeanUnion
import UEOT.V3.HilbertMeanSourceRadius

/-!
# P-STAT-06 — heterogeneous common-sample simultaneous closure

The final finite-family step is intentionally independent of the Hilbert-space
type used by each channel.  Every channel supplies a real-valued error statistic
on the same raw sample space and an `alpha / L` tail bound at the frozen radius.
The union theorem then yields simultaneous control with total failure at most
`alpha`.
-/

namespace UEOT.V3.HilbertMeanSourceSimultaneous

open MeasureTheory
open UEOT.V3.HilbertMeanUnion
open UEOT.V3.HilbertMeanSourceRadius

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- Exact finite-family closure on one common raw sample space.  Since only the
real error statistic enters here, upstream channels may use different RKHSs. -/
theorem source_simultaneous_exact_radius
    {N L : ℕ} (hL : 0 < L)
    (μ : Measure Ω)
    (alpha : ℝ)
    (err : Fin L → Ω → ℝ)
    (h_each : ∀ j,
      μ.real {ω | pStat06SourceRadius N L alpha ≤ err j ω} ≤
        alpha / (L : ℝ)) :
    μ.real {ω | ∃ j : Fin L, pStat06SourceRadius N L alpha ≤ err j ω} ≤ alpha := by
  have hUnion := measure_exists_bad_le_alpha hL μ
    (fun j : Fin L => {ω | pStat06SourceRadius N L alpha ≤ err j ω}) alpha h_each
  have hset :
      {ω | ∃ j : Fin L, pStat06SourceRadius N L alpha ≤ err j ω} =
        ⋃ j : Fin L, {ω | pStat06SourceRadius N L alpha ≤ err j ω} := by
    ext ω
    simp
  rw [hset]
  exact hUnion

end UEOT.V3.HilbertMeanSourceSimultaneous
