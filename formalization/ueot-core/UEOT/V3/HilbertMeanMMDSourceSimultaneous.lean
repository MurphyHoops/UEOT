import UEOT.V3.HilbertMeanMMDSource
import UEOT.V3.HilbertMeanSourceSimultaneous

/-!
# P-STAT-06 — heterogeneous finite-RKHS simultaneous source theorem

All candidate kernels share one raw iid sample but may have different Hilbert
feature spaces.  The single-channel exact-radius theorem is instantiated in
each RKHS independently; only the resulting real bad events are combined on
the common raw product law.
-/

namespace UEOT.V3.HilbertMeanMMDSourceSimultaneous

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanMMDSource
open UEOT.V3.HilbertMeanSourceRadius
open UEOT.V3.HilbertMeanSourceSimultaneous
open UEOT.V3.MMDTransport

universe uY uH

variable {Y : Type uY} [MeasurableSpace Y]

/-- Frozen P-STAT-06 simultaneous RKHS mean-embedding bound.  Each candidate
`j` may use its own Hilbert space `H j`; all candidates are evaluated on the
same raw iid sample from `P`. -/
theorem source_featureMMD_simultaneous_exact_radius
    {N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (P : Measure Y) [IsProbabilityMeasure P]
    (H : Fin L → Type uH)
    [∀ j, NormedAddCommGroup (H j)]
    [∀ j, InnerProductSpace ℝ (H j)]
    [∀ j, MeasurableSpace (H j)]
    [∀ j, BorelSpace (H j)]
    [∀ j, StandardBorelSpace (H j)]
    [∀ j, CompleteSpace (H j)]
    [∀ j, MeasurableAdd₂ (H j)]
    [∀ j, MeasurableSub (H j)]
    [∀ j, Nonempty (H j)]
    (φ : ∀ j, Y → H j)
    (hφ : ∀ j, Measurable (φ j))
    (hInt : ∀ j, Integrable (φ j) P)
    (hunit : ∀ j, ∀ᵐ y ∂P, ‖φ j y‖ ≤ 1) :
    (Measure.pi (fun _ : Fin N => P)).real
      {y : Fin N → Y |
        ∃ j : Fin L,
          pStat06SourceRadius N L alpha ≤
            ‖empiricalMean (fun i => φ j (y i)) - meanEmbedding (φ j) P‖}
      ≤ alpha := by
  let err : Fin L → (Fin N → Y) → ℝ := fun j y =>
    ‖empiricalMean (fun i => φ j (y i)) - meanEmbedding (φ j) P‖
  apply source_simultaneous_exact_radius
    (N := N) hL (Measure.pi (fun _ : Fin N => P)) alpha err
  intro j
  exact source_featureMMD_tail_exact_radius
    (H := H j) hN hL halpha0 halpha1 P (φ j) (hφ j) (hInt j) (hunit j)

end UEOT.V3.HilbertMeanMMDSourceSimultaneous
