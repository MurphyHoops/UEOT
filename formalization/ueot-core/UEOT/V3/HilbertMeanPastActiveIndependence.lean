import UEOT.V3.HilbertMeanProductBlockIndependence
import UEOT.V3.HilbertMeanDoobBlocks
import UEOT.V3.HilbertMeanIndependentCondDistrib
import Mathlib.Tactic

/-!
# P-STAT-06 — strict-past block versus active coordinate

The final noninitial Doob increment only needs the current scalar coordinate,
not the whole singleton active block.  This module derives direct independence
between the strict-past block projection and the raw active coordinate and
packages the resulting conditional-expectation identity with active law `μ i`.
-/

namespace UEOT.V3.HilbertMeanPastActiveIndependence

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanIndependentCondDistrib

universe uH

variable {H : Type uH} [MeasurableSpace H]

/-- The strict-past block is independent of the raw active coordinate under the
canonical finite product law. -/
theorem past_indep_activeCoordinate
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) :
    IndepFun
      (blockProjection (H := H) (past i))
      (fun ω : Fin N → H => ω i)
      (Measure.pi μ) := by
  let ai : active i := ⟨i, by simp [active]⟩
  have hblocks := disjoint_blocks_indep μ (past i) (active i)
    (past_disjoint_active i)
  have hcomp := IndepFun.comp hblocks measurable_id (measurable_pi_apply ai)
  simpa [Function.comp_def, blockProjection, ai] using hcomp

/-- The raw active coordinate has exactly its source marginal law. -/
theorem activeCoordinate_hasLaw
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) :
    HasLaw (fun ω : Fin N → H => ω i) (μ i) (Measure.pi μ) := by
  exact (measurePreserving_eval μ i).hasLaw

/-- Conditioning an integrable function of strict past and active coordinate on
the strict-past sigma algebra is integration over the original active marginal
`μ i`. -/
theorem condExp_past_active_ae_eq_integral_active
    [StandardBorelSpace H] [Nonempty H]
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N)
    (f : (past i → H) × H → ℝ)
    (hf : StronglyMeasurable f)
    (hf_int : Integrable
      (fun ω : Fin N → H => f (blockProjection (past i) ω, ω i))
      (Measure.pi μ)) :
    (Measure.pi μ)[fun ω : Fin N → H =>
        f (blockProjection (past i) ω, ω i) |
      (inferInstance : MeasurableSpace (past i → H)).comap
        (blockProjection (H := H) (past i))] =ᵐ[Measure.pi μ]
      fun ω => ∫ a, f (blockProjection (past i) ω, a) ∂μ i := by
  letI : IsProbabilityMeasure (blockLaw μ (past i)) :=
    blockLaw_isProbability μ (past i)
  exact condExp_prod_ae_eq_integral_future_of_indep
    (μ := Measure.pi μ)
    (ν := blockLaw μ (past i))
    (ξ := μ i)
    (X := blockProjection (H := H) (past i))
    (Y := fun ω : Fin N → H => ω i)
    (measurable_blockProjection (H := H) (past i))
    (block_hasLaw μ (past i))
    (activeCoordinate_hasLaw μ i)
    (past_indep_activeCoordinate μ i)
    f hf hf_int

end UEOT.V3.HilbertMeanPastActiveIndependence
