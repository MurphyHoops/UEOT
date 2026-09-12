import UEOT.V3.HilbertMeanIndependentCondDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Tactic

/-!
# P-STAT-06 — finite blocks of a canonical product sample

The Doob construction only needs the revealed and unrevealed coordinate blocks
to be independent. On the canonical product law this is a direct consequence
of coordinate independence. We also package the pushforward laws of finite
blocks and identify conditional expectations with explicit integration over an
independent future-block law.
-/

namespace UEOT.V3.HilbertMeanProductBlockIndependence

open MeasureTheory ProbabilityTheory

universe uι uH

variable {ι : Type uι} {H : Type uH}
variable [Fintype ι] [MeasurableSpace H]

/-- Projection of a full product sample onto a finite coordinate block. -/
def blockProjection (S : Finset ι) : (ι → H) → (S → H) :=
  fun ω i => ω (i : ι)

/-- Finite block projection is measurable. -/
theorem measurable_blockProjection (S : Finset ι) :
    Measurable (blockProjection (H := H) S) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (i : ι)

/-- The canonical coordinate projections are mutually independent under the
finite product law. -/
theorem coordinate_iIndep
    (μ : ι → Measure H) [∀ i, IsProbabilityMeasure (μ i)] :
    iIndepFun (fun i (ω : ι → H) => ω i) (Measure.pi μ) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- Any two disjoint finite coordinate blocks of a canonical product sample are
independent as vector-valued random variables. -/
theorem disjoint_blocks_indep
    (μ : ι → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun
      (blockProjection (H := H) S)
      (blockProjection (H := H) T)
      (Measure.pi μ) := by
  apply iIndepFun.indepFun_finset S T hST (coordinate_iIndep μ)
  intro i
  exact measurable_pi_apply i

/-- Pushforward law of a finite coordinate block. -/
noncomputable def blockLaw
    (μ : ι → Measure H) (S : Finset ι) : Measure (S → H) :=
  (Measure.pi μ).map (blockProjection (H := H) S)

/-- The block projection has its pushforward law by construction. -/
theorem block_hasLaw
    (μ : ι → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) :
    HasLaw
      (blockProjection (H := H) S)
      (blockLaw μ S)
      (Measure.pi μ) := by
  exact ⟨(measurable_blockProjection (H := H) S).aemeasurable, rfl⟩

/-- A finite coordinate-block law is again a probability measure. -/
theorem blockLaw_isProbability
    (μ : ι → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) :
    IsProbabilityMeasure (blockLaw μ S) := by
  apply Measure.isProbabilityMeasure_map
  exact (measurable_blockProjection (H := H) S).aemeasurable

/-- For two disjoint canonical coordinate blocks, conditioning an integrable
function of both blocks on the first block is exactly integration over the
unconditional law of the second block. This is the abstract past/future bridge
used by the Doob construction. -/
theorem condExp_blocks_ae_eq_integral_second
    [StandardBorelSpace H] [Nonempty H]
    (μ : ι → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (S T : Finset ι) (hST : Disjoint S T)
    (f : (S → H) × (T → H) → ℝ)
    (hf : StronglyMeasurable f)
    (hf_int : Integrable
      (fun (ω : ι → H) =>
        f (blockProjection S ω, blockProjection T ω))
      (Measure.pi μ)) :
    (Measure.pi μ)[fun (ω : ι → H) =>
        f (blockProjection S ω, blockProjection T ω) |
      (inferInstance : MeasurableSpace (S → H)).comap
        (blockProjection (H := H) S)] =ᵐ[Measure.pi μ]
      fun ω => ∫ y, f (blockProjection S ω, y) ∂blockLaw μ T := by
  letI : IsProbabilityMeasure (blockLaw μ S) := blockLaw_isProbability μ S
  letI : IsProbabilityMeasure (blockLaw μ T) := blockLaw_isProbability μ T
  exact UEOT.V3.HilbertMeanIndependentCondDistrib.condExp_prod_ae_eq_integral_future_of_indep
    (μ := Measure.pi μ)
    (ν := blockLaw μ S)
    (ξ := blockLaw μ T)
    (X := blockProjection (H := H) S)
    (Y := blockProjection (H := H) T)
    (measurable_blockProjection (H := H) S)
    (block_hasLaw μ S)
    (block_hasLaw μ T)
    (disjoint_blocks_indep μ S T hST)
    f hf hf_int

end UEOT.V3.HilbertMeanProductBlockIndependence
