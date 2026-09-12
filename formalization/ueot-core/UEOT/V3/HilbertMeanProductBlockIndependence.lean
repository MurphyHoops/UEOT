import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Tactic

/-!
# P-STAT-06 — finite blocks of a canonical product sample

The Doob construction only needs the revealed and unrevealed coordinate blocks
to be independent.  On the canonical product law this is a direct consequence
of coordinate independence.  We isolate that fact here, independently of any
particular prefix/suffix choice.
-/

namespace UEOT.V3.HilbertMeanProductBlockIndependence

open MeasureTheory ProbabilityTheory

universe uι uH

variable {ι : Type uι} {H : Type uH}
variable [Fintype ι] [MeasurableSpace H]

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
      (fun (ω : ι → H) (i : S) => ω i)
      (fun (ω : ι → H) (i : T) => ω i)
      (Measure.pi μ) := by
  apply iIndepFun.indepFun_finset S T hST (coordinate_iIndep μ)
  intro i
  exact measurable_pi_apply i

/-- The pushforward measure of a measurable coordinate block is, by
construction, its law.  Keeping the law abstract at this layer lets the Doob
proof use independence without first normalizing the block into a particular
product-space representation. -/
theorem block_hasLaw
    (μ : ι → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) :
    HasLaw
      (fun (ω : ι → H) (i : S) => ω i)
      ((Measure.pi μ).map (fun (ω : ι → H) (i : S) => ω i))
      (Measure.pi μ) := by
  refine ⟨?_, rfl⟩
  exact (measurable_pi_lambda _ fun i => measurable_pi_apply (i : ι)).aemeasurable

end UEOT.V3.HilbertMeanProductBlockIndependence
