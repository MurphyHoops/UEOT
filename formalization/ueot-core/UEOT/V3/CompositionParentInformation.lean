import UEOT.V3.InformationDeterministicGraph
import UEOT.V3.InformationMemoryBound
import UEOT.V3.InformationRandomEncoderSourceEntropy

/-!
# P-COMP-04 — parent-layer new predictive information

The frozen Core 3 statement conditions on the child canonical cores together
with the interface and uses the minimality consequence of exact sufficiency:
`C_P = g(M_P,U)`.  We package the child-core tuple into an arbitrary finite
side-information type `S`; the canonical map below is deliberately allowed to
use only `(M_P,U)`, not `S`.

The proof is fiberwise.  On every true conditional law of `M_P` given `(S,U)`,
the deterministic graph `(M_P,g(M_P,U))` has mutual information equal to the
Shannon entropy of the image law.  The standard discrete information bound
then gives `H(g(M_P,U)) <= H(M_P)`.  Integrating the genuine conditional
kernels yields the frozen inequality.
-/

namespace UEOT.V3.CompositionParentInformation

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationConditionalStatistic
open UEOT.V3.InformationDeterministicGraph
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationMemoryBound
open UEOT.V3.InformationRandomEncoderSourceEntropy

universe uS uU uM uC

variable {S : Type uS} {U : Type uU} {M : Type uM} {C : Type uC}
variable [MeasurableSpace S] [MeasurableSpace U]
variable [MeasurableSpace M] [MeasurableSpace C]
variable [StandardBorelSpace S] [StandardBorelSpace U]
variable [StandardBorelSpace M] [StandardBorelSpace C]
variable [Fintype M] [Fintype C]
variable [MeasurableSingletonClass M] [MeasurableSingletonClass C]
variable [Nonempty M] [Nonempty C]

/-- The canonical parent core supplied by exact sufficiency/minimality.
The child-core side information `S` is intentionally not an argument of `g`. -/
def parentCoreMap (g : M × U → C) : (S × U) × M → C :=
  fun z => g (z.2, z.1.2)

lemma measurable_parentCoreMap
    (g : M × U → C) (hg : Measurable g) :
    Measurable (parentCoreMap (S := S) g) := by
  unfold parentCoreMap
  exact hg.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

/-- Genuine conditional entropy `H(M_P | S,U)` of the parent representation,
computed by disintegration over the full side-information coordinate. -/
noncomputable def representationConditionalEntropy
    (μ : Measure ((S × U) × M)) [IsProbabilityMeasure μ] : ENNReal :=
  ∫⁻ z, discreteShannonEntropy (μ.condKernel z) ∂μ.fst

/-- A measurable deterministic map cannot increase countable-discrete Shannon
entropy.  This is the one-fiber engine used by P-COMP-04. -/
theorem discreteShannonEntropy_map_le
    (μ : Measure M) [IsProbabilityMeasure μ]
    (f : M → C) (hf : Measurable f) :
    discreteShannonEntropy (μ.map f) ≤ discreteShannonEntropy μ := by
  let ρ : Measure (M × C) := μ.map (deterministicGraph f)
  letI : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_deterministicGraph f hf).aemeasurable).2 inferInstance
  have hinfo :
      mutualInfo ρ = discreteShannonEntropy (μ.map f) := by
    dsimp [ρ]
    exact mutualInfo_deterministicGraph_eq_entropy_map μ f hf
  have hfst : ρ.fst = μ := by
    dsimp [ρ]
    unfold Measure.fst
    rw [Measure.map_map measurable_fst (measurable_deterministicGraph f hf)]
    change μ.map (fun x : M => x) = μ
    exact Measure.map_id'
  calc
    discreteShannonEntropy (μ.map f) = mutualInfo ρ := hinfo.symm
    _ ≤ discreteShannonEntropy ρ.fst :=
      mutualInfo_le_discreteShannonEntropy ρ
    _ = discreteShannonEntropy μ := by rw [hfst]

/-- **P-COMP-04.**  If exact sufficiency/minimality supplies
`C_P = g(M_P,U)`, then conditioning on all child canonical cores and the
interface cannot make the parent representation carry less entropy than the
parent canonical core:

`H(C_P | C_{1:m},U) <= H(M_P | C_{1:m},U)`.

Here `S` packages the finite child-core tuple. -/
theorem p_comp_04
    (μ : Measure ((S × U) × M)) [IsProbabilityMeasure μ]
    (g : M × U → C) (hg : Measurable g) :
    sourceConditionalCoreEntropy μ
        (parentCoreMap (S := S) g)
        (measurable_parentCoreMap (S := S) g hg) ≤
      representationConditionalEntropy μ := by
  unfold sourceConditionalCoreEntropy representationConditionalEntropy
  apply lintegral_mono
  intro z
  letI : IsProbabilityMeasure (μ.condKernel z) := by infer_instance
  exact discreteShannonEntropy_map_le
    (μ.condKernel z)
    (coreAt (parentCoreMap (S := S) g) z)
    (measurable_coreAt
      (parentCoreMap (S := S) g)
      (measurable_parentCoreMap (S := S) g hg) z)

end

end UEOT.V3.CompositionParentInformation
