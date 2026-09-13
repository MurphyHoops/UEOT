import UEOT.V3.InformationMutualInfoSymmetry
import UEOT.V3.InformationRecoverableDiscrete

/-!
# P-INFO-03 — information carried by a deterministic graph

For a source variable `X` and a countable deterministic label `C=f(X)`, the
joint graph law of `(X,C)` carries exactly `H(C)` mutual information.  This is
the fiber identity needed by the canonical `M=C` achievability proof.
-/

namespace UEOT.V3.InformationDeterministicGraph

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationEntropyBound
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationRecoverableDiscrete
open UEOT.V3.InformationMutualInfoSymmetry

universe uX uC

variable {X : Type uX} {C : Type uC}
variable [MeasurableSpace X] [MeasurableSpace C]
variable [StandardBorelSpace X] [Nonempty X]
variable [Countable C] [MeasurableSingletonClass C]

def deterministicGraph (f : X → C) : X → X × C :=
  fun x => (x, f x)

lemma measurable_deterministicGraph
    (f : X → C) (hf : Measurable f) :
    Measurable (deterministicGraph f) :=
  measurable_id.prodMk hf

def deterministicSwapGraph (f : X → C) : X → C × X :=
  fun x => (f x, x)

lemma measurable_deterministicSwapGraph
    (f : X → C) (hf : Measurable f) :
    Measurable (deterministicSwapGraph f) :=
  hf.prodMk measurable_id

theorem deterministicSwapGraph_recoverable
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → C) (hf : Measurable f) :
    (μ.map (deterministicSwapGraph f)).map (decodedCopyMap f) =
      copyJoint (μ.map (deterministicSwapGraph f)).fst := by
  have hg := measurable_deterministicSwapGraph f hf
  rw [Measure.map_map (measurable_decodedCopyMap f hf) hg]
  have hfst :
      (μ.map (deterministicSwapGraph f)).fst = μ.map f := by
    unfold Measure.fst
    rw [Measure.map_map measurable_fst hg]
    rfl
  rw [hfst]
  unfold copyJoint
  have hdup : Measurable (fun c : C => (c, c)) :=
    measurable_id.prodMk measurable_id
  calc
    μ.map (decodedCopyMap f ∘ deterministicSwapGraph f) =
        μ.map (fun x => (f x, f x)) := by
      apply Measure.map_congr
      filter_upwards with x
      rfl
    _ = (μ.map f).map (fun c : C => (c, c)) := by
      symm
      exact Measure.map_map hdup hf

theorem mutualInfo_deterministicGraph_eq_entropy_snd
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → C) (hf : Measurable f) :
    mutualInfo (μ.map (deterministicGraph f)) =
      discreteShannonEntropy (μ.map (deterministicGraph f)).snd := by
  let ρ : Measure (X × C) := μ.map (deterministicGraph f)
  letI : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_deterministicGraph f hf).aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (ρ.map Prod.swap) :=
    (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).2 inferInstance
  have hswap :
      ρ.map Prod.swap = μ.map (deterministicSwapGraph f) := by
    dsimp [ρ]
    rw [Measure.map_map measurable_swap (measurable_deterministicGraph f hf)]
    apply Measure.map_congr
    filter_upwards with x
    rfl
  letI : IsProbabilityMeasure (μ.map (deterministicSwapGraph f)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_deterministicSwapGraph f hf).aemeasurable).2 inferInstance
  have hrec :
      (ρ.map Prod.swap).map (decodedCopyMap f) =
        copyJoint (ρ.map Prod.swap).fst := by
    rw [hswap]
    exact deterministicSwapGraph_recoverable μ f hf
  have hinfo :=
    mutualInfo_eq_discreteShannonEntropy_of_recoverable
      (ρ.map Prod.swap) f hf hrec
  rw [mutualInfo_map_swap ρ, map_swap_fst ρ] at hinfo
  exact hinfo

/-- Deterministic-graph information written directly as the entropy of the
image law `μ.map f`.  This is the form consumed by conditional source entropy. -/
theorem mutualInfo_deterministicGraph_eq_entropy_map
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → C) (hf : Measurable f) :
    mutualInfo (μ.map (deterministicGraph f)) =
      discreteShannonEntropy (μ.map f) := by
  rw [mutualInfo_deterministicGraph_eq_entropy_snd μ f hf]
  congr 1
  unfold Measure.snd
  rw [Measure.map_map measurable_snd (measurable_deterministicGraph f hf)]
  apply Measure.map_congr
  filter_upwards with x
  rfl

end

end UEOT.V3.InformationDeterministicGraph
