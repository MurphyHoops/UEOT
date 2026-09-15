import UEOT.V3.CompositionPathInformation
import UEOT.V3.InformationKernelKLMeasurable
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# P-COMP-01 — kernel-level product reference for path partitions

This file closes the measurability bridge between the source-level conditional
path law and the finite product of its block marginals.

For one common Markov kernel

`κ : Kernel U (∀ i, X i)`

and one actual coordinate partition `blockOf : I → B`, we construct:

* the block marginal kernels;
* the reblocked joint kernel of the same common law;
* the finite product kernel of the block marginals;
* the pointwise identification of those kernels with the measure-level objects
  used in `CompositionPathInformation`;
* measurability of the fiberwise partition KL.

Thus the zero-integral theorem no longer needs an externally supplied
measurability hypothesis.
-/

namespace UEOT.V3.CompositionPathKernelProduct

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal ProbabilityTheory

open UEOT.V3.CompositionPathInformation
open UEOT.V3.InformationKernelKLMeasurable

universe uI uB uX uU

variable {I : Type uI} [Fintype I]
variable {X : I → Type uX}
variable [∀ i, MeasurableSpace (X i)]
variable {B : Type uB} [Fintype B]
variable {U : Type uU} [MeasurableSpace U]

/-- Conditional law of one block, obtained by mapping the one common joint
conditional path kernel through the actual block readout. -/
noncomputable def blockMarginalKernel
    (κ : Kernel U (∀ i, X i))
    (blockOf : I → B) (b : B) :
    Kernel U (BlockPath blockOf X b) :=
  κ.map (blockReadout (X := X) blockOf b)

instance blockMarginalKernel_isMarkov
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B) (b : B) :
    IsMarkovKernel (blockMarginalKernel (X := X) κ blockOf b) := by
  unfold blockMarginalKernel
  exact Kernel.IsMarkovKernel.map κ
    (measurable_blockReadout (X := X) blockOf b)

/-- The reblocked joint conditional law as an honest kernel.  No stochastic law
is changed: only the coordinates of the common path are regrouped. -/
noncomputable def reblockedKernel
    (κ : Kernel U (∀ i, X i))
    (blockOf : I → B) :
    Kernel U (∀ b, BlockPath blockOf X b) :=
  κ.map (reblockPath (X := X) blockOf)

instance reblockedKernel_isMarkov
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B) :
    IsMarkovKernel (reblockedKernel (X := X) κ blockOf) := by
  unfold reblockedKernel
  exact Kernel.IsMarkovKernel.map κ
    (measurable_reblockPath (X := X) blockOf)

/-- Fiber identification for the reblocked kernel. -/
theorem reblockedKernel_apply
    (κ : Kernel U (∀ i, X i))
    (blockOf : I → B) (u : U) :
    reblockedKernel (X := X) κ blockOf u =
      reblockedJointLaw (X := X) (κ u) blockOf := by
  unfold reblockedKernel reblockedJointLaw
  exact Kernel.map_apply κ
    (measurable_reblockPath (X := X) blockOf) u

/-- Fiber identification for each block marginal kernel. -/
theorem blockMarginalKernel_apply
    (κ : Kernel U (∀ i, X i))
    (blockOf : I → B) (b : B) (u : U) :
    blockMarginalKernel (X := X) κ blockOf b u =
      (κ u).map (blockReadout (X := X) blockOf b) := by
  unfold blockMarginalKernel
  exact Kernel.map_apply κ
    (measurable_blockReadout (X := X) blockOf b) u

/-- The block marginal packaged with its probability-measure certificate.
Keeping this dependent codomain explicit prevents Lean from forgetting which
block-path type belongs to each block when `ProbabilityMeasure.pi` is unfolded. -/
noncomputable def blockMarginalProbabilityMeasure
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B) (u : U) (b : B) :
    ProbabilityMeasure (BlockPath blockOf X b) :=
  ⟨blockMarginalKernel (X := X) κ blockOf b u, inferInstance⟩

/-- Finite product of the conditional block marginals, constructed as a
measurable kernel rather than merely pointwise as a family of measures. -/
noncomputable def blockProductKernel
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B) :
    Kernel U (∀ b, BlockPath blockOf X b) where
  toFun u :=
    (ProbabilityMeasure.pi
      (blockMarginalProbabilityMeasure (X := X) κ blockOf u)).toMeasure
  measurable' := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := Set.pi univ ''
        Set.pi univ (fun b =>
          {s : Set (BlockPath blockOf X b) | MeasurableSet s}))
      generateFrom_pi.symm isPiSystem_pi ?_
    rintro _ ⟨C, hC, rfl⟩
    have hCmeas : ∀ b, MeasurableSet (C b) :=
      fun b => hC b (mem_univ b)
    simp_rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
    simpa only [blockMarginalProbabilityMeasure, ProbabilityMeasure.coe_mk] using
      (Finset.measurable_prod Finset.univ fun b _ =>
        Kernel.measurable_coe
          (blockMarginalKernel (X := X) κ blockOf b) (hCmeas b))

instance blockProductKernel_isMarkov
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B) :
    IsMarkovKernel (blockProductKernel (X := X) κ blockOf) := by
  refine ⟨fun u => ?_⟩
  change IsProbabilityMeasure
    ((ProbabilityMeasure.pi
      (blockMarginalProbabilityMeasure (X := X) κ blockOf u)).toMeasure)
  infer_instance

/-- Each fiber of the product kernel is exactly the product of the block
marginals of the same common conditional joint law. -/
theorem blockProductKernel_apply
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B) (u : U) :
    blockProductKernel (X := X) κ blockOf u =
      blockProductLaw (X := X) (κ u) blockOf := by
  change
    (ProbabilityMeasure.pi
      (blockMarginalProbabilityMeasure (X := X) κ blockOf u)).toMeasure =
      blockProductLaw (X := X) (κ u) blockOf
  rw [ProbabilityMeasure.toMeasure_pi]
  unfold blockProductLaw
  congr 1
  funext b
  change blockMarginalKernel (X := X) κ blockOf b u =
    (κ u).map (blockReadout (X := X) blockOf b)
  exact blockMarginalKernel_apply (X := X) κ blockOf b u

/-- Fiberwise source KL is exactly the KL between the reblocked joint kernel
and the finite product kernel. -/
theorem partitionFiberKL_eq_kernelKL
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B) (u : U) :
    partitionFiberKL (X := X) (κ u) blockOf =
      klDiv
        (reblockedKernel (X := X) κ blockOf u)
        (blockProductKernel (X := X) κ blockOf u) := by
  unfold partitionFiberKL
  rw [reblockedKernel_apply (X := X), blockProductKernel_apply (X := X)]

/-- The fiberwise partition KL is measurable whenever the regrouped finite
block-path space is countably generated (or the source is countable). -/
theorem measurable_partitionFiberKL
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B)
    [MeasurableSpace.CountableOrCountablyGenerated U
      (∀ b, BlockPath blockOf X b)] :
    Measurable (fun u => partitionFiberKL (X := X) (κ u) blockOf) := by
  have hKL : Measurable (fun u =>
      klDiv
        (reblockedKernel (X := X) κ blockOf u)
        (blockProductKernel (X := X) κ blockOf u)) :=
    measurable_klDiv_kernel
      (reblockedKernel (X := X) κ blockOf)
      (blockProductKernel (X := X) κ blockOf)
  have hEq :
      (fun u => partitionFiberKL (X := X) (κ u) blockOf) =
        (fun u =>
          klDiv
            (reblockedKernel (X := X) κ blockOf u)
            (blockProductKernel (X := X) κ blockOf u)) := by
    funext u
    exact partitionFiberKL_eq_kernelKL (X := X) κ blockOf u
  rw [hEq]
  exact hKL

/-- The source zero-set statement with no externally supplied measurability
hypothesis. -/
theorem conditionalPartitionInformation_eq_zero_iff
    (ν : Measure U)
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B)
    [MeasurableSpace.CountableOrCountablyGenerated U
      (∀ b, BlockPath blockOf X b)] :
    conditionalPartitionInformation (X := X) ν κ blockOf = 0 ↔
      ConditionallyIndependentBlocks (X := X) ν κ blockOf := by
  exact CompositionPathInformation.conditionalPartitionInformation_eq_zero_iff
    (X := X) ν κ blockOf
    (measurable_partitionFiberKL (X := X) κ blockOf).aemeasurable

end

end UEOT.V3.CompositionPathKernelProduct
