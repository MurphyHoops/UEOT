import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Basic

/-!
# P-COMP-01 — conditional multi-block path integration

The frozen Core 3 source starts from one joint conditional path law
`P_{X_{1:m} | U}` and, for each finite nontrivial partition `π`, merely
regroups the same path coordinates into blocks.  This file keeps that object
identity explicit.

A declared partition is represented by a finite block type `B` and a block
assignment `blockOf : I → B`.  From that assignment we construct the actual
reblocking map

`(∀ i, X i) → ∀ b, (∀ i : {i // blockOf i = b}, X i.1)`.

The map has an explicit inverse, so no new stochastic law is introduced by a
partition.  The partition score is then the KL divergence between the
pushforward of the common joint conditional law under this reblocking and the
product of the corresponding block marginals.

This is intentionally stronger semantically than giving each partition its own
unrelated kernel: all partitions act on one and the same conditional joint path
law, exactly as in the frozen source.
-/

namespace UEOT.V3.CompositionPathInformation

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

universe uI uB uX uU uP

variable {I : Type uI} [Fintype I]
variable {X : I → Type uX}
variable [∀ i, MeasurableSpace (X i)]
variable {B : Type uB} [Fintype B]

/-- Path space carried by one block of a declared coordinate partition. -/
abbrev BlockPath (blockOf : I → B) (X : I → Type uX) (b : B) :=
  (i : {i : I // blockOf i = b}) → X i.1

/-- Read one block from the common full joint path. -/
def blockReadout
    (blockOf : I → B) (b : B) (x : ∀ i, X i) :
    BlockPath blockOf X b :=
  fun i => x i.1

/-- Regroup the common joint path into all blocks of one declared partition. -/
def reblockPath
    (blockOf : I → B) (x : ∀ i, X i) :
    ∀ b, BlockPath blockOf X b :=
  fun b => blockReadout (X := X) blockOf b x

/-- Undo the regrouping by reading each original coordinate from its declared
block. -/
def unReblockPath
    (blockOf : I → B)
    (y : ∀ b, BlockPath blockOf X b) : ∀ i, X i :=
  fun i => y (blockOf i) ⟨i, rfl⟩

/-- Reblocking does not alter the underlying joint path. -/
theorem unReblock_reblock
    (blockOf : I → B) (x : ∀ i, X i) :
    unReblockPath (X := X) blockOf (reblockPath (X := X) blockOf x) = x := by
  funext i
  rfl

/-- Every regrouped block tuple comes from the same original joint path. -/
theorem reblock_unReblock
    (blockOf : I → B)
    (y : ∀ b, BlockPath blockOf X b) :
    reblockPath (X := X) blockOf (unReblockPath (X := X) blockOf y) = y := by
  funext b i
  rcases i with ⟨i, hi⟩
  subst b
  rfl

/-- Each block readout is measurable. -/
theorem measurable_blockReadout
    (blockOf : I → B) (b : B) :
    Measurable (blockReadout (X := X) blockOf b) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply i.1

/-- The full finite regrouping map is measurable. -/
theorem measurable_reblockPath
    (blockOf : I → B) :
    Measurable (reblockPath (X := X) blockOf) := by
  rw [measurable_pi_iff]
  intro b
  exact measurable_blockReadout (X := X) blockOf b

/-- The inverse regrouping map is measurable. -/
theorem measurable_unReblockPath
    (blockOf : I → B) :
    Measurable (unReblockPath (X := X) blockOf) := by
  rw [measurable_pi_iff]
  intro i
  exact (measurable_pi_apply ⟨i, rfl⟩).comp
    (measurable_pi_apply (blockOf i))

/-- Joint law of the same common path after one declared regrouping. -/
noncomputable def reblockedJointLaw
    (μ : Measure (∀ i, X i)) (blockOf : I → B) :
    Measure (∀ b, BlockPath blockOf X b) :=
  μ.map (reblockPath (X := X) blockOf)

instance reblockedJointLaw_isFinite
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (blockOf : I → B) :
    IsFiniteMeasure (reblockedJointLaw (X := X) μ blockOf) := by
  unfold reblockedJointLaw
  infer_instance

/-- Product of the block marginals of the same common joint law. -/
noncomputable def blockProductLaw
    (μ : Measure (∀ i, X i)) (blockOf : I → B) :
    Measure (∀ b, BlockPath blockOf X b) :=
  Measure.pi (fun b => μ.map (blockReadout (X := X) blockOf b))

instance blockProductLaw_isFinite
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (blockOf : I → B) :
    IsFiniteMeasure (blockProductLaw (X := X) μ blockOf) := by
  unfold blockProductLaw
  infer_instance

/-- Fiberwise source score for one actual finite partition of the common path. -/
noncomputable def partitionFiberKL
    (μ : Measure (∀ i, X i)) [IsProbabilityMeasure μ]
    (blockOf : I → B) : ENNReal :=
  klDiv
    (reblockedJointLaw (X := X) μ blockOf)
    (blockProductLaw (X := X) μ blockOf)

/-- The product-law equality for the regrouped common path is exactly indexed
independence of its block readouts under the original joint law. -/
theorem eq_blockProductLaw_iff_iIndep
    (μ : Measure (∀ i, X i)) [IsProbabilityMeasure μ]
    (blockOf : I → B) :
    reblockedJointLaw (X := X) μ blockOf =
        blockProductLaw (X := X) μ blockOf ↔
      iIndepFun (blockReadout (X := X) blockOf) μ := by
  symm
  simpa [reblockedJointLaw, blockProductLaw, reblockPath] using
    (iIndepFun_iff_map_fun_eq_pi_map
      (μ := μ)
      (f := blockReadout (X := X) blockOf)
      (fun b => (measurable_blockReadout (X := X) blockOf b).aemeasurable))

/-- One conditional fiber has zero partition KL exactly when the path blocks of
that declared partition are independent in the common joint law. -/
theorem partitionFiberKL_eq_zero_iff_iIndep
    (μ : Measure (∀ i, X i)) [IsProbabilityMeasure μ]
    (blockOf : I → B) :
    partitionFiberKL (X := X) μ blockOf = 0 ↔
      iIndepFun (blockReadout (X := X) blockOf) μ := by
  unfold partitionFiberKL
  rw [klDiv_eq_zero_iff]
  exact eq_blockProductLaw_iff_iIndep (X := X) μ blockOf

lemma partitionFiberKL_nonneg
    (μ : Measure (∀ i, X i)) [IsProbabilityMeasure μ]
    (blockOf : I → B) :
    0 ≤ partitionFiberKL (X := X) μ blockOf :=
  bot_le

variable {U : Type uU} [MeasurableSpace U]

/-- Frozen-source quantity `I_π`: average conditional KL for one declared
partition of the common conditional joint path law. -/
noncomputable def conditionalPartitionInformation
    (ν : Measure U)
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B) : ENNReal :=
  ∫⁻ u, partitionFiberKL (X := X) (κ u) blockOf ∂ν

/-- Conditional block independence means that, for almost every interface
record `U=u`, the block readouts of the same conditional joint path law are
independent. -/
def ConditionallyIndependentBlocks
    (ν : Measure U)
    (κ : Kernel U (∀ i, X i))
    (blockOf : I → B) : Prop :=
  ∀ᵐ u ∂ν,
    iIndepFun (blockReadout (X := X) blockOf) (κ u)

/-- Conditional KL vanishes exactly for almost-everywhere conditional block
independence.  `hMeas` is the explicit regularity needed to turn zero
`lintegral` into an almost-everywhere zero statement. -/
theorem conditionalPartitionInformation_eq_zero_iff
    (ν : Measure U)
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : I → B)
    (hMeas : AEMeasurable
      (fun u => partitionFiberKL (X := X) (κ u) blockOf) ν) :
    conditionalPartitionInformation (X := X) ν κ blockOf = 0 ↔
      ConditionallyIndependentBlocks (X := X) ν κ blockOf := by
  unfold conditionalPartitionInformation ConditionallyIndependentBlocks
  rw [lintegral_eq_zero_iff' hMeas]
  constructor
  · intro h
    filter_upwards [h] with u hu
    exact (partitionFiberKL_eq_zero_iff_iIndep
      (X := X) (μ := κ u) blockOf).1 hu
  · intro h
    filter_upwards [h] with u hu
    exact (partitionFiberKL_eq_zero_iff_iIndep
      (X := X) (μ := κ u) blockOf).2 hu

variable {P : Type uP} [Fintype P] [Nonempty P]

/-- Finite-family source margin `Σ_path = min_π I_π`. -/
noncomputable def pathIntegrationMargin (Iπ : P → ENNReal) : ENNReal :=
  Finset.univ.inf' Finset.univ_nonempty Iπ

/-- Finite minimum positivity is equivalent to strict positivity of every
partition score. -/
theorem pathIntegrationMargin_pos_iff_all_pos
    (Iπ : P → ENNReal) :
    0 < pathIntegrationMargin Iπ ↔ ∀ π, 0 < Iπ π := by
  unfold pathIntegrationMargin
  rw [Finset.lt_inf'_iff]
  simp

/-- Generic finite-family order step used after the actual source zero-set
characterization has been proved. -/
theorem pathIntegrationMargin_pos_iff_no_factorization
    (Iπ : P → ENNReal)
    (factorizes : P → Prop)
    (hzero : ∀ π, Iπ π = 0 ↔ factorizes π) :
    0 < pathIntegrationMargin Iπ ↔ ∀ π, ¬ factorizes π := by
  rw [pathIntegrationMargin_pos_iff_all_pos]
  constructor
  · intro h π hfac
    exact (ne_of_gt (h π)) ((hzero π).2 hfac)
  · intro h π
    rw [pos_iff_ne_zero]
    intro hI
    exact h π ((hzero π).1 hI)

section DeclaredPartitionFamily

/- `P` indexes the frozen finite family of nontrivial partitions.  Every `π`
partitions the same finite child/path-coordinate type `I`; `BP π` is its block
type and `blockOf π` assigns each common coordinate to exactly one block. -/
variable {BP : P → Type uB} [∀ π, Fintype (BP π)]

/-- **P-COMP-01.**  Start from one common conditional joint path kernel `κ`.
For every declared finite nontrivial partition `π`, regroup that same law by
`blockOf π`, compare it with the product of its block marginals, and average the
fiber KL over `U`.

Then each score is nonnegative, it is zero exactly when that partition's path
blocks are conditionally independent given `U`, and the finite-family minimum
is positive exactly when no declared partition factorizes.

`hSurj` certifies that no declared block is empty; `hNontrivial` certifies that
every declared partition has at least two blocks.  They are retained as source
semantics even though the KL zero-set argument itself does not need them. -/
theorem p_comp_01
    (ν : Measure U)
    (κ : Kernel U (∀ i, X i)) [IsMarkovKernel κ]
    (blockOf : (π : P) → I → BP π)
    (hSurj : ∀ π, Function.Surjective (blockOf π))
    (hNontrivial : ∀ π, 2 ≤ Fintype.card (BP π))
    (hMeas : ∀ π,
      AEMeasurable
        (fun u => partitionFiberKL (X := X) (κ u) (blockOf π)) ν) :
    (∀ π,
      0 ≤ conditionalPartitionInformation (X := X) ν κ (blockOf π)) ∧
    (∀ π,
      conditionalPartitionInformation (X := X) ν κ (blockOf π) = 0 ↔
        ConditionallyIndependentBlocks (X := X) ν κ (blockOf π)) ∧
    (0 < pathIntegrationMargin
        (fun π => conditionalPartitionInformation (X := X) ν κ (blockOf π)) ↔
      ∀ π,
        ¬ ConditionallyIndependentBlocks (X := X) ν κ (blockOf π)) := by
  clear hSurj hNontrivial
  constructor
  · intro π
    exact bot_le
  constructor
  · intro π
    exact conditionalPartitionInformation_eq_zero_iff
      (X := X) ν κ (blockOf π) (hMeas π)
  · apply pathIntegrationMargin_pos_iff_no_factorization
    intro π
    exact conditionalPartitionInformation_eq_zero_iff
      (X := X) ν κ (blockOf π) (hMeas π)

end DeclaredPartitionFamily

end

end UEOT.V3.CompositionPathInformation
