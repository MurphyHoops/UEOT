import UEOT.V3.CompositionPathKernelProduct
import UEOT.V3.CompositionFinitePartitions
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# P-COMP-01 — source-facing conditional path irreducibility

This module is the frozen-source bridge for P-COMP-01.

The source does not start from an arbitrary pair `(ν, κ)`: it starts from one
joint law of the external interface record and all child paths, and then uses
the conditional law `P_{X_{1:m} | U}` of that same joint law for every
partition.  We therefore take a single probability law

`ρ : Measure (U × (∀ i, X i))`

and use Mathlib's canonical regular conditional kernel `ρ.condKernel`.
The theorem `sourceConditionalPathLaw_disintegrates` records the machine-checked
bridge

`ρ.fst ⊗ₘ ρ.condKernel = ρ`.

For each actual finite set partition `π` of the child index set, the score is
then exactly the conditional KL between the reblocked common joint path law and
the product of its block marginals.  The final margin is the minimum over the
complete finite set of all nontrivial partitions, not over a caller-selected
subfamily.

`StandardBorelSpace` and nonemptiness are the regular-conditional-probability
infrastructure required by the pinned Mathlib construction.  They are not new
UEOT physical assumptions; the frozen Core explicitly treats existence of
regular conditional probabilities on standard Borel spaces as a standard
mathematical dependency.
-/

namespace UEOT.V3.CompositionPathSource

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

open UEOT.V3.CompositionPathInformation
open UEOT.V3.CompositionPathKernelProduct
open UEOT.V3.CompositionFinitePartitions

universe uI uX uU

variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {X : I → Type uX}
variable [∀ i, MeasurableSpace (X i)]
variable [∀ i, StandardBorelSpace (X i)]
variable {U : Type uU} [MeasurableSpace U]
variable [Nonempty (∀ i, X i)]

/-- The canonical conditional joint child-path law really disintegrates the
same joint source law.  This is the explicit source-object bridge that rules
out unrelated per-partition kernels. -/
theorem sourceConditionalPathLaw_disintegrates
    (ρ : Measure (U × (∀ i, X i))) [IsProbabilityMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ := by
  exact ρ.disintegrate ρ.condKernel

/-- Mathlib's canonical conditional path law carries the corresponding
`IsCondKernel` certificate for the source joint law. -/
theorem sourceConditionalPathLaw_isCondKernel
    (ρ : Measure (U × (∀ i, X i))) [IsProbabilityMeasure ρ] :
    ρ.IsCondKernel ρ.condKernel := by
  infer_instance

/-- Mathlib's canonical conditional path law is a Markov kernel. -/
theorem sourceConditionalPathLaw_isMarkov
    (ρ : Measure (U × (∀ i, X i))) [IsProbabilityMeasure ρ] :
    IsMarkovKernel ρ.condKernel := by
  infer_instance

/-- Frozen-source quantity `I_π`, now derived from one real joint law `ρ` and
its canonical conditional path law. -/
noncomputable def sourcePartitionInformation
    (ρ : Measure (U × (∀ i, X i))) [IsProbabilityMeasure ρ]
    (π : ChildPartition I) : ENNReal :=
  conditionalPartitionInformation
    (X := X) ρ.fst ρ.condKernel (partitionBlockOf π)

/-- The frozen path-factorization predicate for one actual partition: its path
blocks are independent conditional on `U` under the conditional law of the
same source joint distribution. -/
def SourcePathFactorizes
    (ρ : Measure (U × (∀ i, X i))) [IsProbabilityMeasure ρ]
    (π : ChildPartition I) : Prop :=
  ConditionallyIndependentBlocks
    (X := X) ρ.fst ρ.condKernel (partitionBlockOf π)

/-- Exact frozen-source margin over the complete finite family of all
nontrivial partitions. -/
noncomputable def sourcePathIntegrationMargin
    (ρ : Measure (U × (∀ i, X i))) [IsProbabilityMeasure ρ]
    (hI : 2 ≤ Fintype.card I) : ENNReal :=
  exactPathIntegrationMargin hI
    (fun π => sourcePartitionInformation (X := X) ρ π)

/-- For every actual child partition, the frozen-source score vanishes exactly
when its path blocks are conditionally independent given the external
interface record. -/
theorem sourcePartitionInformation_eq_zero_iff
    (ρ : Measure (U × (∀ i, X i))) [IsProbabilityMeasure ρ]
    (π : ChildPartition I) :
    sourcePartitionInformation (X := X) ρ π = 0 ↔
      SourcePathFactorizes (X := X) ρ π := by
  exact
    CompositionPathKernelProduct.conditionalPartitionInformation_eq_zero_iff
      (X := X) ρ.fst ρ.condKernel (partitionBlockOf π)

/-- **P-COMP-01 (frozen-source form).**

Start from one joint probability law of the external interface record `U` and
all child paths.  For every actual partition `π`, use the conditional joint
path law supplied by the disintegration of that same `ρ`, reblock the same path
coordinates according to `π`, and compare it by KL divergence with the product
of its conditional block marginals.

Then:
1. every partition score is nonnegative;
2. `I_π = 0` iff the blocks of `π` are independent conditional on `U`;
3. the exact finite minimum over all nontrivial partitions is positive iff no
   nontrivial partition conditionally factorizes the path law.
-/
theorem p_comp_01
    (ρ : Measure (U × (∀ i, X i))) [IsProbabilityMeasure ρ]
    (hI : 2 ≤ Fintype.card I) :
    (∀ π : ChildPartition I,
      0 ≤ sourcePartitionInformation (X := X) ρ π) ∧
    (∀ π : ChildPartition I,
      sourcePartitionInformation (X := X) ρ π = 0 ↔
        SourcePathFactorizes (X := X) ρ π) ∧
    (0 < sourcePathIntegrationMargin (X := X) ρ hI ↔
      ∀ π : ChildPartition I,
        IsNontrivialPartition π →
          ¬ SourcePathFactorizes (X := X) ρ π) := by
  constructor
  · intro π
    exact bot_le
  constructor
  · intro π
    exact sourcePartitionInformation_eq_zero_iff (X := X) ρ π
  · unfold sourcePathIntegrationMargin
    exact
      exactPathIntegrationMargin_pos_iff_no_factorization
        hI
        (fun π => sourcePartitionInformation (X := X) ρ π)
        (fun π => SourcePathFactorizes (X := X) ρ π)
        (fun π _ => sourcePartitionInformation_eq_zero_iff (X := X) ρ π)

end

end UEOT.V3.CompositionPathSource
