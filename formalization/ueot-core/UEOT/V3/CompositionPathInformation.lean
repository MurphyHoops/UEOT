import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Basic

/-!
# P-COMP-01 — conditional multi-block path integration

For one declared finite path partition, the block tuple is represented by a
finite dependent product `∀ b, X b`. In each conditional fiber we compare the
true joint law with the finite product of its block marginals. The resulting
KL divergence vanishes exactly when the block coordinate maps are jointly
independent.

The conditional quantity is the `U`-average of these fiber KL divergences. Its
zero set is therefore exactly almost-everywhere conditional block independence.
For a finite nonempty family whose index type enumerates the declared nontrivial
partitions, positivity of the minimum is equivalent to failure of factorization
for every member.
-/

namespace UEOT.V3.CompositionPathInformation

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

universe uB uX uU uP

variable {B : Type uB} [Fintype B]
variable {X : B → Type uX}
variable [∀ b, MeasurableSpace (X b)]

/-- Product of all block marginals of a finite joint law. -/
noncomputable def blockProductMeasure
    (μ : Measure (∀ b, X b)) [IsFiniteMeasure μ] :
    Measure (∀ b, X b) :=
  Measure.pi (fun b => μ.map (fun x => x b))

instance blockProductMeasure_isFinite
    (μ : Measure (∀ b, X b)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (blockProductMeasure μ) := by
  unfold blockProductMeasure
  infer_instance

/-- Fiberwise path-integration score for one finite partition. -/
noncomputable def partitionFiberKL
    (μ : Measure (∀ b, X b)) [IsProbabilityMeasure μ] : ENNReal :=
  klDiv μ (blockProductMeasure μ)

/-- The product-of-marginals law is exactly the indexed independence law. -/
theorem eq_blockProductMeasure_iff_iIndep
    (μ : Measure (∀ b, X b)) [IsProbabilityMeasure μ] :
    μ = blockProductMeasure μ ↔
      iIndepFun (fun b (x : ∀ b, X b) => x b) μ := by
  symm
  simpa [blockProductMeasure] using
    (iIndepFun_iff_map_fun_eq_pi_map
      (μ := μ)
      (f := fun b (x : ∀ b, X b) => x b)
      (fun b => (measurable_pi_apply b).aemeasurable))

/-- A partition fiber has zero KL exactly when its path blocks are independent. -/
theorem partitionFiberKL_eq_zero_iff_iIndep
    (μ : Measure (∀ b, X b)) [IsProbabilityMeasure μ] :
    partitionFiberKL μ = 0 ↔
      iIndepFun (fun b (x : ∀ b, X b) => x b) μ := by
  unfold partitionFiberKL
  rw [klDiv_eq_zero_iff]
  exact eq_blockProductMeasure_iff_iIndep μ

lemma partitionFiberKL_nonneg
    (μ : Measure (∀ b, X b)) [IsProbabilityMeasure μ] :
    0 ≤ partitionFiberKL μ :=
  bot_le

variable {U : Type uU} [MeasurableSpace U]

/-- Source quantity `I_π`: average conditional KL for one declared partition. -/
noncomputable def conditionalPartitionInformation
    (ν : Measure U)
    (κ : Kernel U (∀ b, X b)) [IsMarkovKernel κ] : ENNReal :=
  ∫⁻ u, partitionFiberKL (κ u) ∂ν

/-- Conditional block independence means indexed independence in almost every
true conditional fiber. -/
def ConditionallyIndependentBlocks
    (ν : Measure U)
    (κ : Kernel U (∀ b, X b)) : Prop :=
  ∀ᵐ u ∂ν, iIndepFun (fun b (x : ∀ b, X b) => x b) (κ u)

/-- The conditional path-integration score vanishes exactly for conditional
block independence. `hMeas` is the explicit measurability regularity needed for
the source expectation `E_U`; no finiteness of the KL value is assumed. -/
theorem conditionalPartitionInformation_eq_zero_iff
    (ν : Measure U)
    (κ : Kernel U (∀ b, X b)) [IsMarkovKernel κ]
    (hMeas : AEMeasurable (fun u => partitionFiberKL (κ u)) ν) :
    conditionalPartitionInformation ν κ = 0 ↔
      ConditionallyIndependentBlocks ν κ := by
  unfold conditionalPartitionInformation ConditionallyIndependentBlocks
  rw [lintegral_eq_zero_iff' hMeas]
  constructor
  · intro h
    filter_upwards [h] with u hu
    exact (partitionFiberKL_eq_zero_iff_iIndep (κ u)).1 hu
  · intro h
    filter_upwards [h] with u hu
    exact (partitionFiberKL_eq_zero_iff_iIndep (κ u)).2 hu

variable {P : Type uP} [Fintype P] [Nonempty P]

/-- Finite-family source margin `Σ_path = min_π I_π`. -/
noncomputable def pathIntegrationMargin (I : P → ENNReal) : ENNReal :=
  Finset.univ.inf' Finset.univ_nonempty I

/-- Finite minimum positivity is equivalent to every declared partition having
strictly positive conditional integration score. -/
theorem pathIntegrationMargin_pos_iff_all_pos
    (I : P → ENNReal) :
    0 < pathIntegrationMargin I ↔ ∀ π, 0 < I π := by
  unfold pathIntegrationMargin
  rw [Finset.lt_inf'_iff]
  simp

/-- Generic finite-family order lemma used by the source-facing theorem below. -/
theorem pathIntegrationMargin_pos_iff_no_factorization
    (I : P → ENNReal)
    (factorizes : P → Prop)
    (hzero : ∀ π, I π = 0 ↔ factorizes π) :
    0 < pathIntegrationMargin I ↔ ∀ π, ¬ factorizes π := by
  rw [pathIntegrationMargin_pos_iff_all_pos]
  constructor
  · intro h π hfac
    exact (ne_of_gt (h π)) ((hzero π).2 hfac)
  · intro h π
    rw [pos_iff_ne_zero]
    intro hI
    exact h π ((hzero π).1 hI)

section DeclaredPartitionFamily

/-- `P` indexes the already-declared finite family of nontrivial partitions.
Different partitions may have different finite block index types and block path
spaces. -/
variable {BP : P → Type uB} [∀ π, Fintype (BP π)]
variable {XP : (π : P) → BP π → Type uX}
variable [∀ π b, MeasurableSpace (XP π b)]

/-- **P-COMP-01.** For every declared partition, the conditional KL score is
nonnegative and is zero exactly when its path blocks are conditionally
independent given `U`. Consequently the minimum over the finite declared
nontrivial partition family is positive exactly when none of those partitions
factorizes. -/
theorem p_comp_01
    (ν : Measure U)
    (κ : (π : P) → Kernel U (∀ b : BP π, XP π b))
    [∀ π, IsMarkovKernel (κ π)]
    (hMeas : ∀ π,
      AEMeasurable
        (fun u => partitionFiberKL (B := BP π) (X := XP π) ((κ π) u)) ν) :
    (∀ π,
      0 ≤ conditionalPartitionInformation (B := BP π) (X := XP π) ν (κ π)) ∧
    (∀ π,
      conditionalPartitionInformation (B := BP π) (X := XP π) ν (κ π) = 0 ↔
        ConditionallyIndependentBlocks (B := BP π) (X := XP π) ν (κ π)) ∧
    (0 < pathIntegrationMargin
        (fun π => conditionalPartitionInformation
          (B := BP π) (X := XP π) ν (κ π)) ↔
      ∀ π,
        ¬ ConditionallyIndependentBlocks (B := BP π) (X := XP π) ν (κ π)) := by
  constructor
  · intro π
    exact bot_le
  constructor
  · intro π
    exact conditionalPartitionInformation_eq_zero_iff
      (B := BP π) (X := XP π) ν (κ π) (hMeas π)
  · apply pathIntegrationMargin_pos_iff_no_factorization
    intro π
    exact conditionalPartitionInformation_eq_zero_iff
      (B := BP π) (X := XP π) ν (κ π) (hMeas π)

end DeclaredPartitionFamily

end

end UEOT.V3.CompositionPathInformation
