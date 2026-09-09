import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# P-INFO foundation — KL-backed information quantities

The v3 source uses mutual information, conditional mutual information and KL
chain/data-processing identities.  Pinned Mathlib already machine-checks the
measure-theoretic KL divergence and composition-product chain rule.  This
module builds the UEOT information layer on that foundation rather than
postulating information identities.
-/

namespace UEOT.V3.InformationCore

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ProbabilityTheory ENNReal

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace Y]

/-- Mutual information of a joint law, defined in the standard
measure-theoretic way as KL from the product of its marginals. -/
noncomputable def mutualInfo (μ : Measure (X × Y)) : ℝ≥0∞ :=
  klDiv μ (μ.fst.prod μ.snd)

/-- A same-input conditional KL residual.  When `κ` is the full-history
future kernel and `η` is the kernel reconstructed from a representation,
this is the composition-product form of the conditional information
residual used in P-INFO-01/02. -/
noncomputable def kernelInformationResidual
    (μ : Measure X) (κ η : Kernel X Y) : ℝ≥0∞ :=
  klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)

theorem mutualInfo_eq_zero_iff
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ] :
    mutualInfo μ = 0 ↔ μ = μ.fst.prod μ.snd := by
  unfold mutualInfo
  exact InformationTheory.klDiv_eq_zero_iff

theorem kernelInformationResidual_self
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    kernelInformationResidual μ κ κ = 0 := by
  unfold kernelInformationResidual
  simp

/-- Direct UEOT wrapper around Mathlib's measure-theoretic KL chain rule.
It is the algebraic engine used later to derive the source MI/CMI chain
identities without adding an information-theory axiom. -/
theorem kl_chain_rule_with_kernel_residual
    (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) =
      klDiv μ ν + kernelInformationResidual μ κ η := by
  simpa [kernelInformationResidual] using
    (InformationTheory.klDiv_compProd_eq_add μ ν κ η)

/-- Common post-processing cannot increase KL.  This is the pinned-Mathlib
data-processing bridge needed by later UEOT information statements. -/
theorem kl_map_data_processing
    {Z : Type*} [MeasurableSpace Z]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → Z) (hf : Measurable f) :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν :=
  InformationTheory.klDiv_map_le μ ν hf

end UEOT.V3.InformationCore
