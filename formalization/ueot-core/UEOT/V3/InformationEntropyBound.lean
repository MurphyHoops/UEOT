import UEOT.V3.InformationCore
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# P-INFO-01 entropy-bound reduction

The remaining source-facing inequality `I(M;Y) ≤ H(M)` is separated into two
standard pieces.  This module formalizes the channel/data-processing half:
information sent through an arbitrary Markov channel from a copied discrete
state cannot exceed the self-information of that copied state.  The remaining
layer is the discrete identity between that copy KL divergence and Shannon
entropy.
-/

namespace UEOT.V3.InformationEntropyBound

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

universe uM uY

variable {M : Type uM} {Y : Type uY}
variable [MeasurableSpace M] [MeasurableSpace Y]

/-- The diagonal/copy law of a random state. -/
noncomputable def copyJoint (μ : Measure M) : Measure (M × M) :=
  μ.map (fun m => (m, m))

/-- A Markov channel on a copied pair `(m₁,m₂)` which retains the first
coordinate and sends the second through `κ`.  On a diagonal input this produces
`(m,Y)` with `Y ∼ κ m`; on an independent-copy input it destroys dependence
between the retained first coordinate and the channel output. -/
noncomputable def retainFirstSendSecond (κ : Kernel M Y) :
    Kernel (M × M) (M × Y) :=
  (Kernel.deterministic Prod.fst measurable_fst) ×ₖ
    Kernel.prodMkLeft M κ

instance retainFirstSendSecond_isMarkov
    (κ : Kernel M Y) [IsMarkovKernel κ] :
    IsMarkovKernel (retainFirstSendSecond κ) := by
  unfold retainFirstSendSecond
  infer_instance

/-- Channel data processing: the KL separation remaining after retaining the
first copy and processing the second through `κ` cannot exceed the KL
separation of the original diagonal copy law from two independent copies. -/
theorem channel_kl_le_copy_kl
    (μ : Measure M) [IsProbabilityMeasure μ]
    (κ : Kernel M Y) [IsMarkovKernel κ] :
    klDiv (retainFirstSendSecond κ ∘ₘ copyJoint μ)
        (retainFirstSendSecond κ ∘ₘ μ.prod μ) ≤
      klDiv (copyJoint μ) (μ.prod μ) := by
  exact InformationTheory.klDiv_comp_right_le
    (copyJoint μ) (μ.prod μ) (retainFirstSendSecond κ)

end UEOT.V3.InformationEntropyBound
