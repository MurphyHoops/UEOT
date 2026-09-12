import UEOT.V3.InformationConditionalBinary
import UEOT.V3.InformationDecoderConditionalFano
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# P-INFO-04 — conditional binary source geometry

The frozen-source conditional clause concerns a binary future identity `B`, a
candidate macrostate `M`, an interface `U`, and an arbitrary decoder
`B̂ = δ(M,U)`.

For a law on `U × (M × Fin 2)` this module re-associates the variables as
`(U × M) × Fin 2`, disintegrates to obtain `P(B | U,M)`, and applies the
arbitrary-decoder conditional Fano theorem.  No MAP substitution is used.
-/

namespace UEOT.V3.InformationPInfo04Conditional

open MeasureTheory ProbabilityTheory
open UEOT.V3.InformationConditionalBinary
open UEOT.V3.InformationDecoderConditionalFano

universe uU uM

variable {U : Type uU} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace M]
variable [Nonempty M]

/-- Re-associate `U × (M × B)` as `(U × M) × B`. -/
def reassocUMB : U × (M × Fin 2) → (U × M) × Fin 2 :=
  fun z => ((z.1, z.2.1), z.2.2)

lemma measurable_reassocUMB : Measurable (reassocUMB : U × (M × Fin 2) → (U × M) × Fin 2) := by
  exact
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)

/-- The same experiment law, exposed in the `(U,M)`-then-`B` geometry required
by the decoder/posterior Fano theorem. -/
noncomputable def binaryUMJoint
    (ρ : Measure (U × (M × Fin 2))) : Measure ((U × M) × Fin 2) :=
  ρ.map reassocUMB

instance binaryUMJoint_isProbability
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (binaryUMJoint ρ) := by
  unfold binaryUMJoint
  exact (Measure.isProbabilityMeasure_map_iff measurable_reassocUMB.aemeasurable).2 inferInstance

/-- Posterior binary law `P(B | U,M)`. -/
noncomputable def posteriorBitGivenUM
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    Kernel (U × M) (Fin 2) :=
  (binaryUMJoint ρ).condKernel

instance posteriorBitGivenUM_isMarkov
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (posteriorBitGivenUM ρ) := by
  unfold posteriorBitGivenUM
  infer_instance

/-- Source quantity `H(B | M,U)`, represented as the posterior binary entropy
average under the true `(U,M)` marginal. -/
noncomputable def conditionalBinaryEntropyGivenUM
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] : ℝ :=
  posteriorConditionalEntropy (binaryUMJoint ρ).fst (posteriorBitGivenUM ρ)

/-- Error probability of an arbitrary measurable source decoder
`δ : (U,M) → B`. -/
noncomputable def conditionalBinaryDecoderError
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (d : U × M → Fin 2) : ℝ :=
  decoderError (binaryUMJoint ρ).fst (posteriorBitGivenUM ρ) d

/-- **Conditional binary Fano, actual decoder form.**

For every measurable decoder of `B` from `(U,M)`, the true conditional entropy
is bounded by the binary entropy of its average error probability. -/
theorem conditionalBinaryEntropyGivenUM_le_errorEntropy
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (d : U × M → Fin 2) (hd : Measurable d) :
    conditionalBinaryEntropyGivenUM ρ ≤
      Real.binEntropy (conditionalBinaryDecoderError ρ d) := by
  have h := posteriorConditionalEntropy_le_decoderError
    (M := 2) (by norm_num)
    (binaryUMJoint ρ).fst (posteriorBitGivenUM ρ) d hd
  simpa [conditionalBinaryEntropyGivenUM, conditionalBinaryDecoderError] using h

/-- The source error is a genuine probability and is therefore nonnegative. -/
theorem conditionalBinaryDecoderError_nonneg
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (d : U × M → Fin 2) (hd : Measurable d) :
    0 ≤ conditionalBinaryDecoderError ρ d := by
  unfold conditionalBinaryDecoderError decoderError
  have hc := measurable_decoderCorrectProb (posteriorBitGivenUM ρ) d hd
  apply integral_nonneg
  intro x
  have hx := decoderCorrectProb_mem_Icc (posteriorBitGivenUM ρ) d x
  linarith [hx.2]

/-- **Frozen-source epsilon form of conditional binary Fano.**

If the actual decoder error is at most `ε` and `ε ≤ 1/2`, then
`H(B|M,U) ≤ h₂(ε)`. -/
theorem conditionalBinaryEntropyGivenUM_le_epsilonEntropy
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (d : U × M → Fin 2) (hd : Measurable d)
    (ε : ℝ)
    (herr : conditionalBinaryDecoderError ρ d ≤ ε)
    (hhalf : ε ≤ (2 : ℝ)⁻¹) :
    conditionalBinaryEntropyGivenUM ρ ≤ Real.binEntropy ε := by
  have he0 : 0 ≤ conditionalBinaryDecoderError ρ d :=
    conditionalBinaryDecoderError_nonneg ρ d hd
  have hε0 : 0 ≤ ε := he0.trans herr
  have hehalf : conditionalBinaryDecoderError ρ d ≤ (2 : ℝ)⁻¹ :=
    herr.trans hhalf
  have hmono :
      Real.binEntropy (conditionalBinaryDecoderError ρ d) ≤ Real.binEntropy ε :=
    Real.binEntropy_strictMonoOn.monotoneOn
      ⟨he0, hehalf⟩ ⟨hε0, hhalf⟩ herr
  exact (conditionalBinaryEntropyGivenUM_le_errorEntropy ρ d hd).trans hmono

/-- Finite-binary entropy form of conditional information.

For binary `B`, both conditional entropies are finite real numbers, so this
subtraction has no `∞-∞` ambiguity.  A separate bridge theorem identifies this
quantity with the repository's KL/chain-rule conditional mutual information. -/
noncomputable def conditionalBinaryInformationEntropyForm
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ] : ℝ :=
  conditionalBinaryEntropy ρ - conditionalBinaryEntropyGivenUM ρ

/-- **P-INFO-04 conditional source inequality in entropy form.**

This is the exact Fano implication in the frozen binary clause, before the
representation bridge from finite-binary entropy form to KL conditional mutual
information is applied. -/
theorem conditionalBinaryInformationEntropyForm_ge_sourceBound
    (ρ : Measure (U × (M × Fin 2))) [IsProbabilityMeasure ρ]
    (d : U × M → Fin 2) (hd : Measurable d)
    (ε : ℝ)
    (herr : conditionalBinaryDecoderError ρ d ≤ ε)
    (hhalf : ε ≤ (2 : ℝ)⁻¹) :
    conditionalBinaryEntropy ρ - Real.binEntropy ε ≤
      conditionalBinaryInformationEntropyForm ρ := by
  unfold conditionalBinaryInformationEntropyForm
  have hfano := conditionalBinaryEntropyGivenUM_le_epsilonEntropy
    ρ d hd ε herr hhalf
  linarith

end UEOT.V3.InformationPInfo04Conditional
