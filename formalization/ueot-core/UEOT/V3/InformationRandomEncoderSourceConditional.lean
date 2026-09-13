import UEOT.V3.InformationRandomEncoder
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# P-INFO-03 — randomized encoder source-conditional invariance

A randomized encoder augments a fixed source law `P(U,H)` with a code variable
`M ~ P(M|U,H)`.  The induced law on `U × (H × M)` must preserve not only the
source marginal `P(U,H)` but also the regular conditional law `P(H|U)`.

This module proves that fact through disintegration uniqueness.  Starting from
`ρ = P(U,H,M)`, map the canonical disintegration

`ρ.fst ⊗ₘ ρ.condKernel = ρ`

through the second-coordinate projection `(H,M) ↦ H`.  The resulting
composition product reconstructs the original source law, so its conditional
kernel is almost everywhere the source `μ.condKernel`.
-/

namespace UEOT.V3.InformationRandomEncoderSourceConditional

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationRandomEncoder

universe uU uH uM

variable {U : Type uU} {H : Type uH} {M : Type uM}
variable [MeasurableSpace U] [MeasurableSpace H] [MeasurableSpace M]
variable [StandardBorelSpace U] [StandardBorelSpace H] [StandardBorelSpace M]
variable [Nonempty H] [Nonempty M]

/-- **Conditional source invariance.**  Under any Markov randomized encoder,
the `H|U` kernel obtained by projecting the true `P(H,M|U)` fiber is almost
everywhere the original source conditional kernel `P(H|U)`. -/
theorem randomEncoder_condKernel_fst_ae_eq_source
    (μ : Measure (U × H)) [IsProbabilityMeasure μ]
    (η : Kernel (U × H) M) [IsMarkovKernel η] :
    ((randomEncoderJoint μ η).condKernel.map Prod.fst) =ᵐ[μ.fst]
      μ.condKernel := by
  let ρ : Measure (U × (H × M)) := randomEncoderJoint μ η
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  have hsource :
      ρ.map (encoderSourceProjection (U := U) (H := H) (M := M)) = μ := by
    dsimp [ρ]
    exact randomEncoderJoint_map_sourceProjection μ η
  have hfst : ρ.fst = μ.fst := by
    dsimp [ρ]
    exact randomEncoderJoint_fst μ η
  have hdis : ρ.fst ⊗ₘ ρ.condKernel = ρ :=
    Measure.disintegrate ρ ρ.condKernel
  have hcand : μ = μ.fst ⊗ₘ (ρ.condKernel.map Prod.fst) := by
    calc
      μ = ρ.map (encoderSourceProjection (U := U) (H := H) (M := M)) := hsource.symm
      _ = ρ.map (Prod.map id Prod.fst) := by
        apply Measure.map_congr
        filter_upwards with z
        rfl
      _ = (ρ.fst ⊗ₘ ρ.condKernel).map (Prod.map id Prod.fst) := by
        rw [hdis]
      _ = ρ.fst ⊗ₘ (ρ.condKernel.map Prod.fst) := by
        symm
        exact Measure.compProd_map measurable_fst
      _ = μ.fst ⊗ₘ (ρ.condKernel.map Prod.fst) := by
        rw [hfst]
  exact ProbabilityTheory.eq_condKernel_of_measure_eq_compProd
    (ρ := μ) (ρ.condKernel.map Prod.fst) hcand

end

end UEOT.V3.InformationRandomEncoderSourceConditional
