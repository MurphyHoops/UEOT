import UEOT.V3.InformationKernelKL
import Mathlib.Probability.Kernel.Posterior
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Finite-binary posterior absolute continuity

For a probability law on `X × Fin 2`, the standard-Borel conditional kernel
`P(B | X=x)` is absolutely continuous with respect to the binary marginal
`P_B` for `P_X`-almost every `x`.

The proof does not classify the boundary cases `P_B(B=1)=0,1` manually.  It
swaps the joint law, disintegrates `P(X|B)`, and uses Mathlib's countable-prior
posterior absolute-continuity theorem.
-/

namespace UEOT.V3.InformationBinaryPosterior

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]
variable [StandardBorelSpace X] [Nonempty X]

/-- The same binary experiment with the binary coordinate first. -/
noncomputable def swappedBinaryJoint
    (ρ : Measure (X × Fin 2)) : Measure (Fin 2 × X) :=
  ρ.map Prod.swap

instance swappedBinaryJoint_isProbability
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (swappedBinaryJoint ρ) := by
  unfold swappedBinaryJoint
  exact (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).2 inferInstance

/-- Likelihood kernel `P(X | B)` obtained by disintegrating the swapped law. -/
noncomputable def binaryLikelihood
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] : Kernel (Fin 2) X :=
  (swappedBinaryJoint ρ).condKernel

instance binaryLikelihood_isMarkov
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (binaryLikelihood ρ) := by
  unfold binaryLikelihood
  infer_instance

/-- The likelihood mixture recovers the original `X` marginal. -/
theorem binaryLikelihood_comp_snd_eq_fst
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    binaryLikelihood ρ ∘ₘ ρ.snd = ρ.fst := by
  have hdis :
      ρ.snd ⊗ₘ binaryLikelihood ρ = swappedBinaryJoint ρ := by
    simpa [swappedBinaryJoint, binaryLikelihood] using
      (Measure.disintegrate (swappedBinaryJoint ρ) (swappedBinaryJoint ρ).condKernel)
  rw [← Measure.snd_compProd, hdis]
  simp [swappedBinaryJoint]

/-- The conditional binary kernel selected directly from the original joint is
an a.e. version of the posterior obtained from the swapped likelihood model. -/
theorem condKernel_ae_eq_binaryPosterior
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    ρ.condKernel =ᵐ[ρ.fst] (binaryLikelihood ρ)†ρ.snd := by
  have hdis :
      ρ.snd ⊗ₘ binaryLikelihood ρ = swappedBinaryJoint ρ := by
    simpa [swappedBinaryJoint, binaryLikelihood] using
      (Measure.disintegrate (swappedBinaryJoint ρ) (swappedBinaryJoint ρ).condKernel)
  have hjoint :
      (binaryLikelihood ρ ∘ₘ ρ.snd) ⊗ₘ ρ.condKernel =
        (ρ.snd ⊗ₘ binaryLikelihood ρ).map Prod.swap := by
    calc
      (binaryLikelihood ρ ∘ₘ ρ.snd) ⊗ₘ ρ.condKernel
          = ρ.fst ⊗ₘ ρ.condKernel := by
              rw [binaryLikelihood_comp_snd_eq_fst]
      _ = ρ := Measure.disintegrate ρ ρ.condKernel
      _ = (swappedBinaryJoint ρ).map Prod.swap := by
              unfold swappedBinaryJoint
              rw [Measure.map_map, Prod.swap_swap_eq, Measure.map_id] <;> measurability
      _ = (ρ.snd ⊗ₘ binaryLikelihood ρ).map Prod.swap := by rw [hdis]
  have hpost := ae_eq_posterior_of_compProd_eq
    (κ := binaryLikelihood ρ) (μ := ρ.snd) (η := ρ.condKernel) hjoint
  simpa [binaryLikelihood_comp_snd_eq_fst ρ] using hpost

/-- **Binary posterior AC.**  For `P_X`-a.e. `x`,
`P(B|X=x) ≪ P_B`. -/
theorem condKernel_ac_snd_ae
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    ∀ᵐ x ∂ρ.fst, ρ.condKernel x ≪ ρ.snd := by
  have hprior :
      ∀ᵐ b ∂ρ.snd,
        binaryLikelihood ρ b ≪ binaryLikelihood ρ ∘ₘ ρ.snd :=
    Measure.absolutelyContinuous_comp_of_countable
  have hpostac :
      ∀ᵐ x ∂(binaryLikelihood ρ ∘ₘ ρ.snd),
        ((binaryLikelihood ρ)†ρ.snd) x ≪ ρ.snd :=
    absolutelyContinuous_posterior hprior
  rw [binaryLikelihood_comp_snd_eq_fst ρ] at hpostac
  filter_upwards [condKernel_ae_eq_binaryPosterior ρ, hpostac] with x hx hxac
  rw [hx]
  exact hxac

end UEOT.V3.InformationBinaryPosterior
