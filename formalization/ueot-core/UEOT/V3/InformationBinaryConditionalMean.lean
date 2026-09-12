import Mathlib.Probability.Kernel.Disintegration.Integral
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Binary posterior mean identity

For a probability law on `X × Fin 2`, the conditional success probability
`P(B=1 | X=x)` averages back to the marginal success probability `P(B=1)`.
This is the exact finite-binary tower identity needed to cancel the cross-entropy
term in the P-INFO-04 KL/entropy bridge.
-/

namespace UEOT.V3.InformationBinaryConditionalMean

open MeasureTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]
variable [StandardBorelSpace X] [Nonempty X]

/-- Posterior probability of the binary event `{1}`. -/
noncomputable def posteriorBitOneProb
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ]
    (x : X) : ℝ :=
  (ρ.condKernel x).real ({1} : Set (Fin 2))

theorem measurable_posteriorBitOneProb
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    Measurable (posteriorBitOneProb ρ) := by
  unfold posteriorBitOneProb
  exact ENNReal.measurable_toReal.comp
    (ρ.condKernel.measurable_coe (measurableSet_singleton (1 : Fin 2)))

/-- **Posterior mean = marginal.** -/
theorem integral_posteriorBitOneProb_eq_marginal
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    ∫ x, posteriorBitOneProb ρ x ∂ρ.fst =
      ρ.snd.real ({1} : Set (Fin 2)) := by
  have h := Measure.setIntegral_condKernel_univ_left
    (ρ := ρ)
    (f := fun _ : X × Fin 2 => (1 : ℝ))
    (measurableSet_singleton (1 : Fin 2))
    ((integrable_const (1 : ℝ)).integrableOn)
  have hset :
      (Set.univ : Set X) ×ˢ ({1} : Set (Fin 2)) =
        Prod.snd ⁻¹' ({1} : Set (Fin 2)) := by
    ext z
    simp
  rw [hset] at h
  simpa [posteriorBitOneProb, Measure.snd_apply, measureReal_def] using h

end UEOT.V3.InformationBinaryConditionalMean
