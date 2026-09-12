import UEOT.V3.InformationBinaryConditionalMean
import UEOT.V3.InformationDecoderConditionalFano
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact binary entropy identities

This module contains only the real-valued entropy side of the binary
mutual-information bridge.  It is deliberately independent of KL algebra.
-/

namespace UEOT.V3.InformationBinaryEntropy

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open UEOT.V3.InformationBinaryConditionalMean
open UEOT.V3.InformationDecoderConditionalFano

universe uX

variable {X : Type uX} [MeasurableSpace X]
variable [StandardBorelSpace X] [Nonempty X]

/-- For a probability law on `Fin 2`, the two-point Shannon sum is exactly
Mathlib's binary entropy of the success probability. -/
theorem fin2_negMulLog_sum_eq_binEntropy
    (ν : Measure (Fin 2)) [IsProbabilityMeasure ν] :
    (∑ j : Fin 2, Real.negMulLog ((ν {j}).toReal)) =
      Real.binEntropy (ν.real ({1} : Set (Fin 2))) := by
  have hcomp :
      ({1} : Set (Fin 2))ᶜ = ({0} : Set (Fin 2)) := by
    ext j
    fin_cases j <;> simp
  have h0 :
      ν.real ({0} : Set (Fin 2)) =
        1 - ν.real ({1} : Set (Fin 2)) := by
    have h := probReal_compl_eq_one_sub (μ := ν)
      (measurableSet_singleton (1 : Fin 2))
    rw [hcomp] at h
    exact h
  rw [Fin.sum_univ_two]
  change Real.negMulLog (ν.real ({0} : Set (Fin 2))) +
      Real.negMulLog (ν.real ({1} : Set (Fin 2))) =
    Real.binEntropy (ν.real ({1} : Set (Fin 2)))
  rw [h0, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- The finite-posterior entropy used by the decoder/Fano layer is exactly the
average binary entropy of `P(B=1 | X=x)`. -/
theorem posteriorConditionalEntropy_fin2_eq_binEntropy_integral
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    posteriorConditionalEntropy ρ.fst ρ.condKernel =
      ∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst := by
  unfold posteriorConditionalEntropy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simpa [posteriorBitOneProb] using
      (fin2_negMulLog_sum_eq_binEntropy (ρ.condKernel x))

/-- The posterior binary entropy integrand is integrable, uniformly bounded by
`log 2`. -/
theorem integrable_binEntropy_posteriorBitOneProb
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    Integrable (fun x => Real.binEntropy (posteriorBitOneProb ρ x)) ρ.fst := by
  have hmeas : Measurable (fun x => Real.binEntropy (posteriorBitOneProb ρ x)) :=
    Real.binEntropy_continuous.measurable.comp (measurable_posteriorBitOneProb ρ)
  refine Integrable.mono' (integrable_const (Real.log 2))
    hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hp0 : 0 ≤ posteriorBitOneProb ρ x := measureReal_nonneg
  have hp1 : posteriorBitOneProb ρ x ≤ 1 := measureReal_le_one
  have hnonneg : 0 ≤ Real.binEntropy (posteriorBitOneProb ρ x) :=
    Real.binEntropy_nonneg hp0 hp1
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hlog] using
    (Real.binEntropy_le_log_two (p := posteriorBitOneProb ρ x))

end UEOT.V3.InformationBinaryEntropy
