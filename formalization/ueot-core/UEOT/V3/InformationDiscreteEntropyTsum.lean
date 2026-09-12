import UEOT.V3.InformationDiscreteEntropy
import UEOT.V3.InformationConditionalDiscreteEntropy
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-!
# Countable Shannon `tsum` / discrete entropy compatibility

P-INFO-03 uses a genuine conditional entropy defined fiberwise by the countable
Shannon sum.  The existing P-INFO-01 infrastructure represents countable
Shannon entropy by the extended self-information integral
`discreteShannonEntropy`.  This module proves that the two representations agree
in the finite-entropy regime required by the frozen P-INFO-03 source contract.
-/

namespace UEOT.V3.InformationDiscreteEntropyTsum

noncomputable section

open MeasureTheory
open scoped ENNReal
open UEOT.V3.InformationDiscreteEntropy

universe uC

variable {C : Type uC}
variable [Countable C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- The extended countable Shannon sum of a probability law. -/
noncomputable def discreteShannonTsum (μ : Measure C) : ℝ≥0∞ :=
  ∑' c : C, ENNReal.ofReal (Real.negMulLog ((μ {c}).toReal))

/-- The self-information integrand used by `discreteShannonEntropy`. -/
noncomputable def discreteSelfInfo (μ : Measure C) (c : C) : ℝ :=
  Real.log (copyDensity μ (c, c)).toReal

lemma discreteSelfInfo_nonneg
    (μ : Measure C) [IsProbabilityMeasure μ] (c : C) :
    0 ≤ discreteSelfInfo μ c := by
  have hmass : μ ({c} : Set C) ≤ 1 := by
    simpa using (measure_mono (Set.subset_univ ({c} : Set C)))
  have hp_le_one : (μ ({c} : Set C)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top μ ({c} : Set C)) hmass
  unfold discreteSelfInfo copyDensity
  simp only [if_pos rfl, ENNReal.toReal_inv, Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg hp_le_one)

lemma ofReal_selfInfo_mul_singleton
    (μ : Measure C) [IsProbabilityMeasure μ] (c : C) :
    ENNReal.ofReal (discreteSelfInfo μ c) * μ ({c} : Set C) =
      ENNReal.ofReal (Real.negMulLog ((μ ({c} : Set C)).toReal)) := by
  have hfin : μ ({c} : Set C) ≠ ∞ := measure_ne_top μ ({c} : Set C)
  rw [← ENNReal.ofReal_toReal hfin]
  rw [← ENNReal.ofReal_mul (discreteSelfInfo_nonneg μ c)]
  congr 1
  unfold discreteSelfInfo copyDensity Real.negMulLog
  simp only [if_pos rfl, ENNReal.toReal_inv, Real.log_inv]
  ring

/-- The lower Lebesgue integral of self-information is exactly the countable
Shannon `tsum`. -/
theorem lintegral_selfInfo_eq_discreteShannonTsum
    (μ : Measure C) [IsProbabilityMeasure μ] :
    (∫⁻ c, ENNReal.ofReal (discreteSelfInfo μ c) ∂μ) =
      discreteShannonTsum μ := by
  rw [MeasureTheory.lintegral_countable']
  unfold discreteShannonTsum
  congr 1
  funext c
  exact ofReal_selfInfo_mul_singleton μ c

/-- In the finite-entropy regime used by P-INFO-03, the new fiber Shannon sum
agrees exactly with the pre-existing extended countable entropy. -/
theorem discreteShannonEntropy_eq_discreteShannonTsum_of_ne_top
    (μ : Measure C) [IsProbabilityMeasure μ]
    (hfinite : discreteShannonTsum μ ≠ ∞) :
    discreteShannonEntropy μ = discreteShannonTsum μ := by
  let info : C → ℝ := discreteSelfInfo μ
  have hmeas : AEStronglyMeasurable info μ :=
    (measurable_of_countable info).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[μ] info :=
    ae_of_all μ (fun c => discreteSelfInfo_nonneg μ c)
  have hlin_lt : (∫⁻ c, ENNReal.ofReal (info c) ∂μ) < ∞ := by
    rw [show (∫⁻ c, ENNReal.ofReal (info c) ∂μ) = discreteShannonTsum μ by
      simpa [info] using lintegral_selfInfo_eq_discreteShannonTsum μ]
    exact (lt_top_iff_ne_top).2 hfinite
  have hhas : HasFiniteIntegral info μ :=
    (hasFiniteIntegral_iff_ofReal hnonneg).2 hlin_lt
  have hint : Integrable info μ := ⟨hmeas, hhas⟩
  unfold discreteShannonEntropy
  change (if Integrable info μ then ENNReal.ofReal (∫ c, info c ∂μ) else ∞) = _
  rw [if_pos hint]
  rw [ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  simpa [info] using lintegral_selfInfo_eq_discreteShannonTsum μ

end

end UEOT.V3.InformationDiscreteEntropyTsum
