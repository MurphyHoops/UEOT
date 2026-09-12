import UEOT.V3.InformationStatistic
import UEOT.V3.InformationKernelPinsker
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# P-INFO-02 — source-faithful predictive conditional information

The frozen UEOT Core v3 P-INFO-02 statement uses the standard conditional
mutual-information representation as the average KL divergence between the
predictive kernels `P(Y | H)` and `P(Y | S)`, where the deterministic
statistic `S` packages `(M,U)`.

This module makes that predictive orientation canonical for P-INFO-02.  It is
intentionally separate from the older posterior-oriented chain residual in
`InformationStatistic`: the latter is useful for P-INFO-01's finite-information
chain rule, but its conditional-kernel version is only fixed almost everywhere
under a different first marginal and therefore is not the right primitive for
P-INFO-02 without extra absolute-continuity hypotheses.
-/

namespace UEOT.V3.InformationPredictiveCMI

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.TotalVariation
open UEOT.V3.InformationStatistic
open UEOT.V3.InformationKernelPinsker

universe uH uS uY

variable {H : Type uH} {S : Type uS} {Y : Type uY}
variable [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace Y]

/-- The predictive kernel `P(Y | H)` selected by Mathlib's standard-Borel
disintegration. -/
noncomputable def historyPredictiveKernel
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsFiniteMeasure μ] : Kernel H Y :=
  μ.condKernel

/-- The predictive kernel `P(Y | S=f(H))`, pulled back to the original history
base so that it can be compared fiberwise with `P(Y | H)`. -/
noncomputable def statisticPredictiveKernel
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsFiniteMeasure μ]
    (f : H → S) (hf : Measurable f) : Kernel H Y :=
  Kernel.comap (statisticJoint μ f hf).condKernel f hf

instance historyPredictiveKernel_isMarkov
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsFiniteMeasure μ] :
    IsMarkovKernel (historyPredictiveKernel μ) := by
  unfold historyPredictiveKernel
  infer_instance

instance statisticPredictiveKernel_isMarkov
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsFiniteMeasure μ]
    (f : H → S) (hf : Measurable f) :
    IsMarkovKernel (statisticPredictiveKernel μ f hf) := by
  unfold statisticPredictiveKernel
  infer_instance

/-- The source-faithful conditional predictive-information residual for a
deterministic statistic `S=f(H)`.

It is the KL divergence from the true `(H,Y)` law to the law obtained by
keeping the true history marginal and replacing `P(Y|H)` by `P(Y|S)`. -/
noncomputable def predictiveConditionalInfoStatistic
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → S) (hf : Measurable f) : ℝ≥0∞ :=
  klDiv μ (μ.fst ⊗ₘ statisticPredictiveKernel μ f hf)

/-- The true joint law is the history marginal composed with `P(Y|H)`. -/
theorem compProd_historyPredictiveKernel_eq
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsFiniteMeasure μ] :
    μ.fst ⊗ₘ historyPredictiveKernel μ = μ := by
  unfold historyPredictiveKernel
  exact Measure.disintegrate μ μ.condKernel

/-- Re-express the canonical predictive residual as a shared-base kernel KL. -/
theorem predictiveConditionalInfoStatistic_eq_compProd
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → S) (hf : Measurable f) :
    predictiveConditionalInfoStatistic μ f hf =
      klDiv
        (μ.fst ⊗ₘ historyPredictiveKernel μ)
        (μ.fst ⊗ₘ statisticPredictiveKernel μ f hf) := by
  unfold predictiveConditionalInfoStatistic
  rw [compProd_historyPredictiveKernel_eq μ]

/-- Finite predictive conditional information automatically supplies the
a.e. fiber absolute continuity required by the shared-base KL/Pinsker layer;
no extra source hypothesis is needed. -/
theorem history_ac_statisticPredictive_ae_of_ne_top
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → S) (hf : Measurable f)
    (hfin : predictiveConditionalInfoStatistic μ f hf ≠ ⊤) :
    ∀ᵐ h ∂μ.fst,
      historyPredictiveKernel μ h ≪ statisticPredictiveKernel μ f hf h := by
  have hglobal :
      (μ.fst ⊗ₘ historyPredictiveKernel μ) ≪
        (μ.fst ⊗ₘ statisticPredictiveKernel μ f hf) := by
    have hkl :
        klDiv
          (μ.fst ⊗ₘ historyPredictiveKernel μ)
          (μ.fst ⊗ₘ statisticPredictiveKernel μ f hf) ≠ ⊤ := by
      rw [← predictiveConditionalInfoStatistic_eq_compProd μ f hf]
      exact hfin
    exact (klDiv_ne_top_iff.mp hkl).1
  exact hglobal.kernel_of_compProd

/-- **P-INFO-02 core, finite-information form.**

For a standard-Borel predictive target and deterministic statistic `S=f(H)`,
the expected predictive total-variation loss is controlled by the source
conditional information with the sharp Pinsker/Jensen constant. -/
theorem predictive_tv_le_sqrt_conditionalInfo
    [StandardBorelSpace H] [StandardBorelSpace S]
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → S) (hf : Measurable f)
    (hfin : predictiveConditionalInfoStatistic μ f hf ≠ ⊤) :
    (∫ h, tvDist
        (historyPredictiveKernel μ h)
        (statisticPredictiveKernel μ f hf h) ∂μ.fst) ≤
      Real.sqrt ((predictiveConditionalInfoStatistic μ f hf).toReal / 2) := by
  have hac :=
    history_ac_statisticPredictive_ae_of_ne_top μ f hf hfin
  have hbase : IsProbabilityMeasure μ.fst := by infer_instance
  letI : IsProbabilityMeasure μ.fst := hbase
  have h := integral_tvDist_le_sqrt_klDiv_compProd
    μ.fst
    (historyPredictiveKernel μ)
    (statisticPredictiveKernel μ f hf)
    hac
    (by
      rw [← predictiveConditionalInfoStatistic_eq_compProd μ f hf]
      exact hfin)
  simpa [predictiveConditionalInfoStatistic_eq_compProd μ f hf] using h

end UEOT.V3.InformationPredictiveCMI
