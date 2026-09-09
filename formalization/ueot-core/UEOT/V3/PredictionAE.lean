import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE

/-! Countable common-null-set and measurable-decoder part of P-PRED-01.
No assertion about existence of conditional laws or a measurable quotient is made. -/
namespace UEOT.V3.PredictionAE
open MeasureTheory ProbabilityTheory

theorem canonical_measurable {H I Y : Type*} [MeasurableSpace H] [MeasurableSpace Y]
    (K : I → Kernel H Y) : Measurable (fun h i => K i h) :=
  measurable_pi_lambda _ (fun i => (K i).measurable)

theorem common_factorization {H I S Y : Type*} [Countable I]
    [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace Y]
    (μ : Measure H) (K : I → Kernel H Y) (s : H → S) (L : I → Kernel S Y)
    (hL : ∀ i, ∀ᵐ h ∂μ, K i h = L i (s h)) :
    ∃ decoder : S → (I → Measure Y), Measurable decoder ∧
      ∀ᵐ h ∂μ, (fun i => K i h) = decoder (s h) := by
  refine ⟨fun z i => L i z, measurable_pi_lambda _ (fun i => (L i).measurable), ?_⟩
  have hc : ∀ᵐ h ∂μ, ∀ i, K i h = L i (s h) := ae_all_iff.mpr hL
  exact hc.mono (fun h hh => funext hh)

theorem transported_decoder_measurable {H I S Y : Type*}
    [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace Y]
    (s : H → S) (hs : Measurable s) (L : I → Kernel S Y) :
    Measurable (fun h i => L i (s h)) :=
  (canonical_measurable L).comp hs

end UEOT.V3.PredictionAE
