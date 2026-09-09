import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

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


/-! ## A measurable almost-everywhere factor preorder

This packages the exact "embedding factor modulo a common null set" relation
needed by P-PRED-01.  It is intentionally weaker than declaring equality of
completed sigma-algebras; that bridge is proved separately.
-/

def AEFactors {H S T : Type*} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure H) (f : H → T) (g : H → S) : Prop :=
  ∃ d : S → T, Measurable d ∧ ∀ᵐ h ∂μ, f h = d (g h)

theorem aeFactors_refl {H T : Type*} [MeasurableSpace H] [MeasurableSpace T]
    (μ : Measure H) (f : H → T) :
    AEFactors μ f f := by
  refine ⟨id, measurable_id, ?_⟩
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem aeFactors_trans {H S T U : Type*}
    [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
    (μ : Measure H) {f : H → U} {g : H → T} {h : H → S}
    (hfg : AEFactors μ f g) (hgh : AEFactors μ g h) :
    AEFactors μ f h := by
  rcases hfg with ⟨d, hd, hdf⟩
  rcases hgh with ⟨e, he, heg⟩
  refine ⟨d ∘ e, hd.comp he, ?_⟩
  exact (hdf.and heg).mono (fun x hx => by rw [hx.1, hx.2]; rfl)

theorem canonical_ae_minimal {H I S Y : Type*} [Countable I]
    [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace Y]
    (μ : Measure H) (K : I → Kernel H Y) (s : H → S) (L : I → Kernel S Y)
    (hL : ∀ i, ∀ᵐ h ∂μ, K i h = L i (s h)) :
    AEFactors μ (fun h i => K i h) s := by
  rcases common_factorization μ K s L hL with ⟨d, hd, hEq⟩
  exact ⟨d, hd, hEq⟩

theorem coordinate_ae_sufficient {H I Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (μ : Measure H) (K : I → Kernel H Y) (i : I) :
    AEFactors μ (fun h => K i h) (fun h j => K j h) := by
  refine ⟨fun c => c i, measurable_pi_apply i, ?_⟩
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem canonical_aemeasurable_of_factorization {H I S Y : Type*} [Countable I]
    [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace Y]
    (μ : Measure H) (K : I → Kernel H Y) (s : H → S) (hs : Measurable s)
    (L : I → Kernel S Y)
    (hL : ∀ i, ∀ᵐ h ∂μ, K i h = L i (s h)) :
    AEMeasurable (fun h i => K i h) μ := by
  rcases common_factorization μ K s L hL with ⟨d, hd, hEq⟩
  exact ⟨d ∘ s, hd.comp hs, hEq⟩


/-! `AESigmaLE μ f g` means that an almost-everywhere version of `f`
generates no more sigma-information than `g`. This is the explicit mod-null
sigma-factor order used for the minimal-embedding clause of P-PRED-01. -/
def AESigmaLE {H S T : Type*} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure H) (f : H → T) (g : H → S) : Prop :=
  ∃ f' : H → T, (∀ᵐ h ∂μ, f h = f' h) ∧
    MeasurableSpace.comap f' inferInstance ≤
      MeasurableSpace.comap g inferInstance

theorem aeFactors_sigmaLE {H S T : Type*}
    [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure H) {f : H → T} {g : H → S}
    (hfg : AEFactors μ f g) :
    AESigmaLE μ f g := by
  rcases hfg with ⟨d, hd, hEq⟩
  refine ⟨d ∘ g, ?_, ?_⟩
  · exact hEq
  · exact MeasurableSpace.comap_le_comap_of_eq_comp d hd rfl

theorem canonical_ae_sigma_minimal {H I S Y : Type*} [Countable I]
    [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace Y]
    (μ : Measure H) (K : I → Kernel H Y) (s : H → S) (L : I → Kernel S Y)
    (hL : ∀ i, ∀ᵐ h ∂μ, K i h = L i (s h)) :
    AESigmaLE μ (fun h i => K i h) s :=
  aeFactors_sigmaLE μ (canonical_ae_minimal μ K s L hL)

theorem coordinate_ae_sigma_le_canonical {H I Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (μ : Measure H) (K : I → Kernel H Y) (i : I) :
    AESigmaLE μ (fun h => K i h) (fun h j => K j h) :=
  aeFactors_sigmaLE μ (coordinate_ae_sufficient μ K i)


/-! ## Canonical state is itself protocol-sufficient

For each protocol coordinate, evaluation of the canonical measure-valued state
is itself a measurable kernel. Thus the original history kernel is recovered
exactly, not merely almost everywhere, from the canonical state.
-/

def coordinateKernel {I Y : Type*} [MeasurableSpace Y] (i : I) :
    Kernel (I → Measure Y) Y where
  toFun c := c i
  measurable' := measurable_pi_apply i

theorem coordinateKernel_apply {I Y : Type*} [MeasurableSpace Y]
    (i : I) (c : I → Measure Y) :
    coordinateKernel i c = c i := rfl

theorem canonical_coordinate_sufficient {H I Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (K : I → Kernel H Y) (i : I) :
    ∀ h, K i h = coordinateKernel i (fun j => K j h) := by
  intro h
  rfl

theorem canonical_kernel_sufficient {H I Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (K : I → Kernel H Y) :
    ∀ i, ∃ L : Kernel (I → Measure Y) Y,
      ∀ h, K i h = L (fun j => K j h) := by
  intro i
  exact ⟨coordinateKernel i, canonical_coordinate_sufficient K i⟩


/-! ## Conditional-future-law identification

The next theorem is the tower-property step used in the source proof:
a real-valued quantity that is already a measurable function of a statistic is
fixed by conditional expectation onto the sigma-algebra generated by that
statistic.
-/

theorem condExp_eq_of_exact_factor {H S : Type*}
    [MeasurableSpace H] [MeasurableSpace S]
    (μ : Measure H) [IsFiniteMeasure μ]
    (s : H → S) (hs : Measurable s)
    (f : H → ℝ) (d : S → ℝ)
    (hd : StronglyMeasurable d)
    (hfd : ∀ h, f h = d (s h))
    (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap s inferInstance] = f := by
  let mS : MeasurableSpace H := MeasurableSpace.comap s inferInstance
  have hs_comap : @Measurable H S mS inferInstance s :=
    measurable_iff_comap_le.mpr le_rfl
  have hcomp : StronglyMeasurable[mS] (d ∘ s) :=
    hd.comp_measurable hs_comap
  have heq : f = d ∘ s := funext hfd
  rw [heq]
  exact condExp_of_stronglyMeasurable hs.comap_le hcomp (heq ▸ hf)

theorem canonical_event_condExp {H I Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (K : I → Kernel H Y)
    (hK : ∀ i h, IsProbabilityMeasure (K i h))
    (i : I) {B : Set Y} (hB : MeasurableSet B) :
    μ[(fun h => (K i h).real B) |
      MeasurableSpace.comap (fun h j => K j h) inferInstance] =
      (fun h => (K i h).real B) := by
  let C : H → (I → Measure Y) := fun h j => K j h
  let d : (I → Measure Y) → ℝ := fun c => (c i).real B
  have hC : Measurable C := canonical_measurable K
  have hd_meas : Measurable d := by
    exact ENNReal.measurable_toReal.comp
      ((Measure.measurable_coe hB).comp (measurable_pi_apply i))
  have hf_meas : Measurable (fun h => (K i h).real B) := by
    exact ENNReal.measurable_toReal.comp ((K i).measurable_coe hB)
  have hf_int : Integrable (fun h => (K i h).real B) μ := by
    apply Integrable.of_bound hf_meas.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun h => by
      letI : IsProbabilityMeasure (K i h) := hK i h
      have hnonneg : 0 ≤ (K i h).real B := measureReal_nonneg
      have hle : (K i h).real B ≤ 1 := measureReal_le_one
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle)
  simpa [C, d] using
    condExp_eq_of_exact_factor μ C hC
      (fun h => (K i h).real B) d hd_meas.stronglyMeasurable
      (fun _ => rfl) hf_int

end UEOT.V3.PredictionAE
