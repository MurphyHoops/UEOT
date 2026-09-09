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

end UEOT.V3.PredictionAE
