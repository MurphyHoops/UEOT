import UEOT.V3.PredictionAE

/-!
# Dependent future spaces for P-PRED-01

The v3 source allows each protocol i to have its own standard-Borel future
space Y i.  Once measurable response kernels are already supplied, the
factorization/minimality argument only needs the measurable structures, so the
formal theorem is slightly more general than the source.
-/

namespace UEOT.V3.PredictionDependent

open MeasureTheory ProbabilityTheory

universe uH uI uS uY

variable {H : Type uH} {I : Type uI} {S : Type uS}
variable {Y : I → Type uY}
variable [MeasurableSpace H] [MeasurableSpace S]
variable [∀ i, MeasurableSpace (Y i)]

theorem canonical_measurable
    (K : (i : I) → Kernel H (Y i)) :
    Measurable (fun h i => K i h) :=
  measurable_pi_lambda _ (fun i => (K i).measurable)

theorem common_factorization [Countable I]
    (μ : Measure H)
    (K : (i : I) → Kernel H (Y i))
    (s : H → S)
    (L : (i : I) → Kernel S (Y i))
    (hL : ∀ i, ∀ᵐ h ∂μ, K i h = L i (s h)) :
    ∃ decoder : S → (∀ i, Measure (Y i)), Measurable decoder ∧
      ∀ᵐ h ∂μ, (fun i => K i h) = decoder (s h) := by
  refine ⟨fun z i => L i z, measurable_pi_lambda _ (fun i => (L i).measurable), ?_⟩
  have hc : ∀ᵐ h ∂μ, ∀ i, K i h = L i (s h) := ae_all_iff.mpr hL
  exact hc.mono (fun h hh => funext hh)

theorem canonical_ae_minimal [Countable I]
    (μ : Measure H)
    (K : (i : I) → Kernel H (Y i))
    (s : H → S)
    (L : (i : I) → Kernel S (Y i))
    (hL : ∀ i, ∀ᵐ h ∂μ, K i h = L i (s h)) :
    PredictionAE.AEFactors μ (fun h i => K i h) s := by
  rcases common_factorization μ K s L hL with ⟨d, hd, hEq⟩
  exact ⟨d, hd, hEq⟩

theorem canonical_ae_sigma_minimal [Countable I]
    (μ : Measure H)
    (K : (i : I) → Kernel H (Y i))
    (s : H → S)
    (L : (i : I) → Kernel S (Y i))
    (hL : ∀ i, ∀ᵐ h ∂μ, K i h = L i (s h)) :
    PredictionAE.AESigmaLE μ (fun h i => K i h) s :=
  PredictionAE.aeFactors_sigmaLE μ
    (canonical_ae_minimal μ K s L hL)

def coordinateKernel (i : I) :
    Kernel (∀ j, Measure (Y j)) (Y i) where
  toFun c := c i
  measurable' := measurable_pi_apply i

theorem coordinateKernel_apply (i : I) (c : ∀ j, Measure (Y j)) :
    coordinateKernel i c = c i := rfl

theorem canonical_kernel_sufficient
    (K : (i : I) → Kernel H (Y i)) :
    ∀ i, ∃ L : Kernel (∀ j, Measure (Y j)) (Y i),
      ∀ h, K i h = L (fun j => K j h) := by
  intro i
  exact ⟨coordinateKernel i, fun _ => rfl⟩

theorem canonical_event_condExp
    (μ : Measure H) [IsProbabilityMeasure μ]
    (K : (i : I) → Kernel H (Y i))
    (hK : ∀ i h, IsProbabilityMeasure (K i h))
    (i : I) {B : Set (Y i)} (hB : MeasurableSet B) :
    μ[(fun h => (K i h).real B) |
      MeasurableSpace.comap (fun h j => K j h) inferInstance] =
      (fun h => (K i h).real B) := by
  let C : H → (∀ j, Measure (Y j)) := fun h j => K j h
  let d : (∀ j, Measure (Y j)) → ℝ := fun c => (c i).real B
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
    PredictionAE.condExp_eq_of_exact_factor μ C hC
      (fun h => (K i h).real B) d hd_meas.stronglyMeasurable
      (fun _ => rfl) hf_int

end UEOT.V3.PredictionDependent
