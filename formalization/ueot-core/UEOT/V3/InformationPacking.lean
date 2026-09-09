import UEOT.V3.TotalVariation
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# P-INFO-05 foundation — TV packing obstruction

The source omission/packing theorem is metric before it is information-theoretic:
if two true predictive laws are separated by total variation but one
representation forces a common decoder law, at least one prediction error is
half the true separation.  This module proves that source core directly from
the event-supremum TV definition.
-/

namespace UEOT.V3.InformationPacking

open MeasureTheory
open UEOT.V3.TotalVariation

universe uY uH uS

variable {Y : Type uY} [MeasurableSpace Y]

theorem tvDist_symm
    (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = tvDist ν μ := by
  unfold tvDist
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, by rw [abs_sub_comm]⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, by rw [abs_sub_comm]⟩

theorem tvDist_triangle
    (μ ρ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ tvDist μ ρ + tvDist ρ ν := by
  change sSup (tvEventSet μ ν) ≤ tvDist μ ρ + tvDist ρ ν
  refine csSup_le (tvEventSet_nonempty μ ν) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have htri :
      |μ.real A - ν.real A| ≤
        |μ.real A - ρ.real A| + |ρ.real A - ν.real A| := by
    calc
      |μ.real A - ν.real A| =
          |(μ.real A - ρ.real A) + (ρ.real A - ν.real A)| := by
            congr 1
            ring
      _ ≤ |μ.real A - ρ.real A| + |ρ.real A - ν.real A| :=
        abs_add_le _ _
  have h₁ := tvEvent_le μ ρ A hA
  have h₂ := tvEvent_le ρ ν A hA
  exact htri.trans (add_le_add h₁ h₂)

/-- If one decoder law is used for two true laws, one of the two TV errors is
at least half their separation. -/
theorem common_decoder_half_distance
    (μ ν q : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure q] :
    tvDist μ ν / 2 ≤ max (tvDist μ q) (tvDist ν q) := by
  have htri := tvDist_triangle μ q ν
  have hsym : tvDist q ν = tvDist ν q := tvDist_symm q ν
  rw [hsym] at htri
  have h₁ : tvDist μ q ≤ max (tvDist μ q) (tvDist ν q) :=
    le_max_left _ _
  have h₂ : tvDist ν q ≤ max (tvDist μ q) (tvDist ν q) :=
    le_max_right _ _
  linarith

/-- Source-facing P-INFO-05 first clause: histories merged by the same
representation value necessarily share one decoder law, hence incur the
half-separation obstruction. -/
theorem merged_histories_decoder_lower_bound
    {H : Type uH} {S : Type uS}
    (K : H → Measure Y) (R : H → S) (decode : S → Measure Y)
    (hK : ∀ h, IsProbabilityMeasure (K h))
    (hdecode : ∀ s, IsProbabilityMeasure (decode s))
    {h₁ h₂ : H} (hmerge : R h₁ = R h₂) :
    tvDist (K h₁) (K h₂) / 2 ≤
      max (tvDist (K h₁) (decode (R h₁)))
        (tvDist (K h₂) (decode (R h₂))) := by
  letI : IsProbabilityMeasure (K h₁) := hK h₁
  letI : IsProbabilityMeasure (K h₂) := hK h₂
  letI : IsProbabilityMeasure (decode (R h₁)) := hdecode (R h₁)
  rw [hmerge]
  exact common_decoder_half_distance (K h₁) (K h₂) (decode (R h₂))


/-- If every history in a set is decoded within `ε` in TV and all distinct
true response laws are separated by more than `2ε`, the representation must
be injective on that set.  This is the pigeonhole core of the second clause of
P-INFO-05. -/
theorem packing_forces_injective
    {H : Type uH} {S : Type uS}
    (K : H → Measure Y) (R : H → S) (decode : S → Measure Y)
    (hK : ∀ h, IsProbabilityMeasure (K h))
    (hdecode : ∀ s, IsProbabilityMeasure (decode s))
    (A : Set H) (ε : ℝ)
    (hsep : ∀ ⦃h₁⦄, h₁ ∈ A → ∀ ⦃h₂⦄, h₂ ∈ A →
      h₁ ≠ h₂ → 2 * ε < tvDist (K h₁) (K h₂))
    (herr : ∀ h ∈ A, tvDist (K h) (decode (R h)) ≤ ε) :
    Set.InjOn R A := by
  intro h₁ hh₁ h₂ hh₂ hR
  by_contra hne
  have hlower :=
    merged_histories_decoder_lower_bound K R decode hK hdecode hR
  have hmax :
      max (tvDist (K h₁) (decode (R h₁)))
        (tvDist (K h₂) (decode (R h₂))) ≤ ε :=
    max_le (herr h₁ hh₁) (herr h₂ hh₂)
  have hhalf : tvDist (K h₁) (K h₂) / 2 ≤ ε :=
    hlower.trans hmax
  have hs := hsep hh₁ hh₂ hne
  linarith

/-- Finite-cardinality form of the packing obstruction, stated with
noncomputable set cardinality so that no decidable-equality structure is added
to the representation space. -/
theorem packing_ncard_image
    {H : Type uH} {S : Type uS}
    (K : H → Measure Y) (R : H → S) (decode : S → Measure Y)
    (hK : ∀ h, IsProbabilityMeasure (K h))
    (hdecode : ∀ s, IsProbabilityMeasure (decode s))
    (F : Finset H) (ε : ℝ)
    (hsep : ∀ ⦃h₁⦄, h₁ ∈ F → ∀ ⦃h₂⦄, h₂ ∈ F →
      h₁ ≠ h₂ → 2 * ε < tvDist (K h₁) (K h₂))
    (herr : ∀ h ∈ F, tvDist (K h) (decode (R h)) ≤ ε) :
    Set.ncard (R '' (F : Set H)) = F.card := by
  have hinj : Set.InjOn R (F : Set H) :=
    packing_forces_injective K R decode hK hdecode
      (A := (F : Set H)) ε
      (by simpa using hsep)
      (by simpa using herr)
  rw [hinj.ncard_image, Set.ncard_coe_finset]

end UEOT.V3.InformationPacking
