import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
P-PRED-02: target pushforward and protocol refinement.

The source statement has three parts:
1. measurable target postprocessing pushes every canonical future kernel forward;
2. restricting the protocol family can only reduce the generated sigma-factor;
3. a countable increasing union generates the supremum of the stage sigma-factors.

The final theorem below is slightly stronger than (3): monotonicity of the stage
families is not needed if their coordinate images cover the full protocol family.
-/

namespace UEOT.V3.PredictionRefinement

open MeasureTheory ProbabilityTheory

theorem canonical_target_pushforward
    {H I Y₁ Y₂ : Type*}
    [MeasurableSpace H] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
    (K : I → Kernel H Y₂) (T : Y₂ → Y₁) (hT : Measurable T) :
    (fun h i => (Kernel.map (K i) T) h) =
      (fun h i => (K i h).map T) := by
  funext h i
  exact Kernel.map_apply (K i) hT h

theorem protocol_sigma_mono
    {H I₁ I₂ Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (K : I₂ → Kernel H Y) (r : I₁ → I₂) :
    MeasurableSpace.comap (fun h i => K (r i) h) inferInstance ≤
      MeasurableSpace.comap (fun h i => K i h) inferInstance := by
  rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro i
  exact le_iSup_of_le (r i) le_rfl

theorem protocol_sigma_eq_iSup_of_cover
    {H J Y : Type*} {I : ℕ → Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (K : J → Kernel H Y)
    (r : ∀ n, I n → J)
    (cover : ∀ j, ∃ n i, r n i = j) :
    MeasurableSpace.comap (fun h j => K j h) inferInstance =
      ⨆ n, MeasurableSpace.comap (fun h i => K (r n i) h) inferInstance := by
  apply le_antisymm
  · rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro j
    rcases cover j with ⟨n, i, hri⟩
    subst j
    refine le_iSup_of_le n ?_
    rw [MeasurableSpace.comap_process_pi]
    exact le_iSup_of_le i le_rfl
  · apply iSup_le
    intro n
    exact protocol_sigma_mono K (r n)


theorem protocol_subset_sigma_mono
    {H I Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (K : I → Kernel H Y) {A B : Set I} (hAB : A ⊆ B) :
    MeasurableSpace.comap (fun h i : A => K i.1 h) inferInstance ≤
      MeasurableSpace.comap (fun h i : B => K i.1 h) inferInstance := by
  let r : A → B := fun i => ⟨i.1, hAB i.2⟩
  simpa [r] using
    protocol_sigma_mono (K := fun i : B => K i.1) r

theorem protocol_iUnion_sigma
    {H I Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (K : I → Kernel H Y) (A : ℕ → Set I) :
    MeasurableSpace.comap
        (fun h i : {x : I // x ∈ ⋃ n, A n} => K i.1 h) inferInstance =
      ⨆ n, MeasurableSpace.comap
        (fun h i : {x : I // x ∈ A n} => K i.1 h) inferInstance := by
  let r : ∀ n, {x : I // x ∈ A n} → {x : I // x ∈ ⋃ n, A n} :=
    fun n i => ⟨i.1, Set.mem_iUnion.2 ⟨n, i.2⟩⟩
  have cover :
      ∀ j : {x : I // x ∈ ⋃ n, A n},
        ∃ n i, r n i = j := by
    intro j
    rcases Set.mem_iUnion.1 j.2 with ⟨n, hn⟩
    refine ⟨n, ⟨j.1, hn⟩, ?_⟩
    apply Subtype.ext
    rfl
  simpa [r] using
    protocol_sigma_eq_iSup_of_cover
      (K := fun j : {x : I // x ∈ ⋃ n, A n} => K j.1) r cover

end UEOT.V3.PredictionRefinement
