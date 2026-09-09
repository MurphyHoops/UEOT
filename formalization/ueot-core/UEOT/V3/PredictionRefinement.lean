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

end UEOT.V3.PredictionRefinement
