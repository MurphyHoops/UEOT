import UEOT.Core.Blocker
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Order.Filter.Basic

/-! P-CAR-01/02 for arbitrary consistent measurable readouts.
Use F = Filter.principal Set.univ for pointwise equality, or F = ae μ for
the common reference measure's almost-everywhere equality. -/
namespace UEOT.V3.Access

def FactorsAt {H Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (F : Filter H) (target : H → Z) (read : H → Y) : Prop :=
  ∃ d : Y → Z, Measurable d ∧ ∀ᶠ h in F, target h = d (read h)

theorem factorsAt_trans {H X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (F : Filter H) {f : H → Z} {g : H → Y} {h : H → X}
    (hfg : FactorsAt F f g) (hgh : FactorsAt F g h) : FactorsAt F f h := by
  obtain ⟨d, hd, he⟩ := hfg
  obtain ⟨e, hm, hf⟩ := hgh
  refine ⟨d ∘ e, hd.comp hm, ?_⟩
  exact (he.and hf).mono (fun x hx => by rw [hx.1, hx.2]; rfl)

theorem sufficient_mono {V H Z : Type*} [MeasurableSpace Z]
    (R : Finset V → Type*) [∀ S, MeasurableSpace (R S)]
    (F : Filter H) (target : H → Z) (read : ∀ S, H → R S)
    (consistent : ∀ S T, S ⊆ T → FactorsAt F (read S) (read T))
    {S T : Finset V} (hST : S ⊆ T) (hS : FactorsAt F target (read S)) :
    FactorsAt F target (read T) := factorsAt_trans F hS (consistent S T hST)

theorem contains_minimal {V H Z : Type*} [MeasurableSpace Z]
    (R : Finset V → Type*) [∀ S, MeasurableSpace (R S)]
    (F : Filter H) (target : H → Z) (read : ∀ S, H → R S)
    (consistent : ∀ S T, S ⊆ T → FactorsAt F (read S) (read T)) (S : Finset V) :
    FactorsAt F target (read S) ↔
      ∃ M, M ⊆ S ∧ Finite.Minimal (fun T => FactorsAt F target (read T)) M := by
  constructor
  · exact Finite.exists_minimal_subset (fun T => FactorsAt F target (read T)) S
  · rintro ⟨M, hMS, hM⟩
    exact sufficient_mono R F target read consistent hMS hM.1

theorem erasure_survives {V H Z : Type*} [DecidableEq V] [Fintype V]
    [MeasurableSpace Z] (R : Finset V → Type*) [∀ S, MeasurableSpace (R S)]
    (F : Filter H) (target : H → Z) (read : ∀ S, H → R S)
    (consistent : ∀ S T, S ⊆ T → FactorsAt F (read S) (read T)) (D : Finset V) :
    FactorsAt F target (read (Finset.univ \ D)) ↔
      ∃ M, Finite.Minimal (fun T => FactorsAt F target (read T)) M ∧
        ∀ v ∈ M, v ∉ D := by
  rw [contains_minimal R F target read consistent]
  constructor
  · rintro ⟨M, hMD, hM⟩
    exact ⟨M, hM, fun v hv => (Finset.mem_sdiff.mp (hMD hv)).2⟩
  · rintro ⟨M, hM, hMD⟩
    exact ⟨M, fun v hv => by simp [hMD v hv], hM⟩

theorem erasure_failure {V H Z : Type*} [DecidableEq V] [Fintype V]
    [MeasurableSpace Z] (R : Finset V → Type*) [∀ S, MeasurableSpace (R S)]
    (F : Filter H) (target : H → Z) (read : ∀ S, H → R S)
    (consistent : ∀ S T, S ⊆ T → FactorsAt F (read S) (read T)) (D : Finset V) :
    (¬ FactorsAt F target (read (Finset.univ \ D))) ↔
      Blocker.Hits {M | Finite.Minimal (fun T => FactorsAt F target (read T)) M} D := by
  rw [erasure_survives R F target read consistent]
  exact Blocker.access_failure_iff_hits _ _

theorem minimal_erasure {V H Z : Type*} [DecidableEq V] [Fintype V]
    [MeasurableSpace Z] (R : Finset V → Type*) [∀ S, MeasurableSpace (R S)]
    (F : Filter H) (target : H → Z) (read : ∀ S, H → R S)
    (consistent : ∀ S T, S ⊆ T → FactorsAt F (read S) (read T)) (D : Finset V) :
    Finite.Minimal (fun E => ¬ FactorsAt F target (read (Finset.univ \ E))) D ↔
      D ∈ Blocker.blocker {M | Finite.Minimal (fun T => FactorsAt F target (read T)) M} := by
  have h : (fun E => ¬ FactorsAt F target (read (Finset.univ \ E))) =
      Blocker.Hits {M | Finite.Minimal (fun T => FactorsAt F target (read T)) M} := by
    funext E
    exact propext (erasure_failure R F target read consistent E)
  rw [h]
  rfl

end UEOT.V3.Access
