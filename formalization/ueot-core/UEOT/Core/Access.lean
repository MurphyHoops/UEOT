import UEOT.Core.Finite
import UEOT.Core.Prediction
import UEOT.Core.Blocker

/-! Pointwise access sufficiency on finite sets of coordinates (P-CAR-01).
Readouts are restricted to their realized range when constructing a decoder. -/

namespace UEOT.Access

universe u v w z
variable {V : Type u} {H : Type v} {Y : Type w} {Z : Type z}

def AgreeOn (read : H → V → Y) (S : Finset V) (x y : H) : Prop :=
  ∀ v ∈ S, read x v = read y v

def Sufficient (read : H → V → Y) (target : H → Z) (S : Finset V) : Prop :=
  ∀ x y, AgreeOn read S x y → target x = target y

theorem sufficient_mono {read : H → V → Y} {target : H → Z} {S T : Finset V}
    (hST : S ⊆ T) (hS : Sufficient read target S) : Sufficient read target T := by
  intro x y h
  exact hS x y (fun v hv => h v (hST hv))

def readout (read : H → V → Y) (S : Finset V) (h : H) : {v // v ∈ S} → Y :=
  fun v => read h v.val

def rangeReadout (read : H → V → Y) (S : Finset V) (h : H) :
    {r : {v // v ∈ S} → Y // ∃ x, readout read S x = r} :=
  ⟨readout read S h, h, rfl⟩

theorem agree_iff_readout_eq (read : H → V → Y) (S : Finset V) (x y : H) :
    AgreeOn read S x y ↔ readout read S x = readout read S y := by
  constructor
  · intro h
    exact funext (fun v => h v.val v.property)
  · intro h v hv
    exact congrFun h ⟨v, hv⟩

theorem sufficient_iff_factors_range (read : H → V → Y) (target : H → Z)
    (S : Finset V) : Sufficient read target S ↔ FactorsThrough target (rangeReadout read S) := by
  classical
  constructor
  · intro h
    refine ⟨fun r => target (Classical.choose r.property), ?_⟩
    intro x
    apply h
    apply (agree_iff_readout_eq read S _ _).2
    exact (Classical.choose_spec (rangeReadout read S x).property).symm
  · intro h x y e
    apply factorsThrough_fiber h
    apply Subtype.ext
    exact (agree_iff_readout_eq read S x y).1 e

theorem sufficient_iff_contains_minimal (read : H → V → Y) (target : H → Z)
    (S : Finset V) :
    Sufficient read target S ↔
      ∃ M, M ⊆ S ∧ Finite.Minimal (Sufficient read target) M := by
  constructor
  · exact Finite.exists_minimal_subset _ S
  · rintro ⟨M, hMS, hM⟩
    exact sufficient_mono hMS hM.1

def minimalCarriers (read : H → V → Y) (target : H → Z) : Set (Finset V) :=
  {M | Finite.Minimal (Sufficient read target) M}

theorem minimalCarriers_isClutter (read : H → V → Y) (target : H → Z) :
    Blocker.IsClutter (minimalCarriers read target) := by
  intro S hS T hT hST
  exact Finite.minimal_antichain _ hS hT hST

theorem erasure_survives_iff [DecidableEq V] [Fintype V] (read : H → V → Y) (target : H → Z)
    (D : Finset V) :
    Sufficient read target (Finset.univ \ D) ↔
      ∃ M ∈ minimalCarriers read target, ∀ v ∈ M, v ∉ D := by
  classical
  rw [sufficient_iff_contains_minimal]
  constructor
  · rintro ⟨M, hMD, hM⟩
    exact ⟨M, hM, fun v hv => (Finset.mem_sdiff.mp (hMD hv)).2⟩
  · rintro ⟨M, hM, hMD⟩
    exact ⟨M, fun v hv => by simp [hMD v hv], hM⟩

theorem erasure_failure_iff [DecidableEq V] [Fintype V] (read : H → V → Y) (target : H → Z)
    (D : Finset V) :
    (¬ Sufficient read target (Finset.univ \ D)) ↔
      Blocker.Hits (minimalCarriers read target) D := by
  rw [erasure_survives_iff]
  exact Blocker.access_failure_iff_hits _ _

theorem minimal_erasure_iff_blocker [DecidableEq V] [Fintype V]
    (read : H → V → Y) (target : H → Z) (D : Finset V) :
    Finite.Minimal (fun E => ¬ Sufficient read target (Finset.univ \ E)) D ↔
      D ∈ Blocker.blocker (minimalCarriers read target) := by
  have h : (fun E => ¬ Sufficient read target (Finset.univ \ E)) =
      Blocker.Hits (minimalCarriers read target) := by
    funext E
    exact propext (erasure_failure_iff read target E)
  rw [h]
  rfl

end UEOT.Access
