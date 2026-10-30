import UEOT.Core.Access
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Original commitment: book31.2 needs a proved carrier/cut algorithm from actual finite response data, not a desired carrier hypergraph.
Existing result: original Access sufficiency/decoder and blocker duality, but no table-derived complete executable frontier.
Premise reduced: compute target-distinguishing observation edges, derive suff iff hitting, and prove actual incremental/pruned enumeration.
Model/witness: finite deterministic obs/target table; generic engine requires only DecidableEq atoms and examines generated candidates only.
Consumer: same-table decoder/minimalCarriers and later explicit physical erasure source; no generic polynomial enumeration claim.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteResponseCarrierFrontier
open UEOT

variable {V : Type*} [DecidableEq V]

/-- Only compare candidates already generated; no ambient powerset input. -/
def minimize (F : Finset (Finset V)) : Finset (Finset V) :=
  F.filter (fun S => ∀ T ∈ F, T ⊆ S → S ⊆ T)

def hit (S E : Finset V) : Prop := (S ∩ E).Nonempty

instance hit_decidable (S E : Finset V) : Decidable (hit S E) := inferInstanceAs (Decidable ((S ∩ E).Nonempty))

def HitsList (es : List (Finset V)) (S : Finset V) : Prop := ∀ E ∈ es, hit S E

/-- Berge frontier extension: retain an already-hitting candidate, otherwise
extend only by atoms in THIS edge. Minimize only this generated family. -/
def expand (F : Finset (Finset V)) (E : Finset V) : Finset (Finset V) :=
  F.biUnion (fun S => if hit S E then {S} else E.image (fun v => insert v S))

def advance (F : Finset (Finset V)) (E : Finset V) : Finset (Finset V) := minimize (expand F E)

/-- Structural recursion on the supplied edge list. Every frontier is finite;
empty edges and constant targets retain their original meanings. -/
def enumerate : List (Finset V) → Finset (Finset V)
  | [] => {∅}
  | E::es => advance (enumerate es) E

@[simp] theorem mem_minimize (F : Finset (Finset V)) (S : Finset V) :
    S ∈ minimize F ↔ S ∈ F ∧ ∀ T ∈ F, T ⊆ S → S ⊆ T := by simp [minimize]

theorem minimize_cover (F : Finset (Finset V)) (S : Finset V) (hS : S ∈ F) :
    ∃ T ∈ minimize F, T ⊆ S := by
  classical
  let A := F.filter (fun T => T ⊆ S)
  obtain ⟨T,hT,hmin⟩ := A.exists_min_image Finset.card ⟨S,by simp [A,hS]⟩
  have ht := Finset.mem_filter.mp hT
  refine ⟨T,(mem_minimize F T).mpr ⟨ht.1,?_⟩,ht.2⟩
  intro U hUF hUT
  have hc : T.card ≤ U.card := hmin U (by simp [A,hUF,hUT.trans ht.2])
  exact (Finset.eq_of_subset_of_card_le hUT hc).symm.subset

theorem minimize_antichain (F : Finset (Finset V)) {S T : Finset V}
    (hS : S ∈ minimize F) (hT : T ∈ minimize F) (hST : S ⊆ T) : S=T :=
  Finset.Subset.antisymm hST (((mem_minimize F T).mp hT).2 S ((mem_minimize F S).mp hS).1 hST)

theorem hit_mono {S T E : Finset V} (hST : S ⊆ T) (h : hit S E) : hit T E := by
  obtain ⟨v,hv⟩ := h
  exact ⟨v,Finset.mem_inter.mpr ⟨hST (Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2⟩⟩

theorem HitsList_mono (es : List (Finset V)) {S T : Finset V} (hST : S ⊆ T) (h : HitsList es S) :
    HitsList es T := fun E hE => hit_mono hST (h E hE)

theorem expand_sound (F : Finset (Finset V)) (es : List (Finset V)) (E : Finset V)
    (hF : ∀ S ∈ F, HitsList es S) (T : Finset V) (hT : T ∈ expand F E) : HitsList (E::es) T := by
  obtain ⟨S,hSF,hTS⟩ := Finset.mem_biUnion.mp hT
  have hs := hF S hSF
  by_cases hh : hit S E
  · simp only [if_pos hh,Finset.mem_singleton] at hTS
    subst T
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hh
    · exact hs B hB
  · rw [if_neg hh] at hTS
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hTS
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ⟨v,Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,hv⟩⟩
    · exact HitsList_mono es (Finset.subset_insert _ _) hs B hB

theorem expand_cover (F : Finset (Finset V)) (E T : Finset V)
    (hT : hit T E) (hF : ∃ S ∈ F, S ⊆ T) : ∃ U ∈ expand F E, U ⊆ T := by
  obtain ⟨S,hSF,hST⟩ := hF
  by_cases hh : hit S E
  · refine ⟨S,Finset.mem_biUnion.mpr ⟨S,hSF,?_⟩,hST⟩
    simp [hh]
  · obtain ⟨v,hv⟩ := hT
    have hv' := Finset.mem_inter.mp hv
    refine ⟨insert v S,Finset.mem_biUnion.mpr ⟨S,hSF,?_⟩,Finset.insert_subset hv'.1 hST⟩
    simp only [if_neg hh]
    exact Finset.mem_image.mpr ⟨v,hv'.2,rfl⟩

theorem enumerate_sound (es : List (Finset V)) (S : Finset V) (hS : S ∈ enumerate es) : HitsList es S := by
  induction es generalizing S with
  | nil => intro E hE; cases hE
  | cons E es ih =>
    have hs : S ∈ expand (enumerate es) E := ((mem_minimize (expand (enumerate es) E) S).mp hS).1
    exact expand_sound _ es E (fun T ht => ih T ht) S hs

theorem enumerate_cover (es : List (Finset V)) (T : Finset V) (hT : HitsList es T) :
    ∃ S ∈ enumerate es, S ⊆ T := by
  induction es with
  | nil => exact ⟨∅,by simp [enumerate],Finset.empty_subset _⟩
  | cons E es ih =>
    obtain ⟨S,hS,hST⟩ := ih (fun B hB => hT B (List.mem_cons_of_mem E hB))
    obtain ⟨U,hU,hUT⟩ := expand_cover (enumerate es) E T (hT E (by simp)) ⟨S,hS,hST⟩
    obtain ⟨W,hW,hWU⟩ := minimize_cover (expand (enumerate es) E) U hU
    exact ⟨W,hW,hWU.trans hUT⟩

theorem enumerate_antichain (es : List (Finset V)) {S T : Finset V}
    (hS : S ∈ enumerate es) (hT : T ∈ enumerate es) (hST : S ⊆ T) : S=T := by
  cases es with
  | nil => simp only [enumerate,Finset.mem_singleton] at hS hT; exact hS.trans hT.symm
  | cons E es => exact minimize_antichain _ hS hT hST

/-- Correctness for the ACTUAL returned frontier; no oracle/model-match field. -/
theorem enumerate_mem_iff (es : List (Finset V)) (S : Finset V) :
    S ∈ enumerate es ↔ UEOT.Finite.Minimal (HitsList es) S := by
  constructor
  · intro hS
    refine ⟨enumerate_sound es S hS,?_⟩
    intro T hTS hT
    obtain ⟨U,hU,hUT⟩ := enumerate_cover es T hT
    have he : U=S := enumerate_antichain es hU hS (hUT.trans hTS)
    exact Finset.Subset.antisymm hTS (he ▸ hUT)
  · intro hS
    obtain ⟨T,hT,hTS⟩ := enumerate_cover es S hS.1
    have he : T=S := hS.2 T hTS (enumerate_sound es T hT)
    exact he ▸ hT

/-- Ordered executable representation retained alongside the finite family.
All traversals are over supplied columns/current generated frontier only. -/
def listMinimize (F : List (Finset V)) : List (Finset V) :=
  (F.filter (fun S => F.all (fun T => decide (T ⊆ S → S ⊆ T)))).dedup

def listExpand (columns : List V) (F : List (Finset V)) (E : Finset V) : List (Finset V) :=
  F.flatMap (fun S => if hit S E then [S] else
    (columns.filter (fun v => v ∈ E)).map (fun v => insert v S))

def listEnumerate (columns : List V) : List (Finset V) → List (Finset V)
  | [] => [∅]
  | E::es => listMinimize (listExpand columns (listEnumerate columns es) E)

/-- Ordered implementation visits each supplied column at most once per old
frontier item; even duplicate column lists cannot invalidate this finite bound. -/
theorem listExpand_length_bound (columns : List V) (F : List (Finset V)) (E : Finset V) :
    (listExpand columns F E).length ≤ F.length*(columns.length+1) := by
  induction F with
  | nil => simp [listExpand]
  | cons S F ih =>
    have hs : (if hit S E then [S] else
        (columns.filter (fun v => v∈E)).map (fun v => insert v S)).length ≤ columns.length+1 := by
      split
      · simp
      · simp only [List.length_map]
        exact (List.length_filter_le _ _).trans (Nat.le_succ _)
    rw [listExpand,List.flatMap_cons,List.length_append,List.length_cons]
    calc
      _ ≤ (columns.length+1)+F.length*(columns.length+1) := Nat.add_le_add hs ih
      _ = _ := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]

/-- Output order is executable and duplicate-free; ties retain the list order
chosen by the native dedup operation, never an ambient Finset ordering. -/
theorem listEnumerate_nodup (columns : List V) (es : List (Finset V)) :
    (listEnumerate columns es).Nodup := by
  cases es with
  | nil => simp [listEnumerate]
  | cons E es => exact List.nodup_dedup _

/-- Explicit one-stage generated-candidate bound. Pruning performs subset
comparisons only inside this generated family, at most its squared cardinality.
This is not a polynomial bound in the whole source size. -/
theorem expand_card_bound (F : Finset (Finset V)) (E : Finset V) :
    (expand F E).card ≤ F.card * (E.card+1) := by
  apply Finset.card_biUnion_le_card_mul
  intro S hS
  by_cases h : hit S E
  · simp [h]
  · simp only [if_neg h]
    exact Finset.card_image_le.trans (Nat.le_succ _)

theorem advance_card_bound (F : Finset (Finset V)) (E : Finset V) :
    (advance F E).card ≤ F.card * (E.card+1) :=
  (Finset.card_filter_le _ _).trans (expand_card_bound F E)

theorem listMinimize_family (F : List (Finset V)) : (listMinimize F).toFinset=minimize F.toFinset := by
  ext S
  simp [listMinimize,minimize,List.all_eq_true,imp_iff_not_or]

theorem listExpand_family (columns : List V) (hc : ∀ v, v ∈ columns) (F : List (Finset V)) (E : Finset V) :
    (listExpand columns F E).toFinset=expand F.toFinset E := by
  ext S
  simp only [List.mem_toFinset,listExpand,List.mem_flatMap,expand,Finset.mem_biUnion]
  constructor
  · rintro ⟨T,hTF,hS⟩
    refine ⟨T,hTF,?_⟩
    by_cases hh : hit T E
    · simpa [hh] using hS
    · simp only [if_neg hh,List.mem_map,List.mem_filter] at hS
      obtain ⟨v,⟨_,hv⟩,he⟩ := hS
      exact (by rw [if_neg hh]; exact Finset.mem_image.mpr ⟨v,of_decide_eq_true hv,he⟩)
  · rintro ⟨T,hTF,hS⟩
    refine ⟨T,hTF,?_⟩
    by_cases hh : hit T E
    · simpa [hh] using hS
    · rw [if_neg hh] at hS ⊢
      obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hS
      exact List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨hc v,by simpa using hv⟩,he⟩

theorem listEnumerate_family (columns : List V) (hc : ∀ v, v ∈ columns) (es : List (Finset V)) :
    (listEnumerate columns es).toFinset=enumerate es := by
  induction es with
  | nil => simp [listEnumerate,enumerate]
  | cons E es ih => rw [listEnumerate,listMinimize_family,listExpand_family columns hc,ih]; rfl

theorem listEnumerate_mem_iff (columns : List V) (hc : ∀ v, v ∈ columns) (es : List (Finset V)) (S : Finset V) :
    S ∈ listEnumerate columns es ↔ UEOT.Finite.Minimal (HitsList es) S := by
  rw [← List.mem_toFinset,listEnumerate_family columns hc,enumerate_mem_iff]

theorem HitsList_original (es : List (Finset V)) (S : Finset V) :
    HitsList es S ↔ UEOT.Blocker.Hits {E | E ∈ es} S := by
  constructor
  · intro h E hE
    obtain ⟨v,hv⟩ := h E hE
    exact ⟨v,(Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2⟩
  · intro h E hE
    obtain ⟨v,hv,hE'⟩ := h E hE
    exact ⟨v,Finset.mem_inter.mpr ⟨hv,hE'⟩⟩

section Table
variable {X Y Z : Type*} [Fintype X] [LinearOrder X] [Fintype V] [DecidableEq Y] [DecidableEq Z]

def rowList : List X := (Finset.univ : Finset X).sort (· ≤ ·)

@[simp] theorem mem_rowList (x : X) : x ∈ (rowList : List X) := by simp [rowList,Finset.mem_sort]

/-- This edge is COMPUTED from actual observation-table entries. -/
def differenceEdge (obs : X → V → Y) (x y : X) : Finset V :=
  Finset.univ.filter (fun v => obs x v ≠ obs y v)

def distinguishingEdges (obs : X → V → Y) (target : X → Z) : List (Finset V) :=
  (rowList : List X).flatMap (fun x => ((rowList : List X).filter (fun y => target x ≠ target y)).map
    (fun y => differenceEdge obs x y))

omit [DecidableEq V] in
theorem mem_distinguishingEdges (obs : X → V → Y) (target : X → Z) (E : Finset V) :
    E ∈ distinguishingEdges obs target ↔ ∃ x y, target x ≠ target y ∧ differenceEdge obs x y=E := by
  simp [distinguishingEdges,List.mem_flatMap,List.mem_map]

/-- Source table DERIVES the hitting characterization of access sufficiency. -/
theorem sufficient_iff_hits (obs : X → V → Y) (target : X → Z) (S : Finset V) :
    UEOT.Access.Sufficient obs target S ↔ HitsList (distinguishingEdges obs target) S := by
  classical
  constructor
  · intro hs E hE
    obtain ⟨x,y,hxy,rfl⟩ := (mem_distinguishingEdges obs target E).mp hE
    by_contra hn
    apply hxy
    apply hs x y
    intro v hv
    by_contra hneq
    exact hn ⟨v,Finset.mem_inter.mpr ⟨hv,by simp [differenceEdge,hneq]⟩⟩
  · intro hh x y ha
    by_contra hxy
    have he : differenceEdge obs x y ∈ distinguishingEdges obs target :=
      (mem_distinguishingEdges obs target _).mpr ⟨x,y,hxy,rfl⟩
    obtain ⟨v,hv⟩ := hh _ he
    have hobs : obs x v ≠ obs y v := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
    exact hobs (ha v (Finset.mem_inter.mp hv).1)

def carriers (obs : X → V → Y) (target : X → Z) : Finset (Finset V) :=
  enumerate (distinguishingEdges obs target)

theorem carriers_iff_original (obs : X → V → Y) (target : X → Z) (S : Finset V) :
    S ∈ carriers obs target ↔ S ∈ UEOT.Access.minimalCarriers obs target := by
  rw [carriers,enumerate_mem_iff]
  have he : HitsList (distinguishingEdges obs target)=UEOT.Access.Sufficient obs target :=
    funext (fun T => propext (sufficient_iff_hits obs target T).symm)
  rw [he]
  rfl

/-- Computed off-range rejection; on every actual source row, a sufficient
returned carrier returns the SAME target. No choice decoder is input. -/
def decode (obs : X → V → Y) (target : X → Z) (S : Finset V)
    (r : {v // v ∈ S} → Y) : Option Z :=
  ((rowList : List X).find? (fun x => decide (∀ v (hv : v ∈ S), obs x v=r ⟨v,hv⟩))).map target

theorem decode_returned (obs : X → V → Y) (target : X → Z) (S : Finset V)
    (hS : S ∈ carriers obs target) (x : X) :
    decode obs target S (UEOT.Access.readout obs S x)=some (target x) := by
  have hs : UEOT.Access.Sufficient obs target S := ((carriers_iff_original obs target S).mp hS).1
  have hm : ((rowList : List X).find? (fun y => decide
      (∀ v (hv : v ∈ S), obs y v=UEOT.Access.readout obs S x ⟨v,hv⟩))).isSome=true := by
    apply List.find?_isSome.mpr
    exact ⟨x,mem_rowList x,by simp [UEOT.Access.readout]⟩
  unfold decode
  cases he : (rowList : List X).find? (fun y => decide
      (∀ v (hv : v ∈ S), obs y v=UEOT.Access.readout obs S x ⟨v,hv⟩)) with
  | none => simp [he] at hm
  | some y =>
    have hh := List.find?_some he
    have ha : ∀ v (hv : v ∈ S), obs y v=UEOT.Access.readout obs S x ⟨v,hv⟩ := of_decide_eq_true hh
    exact congrArg some (hs y x ha)

/-- BOTH carrier and cut lists are computed from the SAME source table. -/
def carrierList (columns : List V) (obs : X → V → Y) (target : X → Z) : List (Finset V) :=
  listEnumerate columns (distinguishingEdges obs target)

def cutList (columns : List V) (obs : X → V → Y) (target : X → Z) : List (Finset V) :=
  listEnumerate columns (carrierList columns obs target)

theorem carrierList_iff_original (columns : List V) (hc : ∀ v, v ∈ columns)
    (obs : X → V → Y) (target : X → Z) (S : Finset V) :
    S ∈ carrierList columns obs target ↔ S ∈ UEOT.Access.minimalCarriers obs target := by
  rw [carrierList,← List.mem_toFinset,listEnumerate_family columns hc]
  exact carriers_iff_original obs target S

theorem cutList_iff_original (columns : List V) (hc : ∀ v, v ∈ columns)
    (obs : X → V → Y) (target : X → Z) (D : Finset V) :
    D ∈ cutList columns obs target ↔ D ∈ UEOT.Blocker.blocker (UEOT.Access.minimalCarriers obs target) := by
  rw [cutList,listEnumerate_mem_iff columns hc]
  have hf : {E | E ∈ carrierList columns obs target}=UEOT.Access.minimalCarriers obs target :=
    Set.ext (fun E => carrierList_iff_original columns hc obs target E)
  have he : HitsList (carrierList columns obs target)=UEOT.Blocker.Hits (UEOT.Access.minimalCarriers obs target) := by
    funext S
    exact propext ((HitsList_original _ S).trans (by rw [hf]))
  rw [he]
  rfl

end Table
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteResponseCarrierFrontier
