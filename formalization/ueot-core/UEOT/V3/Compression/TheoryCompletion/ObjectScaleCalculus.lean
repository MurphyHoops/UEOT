import UEOT.V3.Compression.TheoryCompletion.Scale

/-!
# Theory Completion P9 — Object RG / typed scale calculus

The generic UEOT scale layer is a typed object/state transport calculus.  The
module proves composition and semantic-preservation rules without identifying
that calculus with Wilsonian RG.  Identity, purpose, GOD, GOA, repairability and
homeostasis are all transported only under explicit preservation hypotheses.
-/

namespace UEOT.V3.Compression.TheoryCompletion

universe uX uY uZ uOF uOM uOC uS uT

/-- Composition of two typed object-scale maps. -/
def ObjectScaleMap.comp
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {OF : Type uOF} {OM : Type uOM} {OC : Type uOC}
    (M₂ : ObjectScaleMap Y Z OM OC)
    (M₁ : ObjectScaleMap X Y OF OM) :
    ObjectScaleMap X Z OF OC where
  stateMap := M₂.stateMap ∘ M₁.stateMap
  objectMap := M₂.objectMap ∘ M₁.objectMap

@[simp] theorem ObjectScaleMap.comp_stateMap
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {OF : Type uOF} {OM : Type uOM} {OC : Type uOC}
    (M₂ : ObjectScaleMap Y Z OM OC)
    (M₁ : ObjectScaleMap X Y OF OM) (x : X) :
    (M₂.comp M₁).stateMap x = M₂.stateMap (M₁.stateMap x) := rfl

@[simp] theorem ObjectScaleMap.comp_objectMap
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {OF : Type uOF} {OM : Type uOM} {OC : Type uOC}
    (M₂ : ObjectScaleMap Y Z OM OC)
    (M₁ : ObjectScaleMap X Y OF OM) (o : OF) :
    (M₂.comp M₁).objectMap o = M₂.objectMap (M₁.objectMap o) := rfl

/-- Object transport composes exactly. -/
theorem objectScaleTransport_trans
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {OF : Type uOF} {OM : Type uOM} {OC : Type uOC}
    (M₁ : ObjectScaleMap X Y OF OM)
    (M₂ : ObjectScaleMap Y Z OM OC)
    {fine : OF} {middle : OM} {coarse : OC}
    (h₁ : ObjectScaleTransport M₁ fine middle)
    (h₂ : ObjectScaleTransport M₂ middle coarse) :
    ObjectScaleTransport (M₂.comp M₁) fine coarse := by
  unfold ObjectScaleTransport ObjectScaleMap.comp at *
  simp only [Function.comp_apply]
  rw [h₁, h₂]

/-- Generic preservation obligation for one semantic property. -/
def PreservesObjectPredicate
    {X : Type uX} {Y : Type uY}
    {OF : Type uOF} {OC : Type uOC}
    (M : ObjectScaleMap X Y OF OC)
    (FineProperty : OF → Prop) (CoarseProperty : OC → Prop) : Prop :=
  ∀ o, FineProperty o → CoarseProperty (M.objectMap o)

/-- Preservation hypotheses themselves compose. -/
theorem preservesObjectPredicate_comp
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {OF : Type uOF} {OM : Type uOM} {OC : Type uOC}
    (M₁ : ObjectScaleMap X Y OF OM)
    (M₂ : ObjectScaleMap Y Z OM OC)
    (P₁ : OF → Prop) (P₂ : OM → Prop) (P₃ : OC → Prop)
    (h₁ : PreservesObjectPredicate M₁ P₁ P₂)
    (h₂ : PreservesObjectPredicate M₂ P₂ P₃) :
    PreservesObjectPredicate (M₂.comp M₁) P₁ P₃ := by
  intro o ho
  exact h₂ (M₁.objectMap o) (h₁ o ho)

/-- A semantic certificate on the coarse object follows from a fine certificate
only when the corresponding scale map is explicitly proved to preserve it. -/
theorem transport_object_property
    {X : Type uX} {Y : Type uY}
    {OF : Type uOF} {OC : Type uOC}
    (M : ObjectScaleMap X Y OF OC)
    (FineProperty : OF → Prop) (CoarseProperty : OC → Prop)
    {fine : OF} {coarse : OC}
    (htransport : ObjectScaleTransport M fine coarse)
    (hpres : PreservesObjectPredicate M FineProperty CoarseProperty)
    (hfine : FineProperty fine) :
    CoarseProperty coarse := by
  unfold ObjectScaleTransport at htransport
  rw [← htransport]
  exact hpres fine hfine

/-- Typed names for the six P9 semantic obligations.  They are aliases of the
same preservation calculus, not new assumptions smuggled into `ObjectScaleMap`. -/
abbrev PreservesIdentity := @PreservesObjectPredicate
abbrev PreservesPurpose := @PreservesObjectPredicate
abbrev PreservesGOD := @PreservesObjectPredicate
abbrev PreservesGOA := @PreservesObjectPredicate
abbrev PreservesRepairability := @PreservesObjectPredicate
abbrev PreservesHomeostasis := @PreservesObjectPredicate

/-- P9 terminal semantic transport: six independent certificates can be moved
across the *same* object-scale transport when six independent preservation
proofs are available. -/
theorem p9_terminal_objectScale_semantic_transport
    {X : Type uX} {Y : Type uY}
    {OF : Type uOF} {OC : Type uOC}
    (M : ObjectScaleMap X Y OF OC)
    (IF PF GF AF RF HF : OF → Prop)
    (IC PC GC AC RC HC : OC → Prop)
    {fine : OF} {coarse : OC}
    (ht : ObjectScaleTransport M fine coarse)
    (hI : PreservesIdentity M IF IC)
    (hP : PreservesPurpose M PF PC)
    (hG : PreservesGOD M GF GC)
    (hA : PreservesGOA M AF AC)
    (hR : PreservesRepairability M RF RC)
    (hH : PreservesHomeostasis M HF HC)
    (hf : IF fine ∧ PF fine ∧ GF fine ∧ AF fine ∧ RF fine ∧ HF fine) :
    IC coarse ∧ PC coarse ∧ GC coarse ∧ AC coarse ∧ RC coarse ∧ HC coarse := by
  rcases hf with ⟨hif, hpf, hgf, haf, hrf, hhf⟩
  exact ⟨transport_object_property M IF IC ht hI hif,
    transport_object_property M PF PC ht hP hpf,
    transport_object_property M GF GC ht hG hgf,
    transport_object_property M AF AC ht hA haf,
    transport_object_property M RF RC ht hR hrf,
    transport_object_property M HF HC ht hH hhf⟩

/-- Structural scale events are typed separately; merge/split/birth/death are
not silently identified with an invertible scale transport. -/
inductive ObjectScaleEvent
  | transport
  | merge
  | split
  | birth
  | death
  deriving DecidableEq, Repr

/-- A Wilsonian interpretation contains extra physical coupling-flow data.  It
is intentionally not part of generic `ObjectScaleMap`. -/
structure WilsonianRGInterpretation (Coupling : Type uS) where
  couplingFlow : ℕ → Coupling

/-- The standalone Wilsonian coupling-flow data type is nontrivial whenever the
coupling type has two distinct values.  This theorem intentionally makes no
claim about compatibility with a particular `ObjectScaleMap`: such a claim
requires an explicit physical interpretation relation that generic P9 does not
yet provide. -/
theorem wilsonianCouplingFlow_nontrivial_of_twoCouplings
    {Coupling : Type uS} (c₀ c₁ : Coupling) (hne : c₀ ≠ c₁) :
    ∃ W₀ W₁ : WilsonianRGInterpretation Coupling,
      W₀.couplingFlow ≠ W₁.couplingFlow := by
  let W₀ : WilsonianRGInterpretation Coupling :=
    ⟨fun _ => c₀⟩
  let W₁ : WilsonianRGInterpretation Coupling :=
    ⟨fun _ => c₁⟩
  refine ⟨W₀, W₁, ?_⟩
  intro h
  have h0 := congrFun h 0
  exact hne h0

end UEOT.V3.Compression.TheoryCompletion
