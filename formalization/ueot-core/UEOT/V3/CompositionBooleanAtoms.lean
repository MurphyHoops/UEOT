import Mathlib.Order.BooleanSubalgebra

/-!
# P-COMP-05 — canonical Booleanization of overlapping regions

For finitely many overlapping regions `V i ⊆ X`, the frozen Core 3 source
assigns to each point its membership signature and defines the corresponding
signature cells `A_J`.  The nonempty cells are exactly the atoms of the unique
smallest Boolean algebra containing all regions.

We use Mathlib's `BooleanSubalgebra (Set X)` directly.  Thus "smallest Boolean
algebra" is represented by `BooleanSubalgebra.closure (Set.range V)`, rather
than by a bespoke set-family surrogate.
-/

namespace UEOT.V3.CompositionBooleanAtoms

open Set

universe uX uI

variable {X : Type uX} {I : Type uI} [Fintype I]

/-- Membership signature `s(x) = {i | x ∈ V_i}`. -/
noncomputable def regionSignature (V : I → Set X) (x : X) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => x ∈ V i)

/-- Signature cell `A_J`. -/
def signatureAtom (V : I → Set X) (J : Finset I) : Set X :=
  {x | regionSignature V x = J}

/-- The generating family of physical regions. -/
def regionGenerators (V : I → Set X) : Set (Set X) :=
  Set.range V

/-- The unique least Boolean subalgebra containing all declared regions. -/
def generatedBoolean (V : I → Set X) : BooleanSubalgebra (Set X) :=
  BooleanSubalgebra.closure (regionGenerators V)

/-- A nonempty minimal nonempty element of a Boolean subalgebra. -/
def IsBooleanAtom (L : BooleanSubalgebra (Set X)) (A : Set X) : Prop :=
  A.Nonempty ∧ A ∈ L ∧
    ∀ S : Set X, S ∈ L → S ⊆ A → S.Nonempty → S = A

@[simp]
theorem mem_regionSignature_iff (V : I → Set X) (x : X) (i : I) :
    i ∈ regionSignature V x ↔ x ∈ V i := by
  classical
  simp [regionSignature]

/-- Every point belongs to exactly one signature cell. -/
theorem signatureAtom_partition_unique (V : I → Set X) (x : X) :
    ∃! J : Finset I, x ∈ signatureAtom V J := by
  refine ⟨regionSignature V x, ?_, ?_⟩
  · exact rfl
  · intro J hJ
    change regionSignature V x = J at hJ
    exact hJ.symm

/-- Each original region is exactly the union of the signature cells whose
signature contains that region index. -/
theorem region_eq_iUnion_signatureAtoms (V : I → Set X) (i : I) :
    V i = ⋃ J : {J : Finset I // i ∈ J}, signatureAtom V J.1 := by
  ext x
  constructor
  · intro hx
    have hi : i ∈ regionSignature V x :=
      (mem_regionSignature_iff V x i).2 hx
    let J : {J : Finset I // i ∈ J} := ⟨regionSignature V x, hi⟩
    exact Set.mem_iUnion.2 ⟨J, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨J, hxJ⟩
    change regionSignature V x = J.1 at hxJ
    apply (mem_regionSignature_iff V x i).1
    rw [hxJ]
    exact J.2

/-- A signature cell is the finite intersection of the corresponding regions
and complementary regions.  The decidable-equality argument is purely a local
computational witness for `Finset` membership and is not part of the source
mathematical assumptions. -/
theorem signatureAtom_eq_iInter [DecidableEq I]
    (V : I → Set X) (J : Finset I) :
    signatureAtom V J =
      ⋂ i : I, if i ∈ J then V i else (V i)ᶜ := by
  ext x
  simp only [signatureAtom, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hsig i
    subst J
    by_cases hi : i ∈ regionSignature V x
    · simp only [hi, if_pos]
      exact (mem_regionSignature_iff V x i).1 hi
    · simp only [hi, if_neg, Set.mem_compl_iff]
      intro hxi
      exact hi ((mem_regionSignature_iff V x i).2 hxi)
  · intro h
    apply Finset.ext
    intro i
    rw [mem_regionSignature_iff]
    have hiSet := h i
    by_cases hi : i ∈ J
    · have hxV : x ∈ V i := by simpa [hi] using hiSet
      exact ⟨fun _ => hi, fun _ => hxV⟩
    · have hxV : x ∉ V i := by simpa [hi] using hiSet
      exact ⟨fun hxi => (hxV hxi).elim, fun hJi => (hi hJi).elim⟩

/-- Every generator lies in the generated Boolean algebra. -/
theorem region_mem_generated (V : I → Set X) (i : I) :
    V i ∈ generatedBoolean V := by
  unfold generatedBoolean regionGenerators
  apply BooleanSubalgebra.subset_closure
  exact ⟨i, rfl⟩

/-- Every signature cell lies in the generated Boolean algebra. -/
theorem signatureAtom_mem_generated (V : I → Set X) (J : Finset I) :
    signatureAtom V J ∈ generatedBoolean V := by
  classical
  rw [signatureAtom_eq_iInter]
  apply BooleanSubalgebra.iInf_mem
  intro i
  by_cases hi : i ∈ J
  · simpa [hi] using region_mem_generated V i
  · simpa [hi] using
      (generatedBoolean V).compl_mem (region_mem_generated V i)

/-- Membership in any generated Boolean set depends only on the region
signature. -/
theorem generated_membership_congr
    (V : I → Set X) {x y : X}
    (hxy : regionSignature V x = regionSignature V y)
    (S : Set X) (hS : S ∈ generatedBoolean V) :
    x ∈ S ↔ y ∈ S := by
  unfold generatedBoolean at hS
  refine BooleanSubalgebra.closure_bot_sup_induction
    (s := regionGenerators V)
    (p := fun R _ => x ∈ R ↔ y ∈ R)
    ?_ ?_ ?_ ?_ hS
  · intro R hR
    rcases hR with ⟨i, rfl⟩
    constructor
    · intro hx
      have hi : i ∈ regionSignature V x :=
        (mem_regionSignature_iff V x i).2 hx
      rw [hxy] at hi
      exact (mem_regionSignature_iff V y i).1 hi
    · intro hy
      have hi : i ∈ regionSignature V y :=
        (mem_regionSignature_iff V y i).2 hy
      rw [← hxy] at hi
      exact (mem_regionSignature_iff V x i).1 hi
  · simp
  · intro A hA B hB ihA ihB
    simpa [ihA, ihB]
  · intro A hA ihA
    simpa [ihA]

/-- Every nonempty signature cell is an atom of the generated Boolean algebra. -/
theorem signatureAtom_isBooleanAtom
    (V : I → Set X) (J : Finset I)
    (hne : (signatureAtom V J).Nonempty) :
    IsBooleanAtom (generatedBoolean V) (signatureAtom V J) := by
  refine ⟨hne, signatureAtom_mem_generated V J, ?_⟩
  intro S hS hSA hSne
  apply Set.Subset.antisymm hSA
  intro x hxA
  rcases hSne with ⟨y, hyS⟩
  have hyA : y ∈ signatureAtom V J := hSA hyS
  change regionSignature V x = J at hxA
  change regionSignature V y = J at hyA
  have hxy : regionSignature V x = regionSignature V y := hxA.trans hyA.symm
  exact (generated_membership_congr V hxy S hS).2 hyS

/-- Conversely, every atom of the generated Boolean algebra is a nonempty
signature cell. -/
theorem booleanAtom_eq_signatureAtom
    (V : I → Set X) (A : Set X)
    (hA : IsBooleanAtom (generatedBoolean V) A) :
    ∃ J : Finset I, (signatureAtom V J).Nonempty ∧
      A = signatureAtom V J := by
  rcases hA.1 with ⟨x, hxA⟩
  let J : Finset I := regionSignature V x
  have hxSig : x ∈ signatureAtom V J := by
    change regionSignature V x = J
    rfl
  have hSigNon : (signatureAtom V J).Nonempty := ⟨x, hxSig⟩
  have hSigSub : signatureAtom V J ⊆ A := by
    intro y hySig
    change regionSignature V y = J at hySig
    have hsame : regionSignature V y = regionSignature V x := by
      simpa [J] using hySig
    exact (generated_membership_congr V hsame A hA.2.1).2 hxA
  have hEq : signatureAtom V J = A :=
    hA.2.2 (signatureAtom V J) (signatureAtom_mem_generated V J)
      hSigSub hSigNon
  exact ⟨J, hSigNon, hEq.symm⟩

/-- The generated Boolean algebra is below every Boolean algebra containing all
regions. -/
theorem generated_le_of_regions_mem
    (V : I → Set X) (L : BooleanSubalgebra (Set X))
    (hL : ∀ i, V i ∈ L) :
    generatedBoolean V ≤ L := by
  unfold generatedBoolean regionGenerators
  rw [BooleanSubalgebra.closure_le]
  rintro S ⟨i, rfl⟩
  exact hL i

/-- The least Boolean algebra containing the regions is unique. -/
theorem generated_unique_minimal
    (V : I → Set X) (L : BooleanSubalgebra (Set X))
    (hL : ∀ i, V i ∈ L)
    (hmin : ∀ M : BooleanSubalgebra (Set X),
      (∀ i, V i ∈ M) → L ≤ M) :
    L = generatedBoolean V := by
  apply le_antisymm
  · exact hmin (generatedBoolean V) (region_mem_generated V)
  · exact generated_le_of_regions_mem V L hL

/-- Source-facing P-COMP-05: the nonempty membership-signature cells are
exactly the atoms of the unique least Boolean algebra generated by the declared
overlapping regions. -/
theorem p_comp_05 (V : I → Set X) :
    (∀ x : X, ∃! J : Finset I, x ∈ signatureAtom V J) ∧
    (∀ i : I, V i = ⋃ J : {J : Finset I // i ∈ J}, signatureAtom V J.1) ∧
    (∀ J : Finset I, (signatureAtom V J).Nonempty →
      IsBooleanAtom (generatedBoolean V) (signatureAtom V J)) ∧
    (∀ A : Set X, IsBooleanAtom (generatedBoolean V) A →
      ∃ J : Finset I, (signatureAtom V J).Nonempty ∧ A = signatureAtom V J) ∧
    (∀ L : BooleanSubalgebra (Set X),
      (∀ i, V i ∈ L) → generatedBoolean V ≤ L) := by
  exact ⟨signatureAtom_partition_unique V,
    region_eq_iUnion_signatureAtoms V,
    signatureAtom_isBooleanAtom V,
    booleanAtom_eq_signatureAtom V,
    generated_le_of_regions_mem V⟩

end UEOT.V3.CompositionBooleanAtoms
