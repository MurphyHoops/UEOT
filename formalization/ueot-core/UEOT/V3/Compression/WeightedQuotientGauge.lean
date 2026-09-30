import UEOT.V3.Compression.ApproximateQuotientGauge

/-!
# Occupation-weighted quotient gauge

`ApproximateQuotientGauge` counts every finite source point equally.  This
module weights the same optimal relabeling mismatch by one source law
`mu : stdSimplex ℝ X`.

The resulting quantity distinguishes structurally important representation
drift on occupied states from drift on states carrying zero current/long-run
mass.  It remains purely representational: no reward, transition, value, or
control conclusion is built into the definition.
-/

namespace UEOT.V3.Compression.WeightedQuotientGauge

open Function
open UEOT.V3.Compression.ApproximateQuotientGauge

universe uX uY uZ

noncomputable section

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Source-law mass of the points on which one quotient relabeling fails. -/
def weightedMismatch
    (mu : stdSimplex ℝ X)
    (q : X → Y) (r : X → Z) (e : Y ≃ Z) : ℝ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x => e (q x) ≠ r x), mu x

theorem weightedMismatch_nonneg
    (mu : stdSimplex ℝ X)
    (q : X → Y) (r : X → Z) (e : Y ≃ Z) :
    0 ≤ weightedMismatch mu q r e := by
  classical
  unfold weightedMismatch
  exact Finset.sum_nonneg (fun x _ => stdSimplex.zero_le mu x)

/-- Zero weighted mismatch means perfect alignment on every source point with
strictly positive source mass. -/
theorem weightedMismatch_eq_zero_iff_supportAligned
    (mu : stdSimplex ℝ X)
    (q : X → Y) (r : X → Z) (e : Y ≃ Z) :
    weightedMismatch mu q r e = 0 ↔
      ∀ x, 0 < mu x → e (q x) = r x := by
  classical
  unfold weightedMismatch
  let B : Finset X := Finset.univ.filter (fun x => e (q x) ≠ r x)
  have hnonneg : ∀ x ∈ B, 0 ≤ mu x :=
    fun x _ => stdSimplex.zero_le mu x
  constructor
  · intro hzero x hpos
    by_contra hne
    have hxB : x ∈ B := by simp [B, hne]
    have hall : ∀ y ∈ B, mu y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    exact (ne_of_gt hpos) (hall x hxB)
  · intro halign
    apply (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mpr
    intro x hxB
    have hne : e (q x) ≠ r x := by
      simpa [B] using hxB
    have hnotpos : ¬ 0 < mu x := by
      intro hpos
      exact hne (halign x hpos)
    exact le_antisymm (not_lt.mp hnotpos) (stdSimplex.zero_le mu x)

/-- All occupation-weighted mismatch costs realized by finite relabelings. -/
def weightedGaugeCosts
    (mu : stdSimplex ℝ X) (q : X → Y) (r : X → Z) : Finset ℝ := by
  classical
  exact Finset.univ.image (weightedMismatch mu q r)

theorem weightedGaugeCosts_nonempty
    [Nonempty (Y ≃ Z)]
    (mu : stdSimplex ℝ X) (q : X → Y) (r : X → Z) :
    (weightedGaugeCosts mu q r).Nonempty := by
  classical
  let e : Y ≃ Z := Classical.choice inferInstance
  exact ⟨weightedMismatch mu q r e, by simp [weightedGaugeCosts]⟩

/-- Minimum occupied source mass that must change quotient membership after the
best finite relabeling. -/
def weightedGaugeMismatch
    [Nonempty (Y ≃ Z)]
    (mu : stdSimplex ℝ X) (q : X → Y) (r : X → Z) : ℝ :=
  (weightedGaugeCosts mu q r).min'
    (weightedGaugeCosts_nonempty mu q r)

theorem exists_optimalEquiv_weighted
    [Nonempty (Y ≃ Z)]
    (mu : stdSimplex ℝ X) (q : X → Y) (r : X → Z) :
    ∃ e : Y ≃ Z,
      weightedMismatch mu q r e = weightedGaugeMismatch mu q r := by
  classical
  have hmem : weightedGaugeMismatch mu q r ∈ weightedGaugeCosts mu q r :=
    Finset.min'_mem _ (weightedGaugeCosts_nonempty mu q r)
  rcases Finset.mem_image.mp hmem with ⟨e, _, he⟩
  exact ⟨e, he⟩

theorem weightedGaugeMismatch_le
    [Nonempty (Y ≃ Z)]
    (mu : stdSimplex ℝ X) (q : X → Y) (r : X → Z) (e : Y ≃ Z) :
    weightedGaugeMismatch mu q r ≤ weightedMismatch mu q r e := by
  classical
  apply Finset.min'_le
  simp [weightedGaugeCosts]

theorem weightedGaugeMismatch_nonneg
    [Nonempty (Y ≃ Z)]
    (mu : stdSimplex ℝ X) (q : X → Y) (r : X → Z) :
    0 ≤ weightedGaugeMismatch mu q r := by
  rcases exists_optimalEquiv_weighted mu q r with ⟨e, he⟩
  rw [← he]
  exact weightedMismatch_nonneg mu q r e

/-- Zero optimal weighted mismatch is exactly existence of one gauge alignment
that is perfect on the positive-mass support of `mu`. -/
theorem weightedGaugeMismatch_eq_zero_iff_exists_supportAligned
    [Nonempty (Y ≃ Z)]
    (mu : stdSimplex ℝ X) (q : X → Y) (r : X → Z) :
    weightedGaugeMismatch mu q r = 0 ↔
      ∃ e : Y ≃ Z, ∀ x, 0 < mu x → e (q x) = r x := by
  constructor
  · intro hzero
    rcases exists_optimalEquiv_weighted mu q r with ⟨e, he⟩
    refine ⟨e, (weightedMismatch_eq_zero_iff_supportAligned mu q r e).mp ?_⟩
    simpa [hzero] using he
  · rintro ⟨e, halign⟩
    have hcost : weightedMismatch mu q r e = 0 :=
      (weightedMismatch_eq_zero_iff_supportAligned mu q r e).mpr halign
    have hle := weightedGaugeMismatch_le mu q r e
    have hnonneg := weightedGaugeMismatch_nonneg mu q r
    rw [hcost] at hle
    exact le_antisymm hle hnonneg

/-- With full source support, weighted zero mismatch upgrades from almost-sure
alignment to exact same-fibre quotient identity. -/
theorem weightedGaugeMismatch_eq_zero_iff_sameFibers_of_fullSupport
    [Nonempty (Y ≃ Z)]
    (mu : stdSimplex ℝ X)
    (hfull : ∀ x, 0 < mu x)
    (q : X → Y) (r : X → Z)
    (hq : Surjective q) (hr : Surjective r) :
    weightedGaugeMismatch mu q r = 0 ↔
      UEOT.V3.Compression.QuotientGauge.SameFibers q r := by
  rw [weightedGaugeMismatch_eq_zero_iff_exists_supportAligned]
  constructor
  · rintro ⟨e, he⟩
    apply (UEOT.V3.Compression.QuotientGauge.sameFibers_iff_existsUnique_equiv
      q r hq hr).2
    refine ⟨e, ?_, ?_⟩
    · funext x
      exact he x (hfull x)
    · intro e' he'
      apply Equiv.ext
      intro y
      rcases hq y with ⟨x, rfl⟩
      have hx := he x (hfull x)
      simpa only [Function.comp_apply] using
        (congrFun he' x).trans hx.symm
  · intro hsame
    let e := UEOT.V3.Compression.QuotientGauge.quotientEquiv
      q r hq hr hsame
    refine ⟨e, ?_⟩
    intro x _
    exact congrFun
      (UEOT.V3.Compression.QuotientGauge.quotientEquiv_comp
        q r hq hr hsame) x

/-- Weighted mismatch is preserved by reversing a quotient relabeling. -/
theorem weightedMismatch_symm
    (mu : stdSimplex ℝ X)
    (q : X → Y) (r : X → Z) (e : Y ≃ Z) :
    weightedMismatch mu r q e.symm = weightedMismatch mu q r e := by
  classical
  unfold weightedMismatch
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hne heq
      apply hne
      apply e.injective
      simpa using heq.symm
    · intro hne heq
      apply hne
      have := congrArg e heq
      simpa using this.symm
  · intro x _
    rfl

theorem weightedGaugeMismatch_symm
    [Nonempty (Y ≃ Z)] [Nonempty (Z ≃ Y)]
    (mu : stdSimplex ℝ X) (q : X → Y) (r : X → Z) :
    weightedGaugeMismatch mu q r = weightedGaugeMismatch mu r q := by
  apply le_antisymm
  · rcases exists_optimalEquiv_weighted mu r q with ⟨e, he⟩
    calc
      weightedGaugeMismatch mu q r
          ≤ weightedMismatch mu q r e.symm :=
        weightedGaugeMismatch_le mu q r e.symm
      _ = weightedMismatch mu r q e := weightedMismatch_symm mu r q e
      _ = weightedGaugeMismatch mu r q := he
  · rcases exists_optimalEquiv_weighted mu q r with ⟨e, he⟩
    calc
      weightedGaugeMismatch mu r q
          ≤ weightedMismatch mu r q e.symm :=
        weightedGaugeMismatch_le mu r q e.symm
      _ = weightedMismatch mu q r e := weightedMismatch_symm mu q r e
      _ = weightedGaugeMismatch mu q r := he

/-- Weighted mismatch composes subadditively under quotient relabelings. -/
theorem weightedMismatch_trans_le
    {W : Type*} [Fintype W]
    (mu : stdSimplex ℝ X)
    (q : X → Y) (r : X → Z) (s : X → W)
    (e : Y ≃ Z) (f : Z ≃ W) :
    weightedMismatch mu q s (e.trans f) ≤
      weightedMismatch mu q r e + weightedMismatch mu r s f := by
  classical
  let A : Finset X := Finset.univ.filter (fun x => e (q x) ≠ r x)
  let B : Finset X := Finset.univ.filter (fun x => f (r x) ≠ s x)
  let C : Finset X := Finset.univ.filter (fun x => (e.trans f) (q x) ≠ s x)
  have hsub : C ⊆ A ∪ B := by
    intro x hx
    have hx' : f (e (q x)) ≠ s x := by
      have hpred : (e.trans f) (q x) ≠ s x := (Finset.mem_filter.mp hx).2
      simpa only [Equiv.trans_apply] using hpred
    simp only [A, B, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hA : e (q x) = r x
    · right
      intro hB
      apply hx'
      rw [hA, hB]
    · exact Or.inl hA
  have hCunion : (∑ x ∈ C, mu x) ≤ ∑ x ∈ A ∪ B, mu x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro x _ _
    exact stdSimplex.zero_le mu x
  have hinter : 0 ≤ ∑ x ∈ A ∩ B, mu x :=
    Finset.sum_nonneg (fun x _ => stdSimplex.zero_le mu x)
  have hunion :
      (∑ x ∈ A ∪ B, mu x) ≤ (∑ x ∈ A, mu x) + ∑ x ∈ B, mu x := by
    have hEq :
        (∑ x ∈ A ∪ B, mu x) + (∑ x ∈ A ∩ B, mu x) =
          (∑ x ∈ A, mu x) + ∑ x ∈ B, mu x :=
      Finset.sum_union_inter
    linarith
  unfold weightedMismatch
  simpa [A, B, C] using hCunion.trans hunion

theorem weightedGaugeMismatch_triangle
    {W : Type*} [Fintype W]
    [Nonempty (Y ≃ Z)] [Nonempty (Z ≃ W)] [Nonempty (Y ≃ W)]
    (mu : stdSimplex ℝ X)
    (q : X → Y) (r : X → Z) (s : X → W) :
    weightedGaugeMismatch mu q s ≤
      weightedGaugeMismatch mu q r + weightedGaugeMismatch mu r s := by
  rcases exists_optimalEquiv_weighted mu q r with ⟨e, he⟩
  rcases exists_optimalEquiv_weighted mu r s with ⟨f, hf⟩
  calc
    weightedGaugeMismatch mu q s
        ≤ weightedMismatch mu q s (e.trans f) :=
      weightedGaugeMismatch_le mu q s (e.trans f)
    _ ≤ weightedMismatch mu q r e + weightedMismatch mu r s f :=
      weightedMismatch_trans_le mu q r s e f
    _ = weightedGaugeMismatch mu q r + weightedGaugeMismatch mu r s := by
      rw [he, hf]

theorem weightedGaugeMismatch_self
    (mu : stdSimplex ℝ X) (q : X → Y) :
    weightedGaugeMismatch mu q q = 0 := by
  apply (weightedGaugeMismatch_eq_zero_iff_exists_supportAligned mu q q).2
  exact ⟨Equiv.refl Y, by intro x _; rfl⟩

end

end UEOT.V3.Compression.WeightedQuotientGauge
