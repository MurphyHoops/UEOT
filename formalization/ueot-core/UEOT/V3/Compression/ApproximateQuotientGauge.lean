import UEOT.V3.Compression.QuotientGauge

/-!
# Approximate quotient gauge on finite source representations

Exact `QuotientGauge.SameFibers` identifies two surjective quotient
representations when they differ only by a bijective relabeling of quotient
states.  For moving/learned encoders we also need a label-invariant finite
mismatch quantity.

For finite source `X`, define the mismatch cost of one relabeling `e : Y ≃ Z`
as the number of source points where `e (q x) != r x`.  The gauge mismatch is
the minimum of that cost over all quotient-state equivalences.

This quantity intentionally measures representation/partition mismatch only.
It contains no reward, transition, visitation-frequency, or control semantics.
Those must be supplied by separate adapters before behavioral conclusions are
drawn.
-/

namespace UEOT.V3.Compression.ApproximateQuotientGauge

open Function
open UEOT.V3.Compression.QuotientGauge

universe uX uY uZ

noncomputable section

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Number of source points on which one candidate quotient relabeling fails
to align the two encoder labels. -/
def mismatchCount (q : X → Y) (r : X → Z) (e : Y ≃ Z) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x => e (q x) ≠ r x)).card

theorem mismatchCount_eq_zero_iff
    (q : X → Y) (r : X → Z) (e : Y ≃ Z) :
    mismatchCount q r e = 0 ↔ ∀ x, e (q x) = r x := by
  classical
  simp [mismatchCount]

/-- All mismatch costs realized by finite quotient-state relabelings. -/
def gaugeCosts (q : X → Y) (r : X → Z) : Finset ℕ := by
  classical
  exact Finset.univ.image (mismatchCount q r)

theorem gaugeCosts_nonempty
    [Nonempty (Y ≃ Z)] (q : X → Y) (r : X → Z) :
    (gaugeCosts q r).Nonempty := by
  classical
  let e : Y ≃ Z := Classical.choice inferInstance
  exact ⟨mismatchCount q r e, by simp [gaugeCosts]⟩

/-- Label-invariant finite representation mismatch.  The quotient carriers
must have the same finite cardinality, represented here by `Nonempty (Y ≃ Z)`.
-/
def gaugeMismatch [Nonempty (Y ≃ Z)] (q : X → Y) (r : X → Z) : ℕ :=
  (gaugeCosts q r).min' (gaugeCosts_nonempty q r)

/-- An optimal quotient-state relabeling exists because the relabeling space is
finite. -/
theorem exists_optimalEquiv
    [Nonempty (Y ≃ Z)] (q : X → Y) (r : X → Z) :
    ∃ e : Y ≃ Z, mismatchCount q r e = gaugeMismatch q r := by
  classical
  have hmem : gaugeMismatch q r ∈ gaugeCosts q r := by
    exact Finset.min'_mem _ (gaugeCosts_nonempty q r)
  rcases Finset.mem_image.mp hmem with ⟨e, _, he⟩
  exact ⟨e, he⟩

theorem gaugeMismatch_le
    [Nonempty (Y ≃ Z)] (q : X → Y) (r : X → Z) (e : Y ≃ Z) :
    gaugeMismatch q r ≤ mismatchCount q r e := by
  classical
  apply Finset.min'_le
  simp [gaugeCosts]

/-- Zero gauge mismatch is exactly existence of a perfect relabeling on every
source point. -/
theorem gaugeMismatch_eq_zero_iff_exists_equiv
    [Nonempty (Y ≃ Z)] (q : X → Y) (r : X → Z) :
    gaugeMismatch q r = 0 ↔ ∃ e : Y ≃ Z, e ∘ q = r := by
  constructor
  · intro hzero
    rcases exists_optimalEquiv q r with ⟨e, he⟩
    have hcost : mismatchCount q r e = 0 := by simpa [hzero] using he
    refine ⟨e, ?_⟩
    funext x
    exact (mismatchCount_eq_zero_iff q r e).mp hcost x
  · rintro ⟨e, he⟩
    have hcost : mismatchCount q r e = 0 := by
      apply (mismatchCount_eq_zero_iff q r e).mpr
      intro x
      simpa only [Function.comp_apply] using congrFun he x
    have hle := gaugeMismatch_le q r e
    omega

/-- For surjective finite quotient maps of equal cardinality, zero approximate
gauge mismatch recovers the exact same-fibre relation from `QuotientGauge`.
-/
theorem gaugeMismatch_eq_zero_iff_sameFibers
    [Nonempty (Y ≃ Z)]
    (q : X → Y) (r : X → Z)
    (hq : Surjective q) (hr : Surjective r) :
    gaugeMismatch q r = 0 ↔ SameFibers q r := by
  rw [gaugeMismatch_eq_zero_iff_exists_equiv]
  constructor
  · rintro ⟨e, he⟩
    exact (sameFibers_iff_existsUnique_equiv q r hq hr).2
      ⟨e, he, by
        intro e' he'
        apply Equiv.ext
        intro y
        rcases hq y with ⟨x, rfl⟩
        simpa only [Function.comp_apply] using
          (congrFun he' x).trans (congrFun he x).symm⟩
  · intro hsame
    exact ⟨quotientEquiv q r hq hr hsame,
      quotientEquiv_comp q r hq hr hsame⟩

/-- Reversing the alignment preserves its mismatch count. -/
theorem mismatchCount_symm
    (q : X → Y) (r : X → Z) (e : Y ≃ Z) :
    mismatchCount r q e.symm = mismatchCount q r e := by
  classical
  unfold mismatchCount
  congr 1
  ext x
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

/-- Gauge mismatch is symmetric.  The reverse comparison uses the inverse of
an optimal relabeling; no canonical choice of labels is required. -/
theorem gaugeMismatch_symm
    [Nonempty (Y ≃ Z)] [Nonempty (Z ≃ Y)]
    (q : X → Y) (r : X → Z) :
    gaugeMismatch q r = gaugeMismatch r q := by
  apply Nat.le_antisymm
  · rcases exists_optimalEquiv r q with ⟨e, he⟩
    have hle := gaugeMismatch_le q r e.symm
    calc
      gaugeMismatch q r ≤ mismatchCount q r e.symm := hle
      _ = mismatchCount r q e := mismatchCount_symm r q e
      _ = gaugeMismatch r q := he
  · rcases exists_optimalEquiv q r with ⟨e, he⟩
    have hle := gaugeMismatch_le r q e.symm
    calc
      gaugeMismatch r q ≤ mismatchCount r q e.symm := hle
      _ = mismatchCount q r e := mismatchCount_symm q r e
      _ = gaugeMismatch q r := he

/-- Mismatch counts compose subadditively under composition of quotient-state
relabelings.  A source point can fail the composed alignment only if it already
fails the first alignment or the second alignment. -/
theorem mismatchCount_trans_le
    {W : Type*} [Fintype W]
    (q : X → Y) (r : X → Z) (s : X → W)
    (e : Y ≃ Z) (f : Z ≃ W) :
    mismatchCount q s (e.trans f) ≤
      mismatchCount q r e + mismatchCount r s f := by
  classical
  unfold mismatchCount
  have hsub :
      Finset.univ.filter (fun x => (e.trans f) (q x) ≠ s x) ⊆
        Finset.univ.filter (fun x => e (q x) ≠ r x) ∪
          Finset.univ.filter (fun x => f (r x) ≠ s x) := by
    intro x hx
    have hx' : f (e (q x)) ≠ s x := by
      have hpred : (e.trans f) (q x) ≠ s x := (Finset.mem_filter.mp hx).2
      simpa only [Equiv.trans_apply] using hpred
    simp only [Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hA : e (q x) = r x
    · right
      intro hB
      apply hx'
      rw [hA, hB]
    · exact Or.inl hA
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le
      (Finset.univ.filter (fun x => e (q x) ≠ r x))
      (Finset.univ.filter (fun x => f (r x) ≠ s x)))

/-- Gauge mismatch satisfies the triangle inequality across finite quotient
representations of equal cardinality. -/
theorem gaugeMismatch_triangle
    {W : Type*} [Fintype W]
    [Nonempty (Y ≃ Z)] [Nonempty (Z ≃ W)] [Nonempty (Y ≃ W)]
    (q : X → Y) (r : X → Z) (s : X → W) :
    gaugeMismatch q s ≤ gaugeMismatch q r + gaugeMismatch r s := by
  rcases exists_optimalEquiv q r with ⟨e, he⟩
  rcases exists_optimalEquiv r s with ⟨f, hf⟩
  calc
    gaugeMismatch q s ≤ mismatchCount q s (e.trans f) :=
      gaugeMismatch_le q s (e.trans f)
    _ ≤ mismatchCount q r e + mismatchCount r s f :=
      mismatchCount_trans_le q r s e f
    _ = gaugeMismatch q r + gaugeMismatch r s := by rw [he, hf]

/-- A representation has zero gauge mismatch with itself. -/
theorem gaugeMismatch_self
    (q : X → Y) :
    gaugeMismatch q q = 0 := by
  apply (gaugeMismatch_eq_zero_iff_exists_equiv q q).2
  exact ⟨Equiv.refl Y, rfl⟩

end

end UEOT.V3.Compression.ApproximateQuotientGauge
