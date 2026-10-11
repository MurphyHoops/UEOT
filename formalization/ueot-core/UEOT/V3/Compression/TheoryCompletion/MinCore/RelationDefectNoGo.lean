import Mathlib

/-!
# UEOT MINCORE — relation/defect calibration boundary

This additive, uncounted research module tests the remaining second-order
compression route identified by the structural-defect feasibility audit:
an exact relation equipped with a separately supplied quantitative defect
presentation.

The result is deliberately negative.  The exact zero relation does not
determine the numerical defect scale.  Positive rescaling preserves the exact
relation while changing every nonzero quantitative defect and correspondingly
rescales finite error budgets.  Therefore a relation-only common core cannot
recover the quantitative certificates used by M-TC without an additional
calibration/gauge premise.

This does not alter the frozen Core 106, the counted generator ledger, or the
relative four-generator minimality result.
-/

namespace UEOT.V3.Compression.TheoryCompletion.MinCore

/-- An exact binary relation together with one nonnegative quantitative
presentation whose zero set is exactly that relation. -/
structure RelationDefectPresentation (X : Type*) where
  rel : X → X → Prop
  defect : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ defect x y
  zero_iff : ∀ x y, defect x y = 0 ↔ rel x y

namespace RelationDefectPresentation

variable {X : Type*}

/-- Positive rescaling changes only the quantitative calibration, not the
underlying exact relation. -/
def rescale (P : RelationDefectPresentation X) (c : ℝ) (hc : 0 < c) :
    RelationDefectPresentation X where
  rel := P.rel
  defect := fun x y => c * P.defect x y
  nonneg := by
    intro x y
    exact mul_nonneg (le_of_lt hc) (P.nonneg x y)
  zero_iff := by
    intro x y
    simp [ne_of_gt hc, P.zero_iff x y]

@[simp] theorem rescale_rel
    (P : RelationDefectPresentation X) (c : ℝ) (hc : 0 < c) :
    (P.rescale c hc).rel = P.rel := rfl

@[simp] theorem rescale_defect
    (P : RelationDefectPresentation X) (c : ℝ) (hc : 0 < c) (x y : X) :
    (P.rescale c hc).defect x y = c * P.defect x y := rfl

/-- Exact relatedness is invariant under every positive defect rescaling. -/
theorem rescale_preserves_exact_relation
    (P : RelationDefectPresentation X) (c : ℝ) (hc : 0 < c) (x y : X) :
    (P.rescale c hc).rel x y ↔ P.rel x y := Iff.rfl

/-- The zero-defect predicate is calibration invariant. -/
theorem rescale_zero_iff
    (P : RelationDefectPresentation X) (c : ℝ) (hc : 0 < c) (x y : X) :
    (P.rescale c hc).defect x y = 0 ↔ P.defect x y = 0 := by
  simp [rescale, ne_of_gt hc]

/-- Every finite quantitative threshold changes with the calibration scale. -/
theorem rescale_budget_iff
    (P : RelationDefectPresentation X) (c ε : ℝ) (hc : 0 < c) (x y : X) :
    (P.rescale c hc).defect x y ≤ ε ↔ P.defect x y ≤ ε / c := by
  simpa [rescale, mul_comm] using
    (le_div_iff₀ hc : P.defect x y ≤ ε / c ↔ P.defect x y * c ≤ ε).symm

/-- A positive nontrivial rescaling changes every nonzero defect value. -/
theorem rescale_changes_nonzero_defect
    (P : RelationDefectPresentation X) (c : ℝ) (hc : 0 < c) (hc1 : c ≠ 1)
    {x y : X} (hd : P.defect x y ≠ 0) :
    (P.rescale c hc).defect x y ≠ P.defect x y := by
  simp only [rescale_defect]
  intro h
  have hz : (c - 1) * P.defect x y = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hz with hscale | hdefect
  · exact hc1 (sub_eq_zero.mp hscale)
  · exact hd hdefect

end RelationDefectPresentation

/-- Canonical two-point presentation: equality is the exact relation and
off-diagonal pairs have unit defect. -/
def boolEqualityUnitDefect : RelationDefectPresentation Bool where
  rel := fun x y => x = y
  defect := fun x y => if x = y then 0 else 1
  nonneg := by
    intro x y
    split <;> norm_num
  zero_iff := by
    intro x y
    by_cases h : x = y
    · simp [h]
    · simp [h]

@[simp] theorem boolEqualityUnitDefect_false_true :
    boolEqualityUnitDefect.defect false true = 1 := by
  simp [boolEqualityUnitDefect]

/-- A continuum of positive calibrations realizes exactly the same equality
relation while assigning an arbitrary positive value to the off-diagonal pair. -/
theorem same_relation_arbitrary_positive_scale
    (c : ℝ) (hc : 0 < c) :
    (∀ x y : Bool,
      (boolEqualityUnitDefect.rescale c hc).rel x y ↔
        boolEqualityUnitDefect.rel x y) ∧
    (boolEqualityUnitDefect.rescale c hc).defect false true = c := by
  constructor
  · intro x y
    rfl
  · simp [RelationDefectPresentation.rescale, boolEqualityUnitDefect]

/-- No functional of the exact relation alone can recover the numerical defect
for every admissible presentation, even on a two-point space. -/
theorem no_relation_only_quantitative_recovery
    (recover : (Bool → Bool → Prop) → Bool → Bool → ℝ) :
    ¬ (∀ P : RelationDefectPresentation Bool,
      recover P.rel false true = P.defect false true) := by
  intro hrecover
  have hunit := hrecover boolEqualityUnitDefect
  have hdouble :=
    hrecover (boolEqualityUnitDefect.rescale 2 (by norm_num))
  simp [boolEqualityUnitDefect, RelationDefectPresentation.rescale] at hunit hdouble
  linarith

/-- Stronger paired witness: two admissible presentations have definitionally
the same exact relation but different finite defect values. -/
theorem exists_same_relation_different_defect :
    ∃ P Q : RelationDefectPresentation Bool,
      P.rel = Q.rel ∧ P.defect false true ≠ Q.defect false true := by
  refine ⟨boolEqualityUnitDefect,
    boolEqualityUnitDefect.rescale 2 (by norm_num), ?_, ?_⟩
  · rfl
  · simp [boolEqualityUnitDefect, RelationDefectPresentation.rescale]

/-- A three-point presentation with the same exact equality relation but a
quantitative defect that deliberately violates the triangle inequality. -/
def threePointNonmetricDefect : RelationDefectPresentation (Fin 3) where
  rel := fun x y => x = y
  defect := fun x y =>
    if x = y then 0
    else if x = (0 : Fin 3) ∧ y = (2 : Fin 3) then 3
    else 1
  nonneg := by
    intro x y
    by_cases hxy : x = y
    · simp [hxy]
    · by_cases h02 : x = (0 : Fin 3) ∧ y = (2 : Fin 3)
      · simp [h02]
      · simp [hxy, h02]
  zero_iff := by
    intro x y
    by_cases hxy : x = y
    · simp [hxy]
    · by_cases h02 : x = (0 : Fin 3) ∧ y = (2 : Fin 3)
      · simp [h02]
      · simp [hxy, h02]

/-- Zero-set compatibility and nonnegativity alone do not provide the
triangle/finite-composition regularity required by transport calculus. -/
theorem relationDefectPresentation_does_not_force_triangle :
    ¬ (∀ (P : RelationDefectPresentation (Fin 3)) (x y z : Fin 3),
      P.defect x z ≤ P.defect x y + P.defect y z) := by
  intro htriangle
  have hbad :=
    htriangle threePointNonmetricDefect (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
  have h02 : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
  have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have h12 : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
  norm_num [threePointNonmetricDefect, h02, h01, h12] at hbad

end UEOT.V3.Compression.TheoryCompletion.MinCore
