import UEOT.V3.Compression.TheoryCompletion.MinCore.RelationDefectNoGo
import UEOT.V3.Compression.TransportCertificate

/-!
# UEOT MINCORE — calibrated defect comparison

This additive, uncounted research module continues the relation/defect
identifiability audit.  The previous MINCORE no-go shows that an exact
relation, even together with a nonnegative zero-set-compatible defect, does not
determine quantitative calibration or transport regularity.

Here the missing information is supplied explicitly: two defect presentations
are related by two-sided calibration constants

```text
a * d <= d' <= b * d,   0 < a,   0 <= b.
```

The main results separate what is genuinely gauge-covariant from what is
calibration-dependent:

* exact relatedness and zero defect are forced to agree by a positive
  two-sided calibration;
* finite upper budgets transport with an explicit factor `b`;
* reverse budgets require the lower calibration `a`;
* an M-TC weighted finite-horizon certificate transports to the calibrated
  target defect by the same explicit terminal factor `b`;
* the exact relation alone still does not transport a numerical budget.

No frozen Core theorem, counted compression generator, or C1-C7 physical claim
is changed by this module.
-/

namespace UEOT.V3.Compression.TheoryCompletion.MinCore

open scoped BigOperators

universe u

/-- A non-circular quantitative bridge between two defect presentations.

The constants are deliberately explicit.  They are additional data, not
recoverable from the exact zero relation by the preceding MINCORE no-go.

No separate `same_rel` field is assumed: positive two-sided comparability,
together with each presentation's `zero_iff`, already forces the exact
relations to coincide. -/
structure DefectCalibration {X : Type u}
    (P Q : RelationDefectPresentation X) (a b : ℝ) : Prop where
  a_pos : 0 < a
  b_nonneg : 0 ≤ b
  lower : ∀ x y, a * P.defect x y ≤ Q.defect x y
  upper : ∀ x y, Q.defect x y ≤ b * P.defect x y

namespace DefectCalibration

variable {X : Type u}
variable {P Q : RelationDefectPresentation X}
variable {a b : ℝ}

/-- Zero defect is gauge-covariant under positive two-sided calibration. -/
theorem zero_defect_iff (C : DefectCalibration P Q a b) (x y : X) :
    P.defect x y = 0 ↔ Q.defect x y = 0 := by
  constructor
  · intro hP
    have hQle : Q.defect x y ≤ 0 := by
      simpa [hP] using C.upper x y
    exact le_antisymm hQle (Q.nonneg x y)
  · intro hQ
    have hscaled_le : a * P.defect x y ≤ 0 := by
      simpa [hQ] using C.lower x y
    have hscaled_nonneg : 0 ≤ a * P.defect x y :=
      mul_nonneg (le_of_lt C.a_pos) (P.nonneg x y)
    have hscaled : a * P.defect x y = 0 :=
      le_antisymm hscaled_le hscaled_nonneg
    rcases mul_eq_zero.mp hscaled with ha | hP
    · exact (ne_of_gt C.a_pos ha).elim
    · exact hP

/-- Exact relatedness is therefore gauge-covariant without an independent
same-relation assumption. -/
theorem rel_iff (C : DefectCalibration P Q a b) (x y : X) :
    P.rel x y ↔ Q.rel x y := by
  rw [← P.zero_iff x y, ← Q.zero_iff x y]
  exact C.zero_defect_iff x y

/-- A finite upper certificate in `P` transports to `Q` with the explicit
upper calibration factor. -/
theorem forward_budget
    (C : DefectCalibration P Q a b) {x y : X} {ε : ℝ}
    (hP : P.defect x y ≤ ε) :
    Q.defect x y ≤ b * ε := by
  exact
    (C.upper x y).trans
      (mul_le_mul_of_nonneg_left hP C.b_nonneg)

/-- A finite upper certificate in `Q` transports back to `P` only through
the independently supplied positive lower calibration. -/
theorem reverse_budget
    (C : DefectCalibration P Q a b) {x y : X} {ε : ℝ}
    (hQ : Q.defect x y ≤ ε) :
    P.defect x y ≤ ε / a := by
  apply (le_div_iff₀ C.a_pos).2
  simpa [mul_comm] using (C.lower x y).trans hQ

end DefectCalibration

/-- Positive rescaling is the canonical calibrated gauge transformation. -/
def rescaleCalibration
    {X : Type u} (P : RelationDefectPresentation X)
    (c : ℝ) (hc : 0 < c) :
    DefectCalibration P (P.rescale c hc) c c where
  a_pos := hc
  b_nonneg := le_of_lt hc
  lower := by
    intro x y
    exact le_rfl
  upper := by
    intro x y
    exact le_rfl

/-- M-TC conclusion transport under a stagewise calibrated target defect.

The full weighted recurrence is proved only once, for `P`, by the registered
M-TC theorem `weighted_chain_bound`.  A stagewise calibration then transports
that already-established finite-horizon certificate to `Q`.  The numerical
budget is not invariant: it acquires the explicit terminal factor `b n`.

This theorem does not claim that calibration alone transports the local
triangle or contraction hypotheses themselves.  Those remain properties of
the source certificate. -/
theorem calibrated_weighted_chain_bound
    {A : ℕ → Type*}
    (P Q : ∀ n, RelationDefectPresentation (A n))
    (a b : ℕ → ℝ)
    (C : ∀ n, DefectCalibration (P n) (Q n) (a n) (b n))
    (ideal actual : (n : ℕ) → A n)
    (step : ∀ n, A n → A (n + 1))
    (L ε : ℕ → ℝ)
    (hcontract : ∀ n,
      (P (n + 1)).defect (ideal (n + 1)) (step n (actual n)) ≤
        L n * (P n).defect (ideal n) (actual n))
    (htriangle : ∀ n,
      (P (n + 1)).defect (ideal (n + 1)) (actual (n + 1)) ≤
        (P (n + 1)).defect (ideal (n + 1)) (step n (actual n)) +
        (P (n + 1)).defect (step n (actual n)) (actual (n + 1)))
    (hlocal : ∀ n,
      (P (n + 1)).defect (step n (actual n)) (actual (n + 1)) ≤ ε n)
    (hL0 : ∀ n, 0 ≤ L n)
    (n : ℕ) :
    (Q n).defect (ideal n) (actual n) ≤
      b n *
        ((∏ j ∈ Finset.range n, L j) *
            (P 0).defect (ideal 0) (actual 0) +
          ∑ k ∈ Finset.range n,
            ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j) := by
  have hP :
      (P n).defect (ideal n) (actual n) ≤
        (∏ j ∈ Finset.range n, L j) *
            (P 0).defect (ideal 0) (actual 0) +
          ∑ k ∈ Finset.range n,
            ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j := by
    exact TransportCertificate.weighted_chain_bound
      (defect := fun t => (P t).defect)
      (ideal := ideal)
      (actual := actual)
      (step := step)
      (L := L)
      (ε := ε)
      hcontract htriangle hlocal hL0 n
  exact
    ((C n).upper (ideal n) (actual n)).trans
      (mul_le_mul_of_nonneg_left hP (C n).b_nonneg)

/-- Same exact relation is insufficient to preserve a fixed numerical budget.

This is the concrete failure witness required by the calibrated-comparison
program: the unit off-diagonal defect satisfies the unit budget, while its
factor-two rescaling presents exactly the same equality relation and violates
that same budget. -/
theorem same_relation_does_not_transport_unit_budget :
    ∃ P Q : RelationDefectPresentation Bool,
      P.rel = Q.rel ∧
      P.defect false true ≤ 1 ∧
      ¬ Q.defect false true ≤ 1 := by
  refine
    ⟨boolEqualityUnitDefect,
      boolEqualityUnitDefect.rescale 2 (by norm_num),
      rfl, ?_, ?_⟩
  · norm_num [boolEqualityUnitDefect]
  · norm_num
      [RelationDefectPresentation.rescale, boolEqualityUnitDefect]

end UEOT.V3.Compression.TheoryCompletion.MinCore
