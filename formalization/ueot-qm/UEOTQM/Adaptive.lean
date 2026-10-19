import UEOTQM.FiniteCoordinates
import Mathlib.Data.Fintype.BigOperators

/-!
# Complete finite adaptive quantum protocols

The controller is a finite tree whose continuation is specified for every
outcome, including zero-probability outcomes. Leaves carry their actual
chronological action/outcome words. The normalization theorem is derived from
Kraus completeness for arbitrary subnormalized operator inputs, then specialized
to density states. Equality of all-word responses therefore preserves every
complete finite adaptive protocol law.

This is a mathematical interpreter for the common finite outcome index of the
Lean instrument family. The Python tree serialization and its varying outcome
index adapters have their own refinement obligations.
-/

namespace UEOTQM.Adaptive

open Matrix Function
open scoped BigOperators ComplexOrder

noncomputable section

/-- A deterministic finite causal controller with complete outcome branches. -/
inductive Protocol (A O : Type*) where
  | stop : Protocol A O
  | node (action : A) (next : O → Protocol A O) : Protocol A O

namespace Protocol

variable {A O : Type*}

/-- A leaf remembers the successive outcome choices of this particular tree. -/
def Leaf : Protocol A O → Type _
  | .stop => PUnit
  | .node _ next => (o : O) × Leaf (next o)

/-- Finiteness is obtained by induction, rather than assumed for the law. -/
instance leafFintype [Fintype O] (π : Protocol A O) : Fintype (Leaf π) := by
  induction π with
  | stop => exact inferInstanceAs (Fintype PUnit)
  | node a next ih =>
    letI : ∀ o, Fintype (Leaf (next o)) := ih
    exact inferInstanceAs (Fintype ((o : O) × Leaf (next o)))

/-- The actual chronological word selected by a leaf. -/
def word : (π : Protocol A O) → Leaf π → List (A × O)
  | .stop, _ => []
  | .node a next, l => (a, l.1) :: word (next l.1) l.2

/-- Distinct leaves have distinct recorded action/outcome words. -/
theorem word_injective (π : Protocol A O) : Injective (word π) := by
  induction π with
  | stop =>
    intro x y _
    cases x
    cases y
    rfl
  | node a next ih =>
    intro x y h
    rcases x with ⟨o, x⟩
    rcases y with ⟨p, y⟩
    change (a, o) :: word (next o) x = (a, p) :: word (next p) y at h
    have hop : o = p := congrArg Prod.snd (List.cons.inj h).1
    cases hop
    have hxy := ih o (List.cons.inj h).2
    cases hxy
    rfl

end Protocol

variable {ι κ O A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype O]

/-- No intermediate branch normalization is used in a full record weight. -/
def leafWeight (I : A → Instrument ι O κ) (π : Protocol A O)
    (X : Operator ι) (l : π.Leaf) : ℝ :=
  mass (recordOperator I (π.word l) X)

/-- Complete finite adaptive branching preserves total input mass. -/
theorem sum_leafWeight (I : A → Instrument ι O κ) (π : Protocol A O)
    (X : Operator ι) : (∑ l : π.Leaf, leafWeight I π X l) = mass X := by
  induction π generalizing X with
  | stop =>
    change (∑ _ : PUnit, mass X) = mass X
    simp
  | node a next ih =>
    change (∑ l : (o : O) × (next o).Leaf,
      mass (recordOperator I ((next l.1).word l.2) ((I a).branch l.1 X))) = mass X
    rw [Fintype.sum_sigma]
    calc
      (∑ o, ∑ l : (next o).Leaf,
          mass (recordOperator I ((next o).word l) ((I a).branch o X))) =
          ∑ o, mass ((I a).branch o X) := by
        apply Finset.sum_congr rfl
        intro o _
        exact ih o ((I a).branch o X)
      _ = mass X := (I a).sum_mass_branch X

theorem leafWeight_nonneg (I : A → Instrument ι O κ) (π : Protocol A O)
    {X : Operator ι} (hX : X.PosSemidef) (l : π.Leaf) :
    0 ≤ leafWeight I π X l :=
  mass_nonneg (recordOperator_posSemidef I (π.word l) hX)

def leafProbability (I : A → Instrument ι O κ) (π : Protocol A O)
    (ρ : Density ι) : π.Leaf → ℝ := leafWeight I π ρ.matrix

@[simp] theorem leafProbability_eq_response (I : A → Instrument ι O κ)
    (π : Protocol A O) (ρ : Density ι) (l : π.Leaf) :
    leafProbability I π ρ l = response I ρ (π.word l) := rfl

theorem leafProbability_nonneg (I : A → Instrument ι O κ)
    (π : Protocol A O) (ρ : Density ι) (l : π.Leaf) :
    0 ≤ leafProbability I π ρ l := leafWeight_nonneg I π ρ.positive l

/-- The leaf vector is an actual finite probability law. -/
theorem sum_leafProbability (I : A → Instrument ι O κ)
    (π : Protocol A O) (ρ : Density ι) :
    (∑ l : π.Leaf, leafProbability I π ρ l) = 1 := by
  change (∑ l : π.Leaf, leafWeight I π ρ.matrix l) = 1
  rw [sum_leafWeight, ρ.mass_one]

theorem leafProbability_le_one (I : A → Instrument ι O κ)
    (π : Protocol A O) (ρ : Density ι) (l : π.Leaf) :
    leafProbability I π ρ l ≤ 1 := by
  calc
    leafProbability I π ρ l ≤ ∑ k : π.Leaf, leafProbability I π ρ k :=
      Finset.single_le_sum (fun k _ => leafProbability_nonneg I π ρ k)
        (Finset.mem_univ l)
    _ = 1 := sum_leafProbability I π ρ

/-- The existing all-word quotient preserves every adaptive tree law. -/
theorem leafProbability_eq_of_response_eq (I : A → Instrument ι O κ)
    {ρ σ : Density ι} (h : response I ρ = response I σ) (π : Protocol A O) :
    leafProbability I π ρ = leafProbability I π σ := by
  funext l
  exact congrFun h (π.word l)

/-- The finite coordinate matrices compute every leaf of the actual adaptive
law, using the chronological word belonging to that leaf. -/
theorem leafProbability_eq_recordCoordinates_unit {β : Type*} [Fintype β]
    (I : A → Instrument ι O κ) (C : FiniteObservablePresentation I β)
    (π : Protocol A O) (ρ : Density ι) (l : π.Leaf) :
    leafProbability I π ρ l =
      C.recordCoordinates (π.word l) (C.coordinates ρ) C.unitIndex :=
  C.response_eq_recordCoordinates_unit ρ (π.word l)

/-- A locally checked finite observable presentation preserves every complete
finite adaptive protocol law, without a horizon-specific equivalence premise. -/
theorem leafProbability_eq_of_coordinates_eq {β : Type*} [Fintype β]
    (I : A → Instrument ι O κ) (C : FiniteObservablePresentation I β)
    {ρ σ : Density ι} (h : C.coordinates ρ = C.coordinates σ) (π : Protocol A O) :
    leafProbability I π ρ = leafProbability I π σ :=
  leafProbability_eq_of_response_eq I ((C.coordinates_eq_iff_response_eq ρ σ).mp h) π

/-- A positive observed prefix is conditioned exactly once before continuation. -/
theorem leafProbability_posterior (I : A → Instrument ι O κ)
    (ρ : Density ι) (e : A × O) (hp : 0 < (I e.1).probability ρ e.2)
    (π : Protocol A O) (l : π.Leaf) :
    leafProbability I π ((I e.1).posterior ρ e.2 hp) l =
      response I ρ (e :: π.word l) / (I e.1).probability ρ e.2 :=
  response_posterior I ρ e hp (π.word l)

end

end UEOTQM.Adaptive
