import UEOTQM.Exact
import UEOTQM.Adaptive

/-!
# Kernel-checked exact certificates for finite quantum response coordinates

`Data` contains only finite rational tables and record words. `Conditions`
checks nonnegative weights, weighted completeness, the empty word, the actual
word effect of every supplied basis matrix, and every local pullback identity.
Neither all-word sufficiency nor posterior congruence is a data field.

`check` is computable. A concrete generated proof of `check data = true` is
checked by Lean's kernel; the generic construction below then gives ordinary
complex quantum instruments and a `FiniteObservablePresentation`. This proves
the meaning of each accepted instance, not universal correctness of an
external JSON parser, search procedure, or Python source-code exporter.
-/

namespace UEOTQM.ExactCertificate

open Matrix
open scoped BigOperators

variable {d a o k r : ℕ}

/-- Finite exact input tables. Labels are external metadata; the semantic
indices and all arithmetic used here are explicit finite data. -/
structure Data (d a o k r : ℕ) where
  weight : Fin a → Fin o → Fin k → ℚ
  kraus : Fin a → Fin o → Fin k → Exact.OperatorData (Fin d)
  basis : Fin r → Exact.OperatorData (Fin d)
  word : Fin r → List (Fin a × Fin o)
  unitIndex : Fin r
  coeff : (Fin a × Fin o) → Fin r → Fin r → ℚ

/-- Exact backward effect of a chronological word. The recursive order agrees
with the existing complex `UEOTQM.recordEffect`. -/
def exactRecordEffect (D : Data d a o k r) :
    List (Fin a × Fin o) → Exact.OperatorData (Fin d)
  | [] => Exact.MatrixData.one
  | e :: w => Exact.weightedPullback Finset.univ
      (D.weight e.1 e.2) (D.kraus e.1 e.2) (exactRecordEffect D w)

/-- The entire instrument completeness table, including every outcome. -/
def exactCompleteness (D : Data d a o k r) (act : Fin a) :
    Exact.OperatorData (Fin d) :=
  Exact.MatrixData.sum Finset.univ fun out =>
    Exact.weightedCompleteness Finset.univ (D.weight act out) (D.kraus act out)

/-- A local finite row expansion, retaining the rational row convention. -/
def exactExpansion (D : Data d a o k r) (e : Fin a × Fin o) (j : Fin r) :
    Exact.OperatorData (Fin d) :=
  Exact.MatrixData.sum Finset.univ fun i =>
    Exact.MatrixData.scale (D.coeff e j i) (D.basis i)

/-- Independently decidable local obligations. The numeric basis is bound to
the supplied word witnesses, rather than merely assumed to be generated. -/
def Conditions (D : Data d a o k r) : Prop :=
  (∀ act out term, 0 ≤ D.weight act out term) ∧
  (∀ act, exactCompleteness D act = Exact.MatrixData.one) ∧
  D.word D.unitIndex = [] ∧
  (∀ j, exactRecordEffect D (D.word j) = D.basis j) ∧
  (∀ e j, Exact.weightedPullback Finset.univ
    (D.weight e.1 e.2) (D.kraus e.1 e.2) (D.basis j) = exactExpansion D e j)

instance conditionsDecidable (D : Data d a o k r) : Decidable (Conditions D) := by
  unfold Conditions
  infer_instance

/-- A Boolean evaluator of the explicit finite algebraic conditions. -/
def check (D : Data d a o k r) : Bool := decide (Conditions D)

theorem check_eq_true_iff (D : Data d a o k r) : check D = true ↔ Conditions D := by
  exact decide_eq_true_iff

theorem check_sound (D : Data d a o k r) (h : check D = true) : Conditions D :=
  (check_eq_true_iff D).mp h

noncomputable section

/-- Rational weighted completeness is transported to actual complex matrices;
ordinary Kraus completeness is then derived by the square-root scaling bridge. -/
def weightedInstrument (D : Data d a o k r) (h : check D = true) (act : Fin a) :
    WeightedInstrument (Fin d) (Fin o) (Fin k) where
  weight out term := (D.weight act out term : ℝ)
  kraus out term := (D.kraus act out term).toMatrix
  weight_nonneg := by
    intro out term
    exact_mod_cast (check_sound D h).1 act out term
  complete := by
    have hc := congrArg Exact.MatrixData.toMatrix ((check_sound D h).2.1 act)
    simpa only [exactCompleteness, Exact.MatrixData.toMatrix_sum,
      Exact.toMatrix_weightedCompleteness, Exact.MatrixData.toMatrix_one] using hc

/-- Actual ordinary complex instruments associated with checked exact data. -/
def instrumentFamily (D : Data d a o k r) (h : check D = true) :
    Fin a → Instrument (Fin d) (Fin o) (Fin k) :=
  fun act => (weightedInstrument D h act).toInstrument

/-- The interpreted branch is exactly the original rational weighted formula. -/
theorem branch_eq_exact (D : Data d a o k r) (h : check D = true)
    (e : Fin a × Fin o) (X : Exact.OperatorData (Fin d)) :
    (instrumentFamily D h e.1).branch e.2 X.toMatrix =
      (Exact.weightedBranch Finset.univ (D.weight e.1 e.2)
        (D.kraus e.1 e.2) X).toMatrix := by
  rw [instrumentFamily, WeightedInstrument.toInstrument_branch,
    Exact.toMatrix_weightedBranch_univ]
  rfl

theorem heisenberg_eq_exact (D : Data d a o k r) (h : check D = true)
    (e : Fin a × Fin o) (E : Exact.OperatorData (Fin d)) :
    heisenberg ((instrumentFamily D h e.1).kraus e.2) E.toMatrix =
      (Exact.weightedPullback Finset.univ (D.weight e.1 e.2)
        (D.kraus e.1 e.2) E).toMatrix := by
  rw [instrumentFamily, WeightedInstrument.toInstrument_heisenberg,
    Exact.toMatrix_weightedPullback_univ]
  rfl

/-- Every exact word effect interprets as the actual complex word effect,
without any bound on the length of the word. -/
theorem exactRecordEffect_toMatrix (D : Data d a o k r) (h : check D = true)
    (w : List (Fin a × Fin o)) :
    (exactRecordEffect D w).toMatrix = recordEffect (instrumentFamily D h) w := by
  induction w with
  | nil => exact Exact.MatrixData.toMatrix_one
  | cons e w ih =>
    rw [exactRecordEffect, recordEffect, ← ih]
    exact (heisenberg_eq_exact D h e (exactRecordEffect D w)).symm

/-- Binding of each supplied numeric basis matrix to its checked word witness. -/
theorem basis_toMatrix (D : Data d a o k r) (h : check D = true) (j : Fin r) :
    (D.basis j).toMatrix = recordEffect (instrumentFamily D h) (D.word j) := by
  rw [← (check_sound D h).2.2.2.1 j]
  exact exactRecordEffect_toMatrix D h (D.word j)

/-- The local checker constructs the existing all-word coordinate certificate.
No global response equivalence is assumed by this constructor. -/
def presentation (D : Data d a o k r) (h : check D = true) :
    FiniteObservablePresentation (instrumentFamily D h) (Fin r) where
  word := D.word
  unitIndex := D.unitIndex
  unit_word := (check_sound D h).2.2.1
  coeff e j i := (D.coeff e j i : ℝ)
  pullback_eq := by
    intro e j
    rw [← basis_toMatrix D h j, heisenberg_eq_exact D h e (D.basis j)]
    have hc := congrArg Exact.MatrixData.toMatrix ((check_sound D h).2.2.2.2 e j)
    simpa only [exactExpansion, Exact.MatrixData.toMatrix_sum,
      Exact.MatrixData.toMatrix_scale, basis_toMatrix D h] using hc

/-- Finite coordinate equality is equivalent to agreement on every finite
record of the checked ordinary quantum instrument family. -/
theorem coordinates_eq_iff_response_eq (D : Data d a o k r) (h : check D = true)
    (ρ σ : Density (Fin d)) :
    (presentation D h).coordinates ρ = (presentation D h).coordinates σ ↔
      response (instrumentFamily D h) ρ = response (instrumentFamily D h) σ :=
  (presentation D h).coordinates_eq_iff_response_eq ρ σ

theorem response_eq_recordCoordinates_unit (D : Data d a o k r) (h : check D = true)
    (ρ : Density (Fin d)) (w : List (Fin a × Fin o)) :
    response (instrumentFamily D h) ρ w =
      (presentation D h).recordCoordinates w ((presentation D h).coordinates ρ) D.unitIndex :=
  (presentation D h).response_eq_recordCoordinates_unit ρ w

/-- The same finite coordinates suffice for every complete finite adaptive
tree over the checked alphabet, including zero-probability leaves. -/
theorem adaptive_leafProbability_eq (D : Data d a o k r) (h : check D = true)
    (ρ σ : Density (Fin d))
    (hcoords : (presentation D h).coordinates ρ = (presentation D h).coordinates σ)
    (π : Adaptive.Protocol (Fin a) (Fin o)) :
    Adaptive.leafProbability (instrumentFamily D h) π ρ =
      Adaptive.leafProbability (instrumentFamily D h) π σ :=
  Adaptive.leafProbability_eq_of_coordinates_eq (instrumentFamily D h)
    (presentation D h) hcoords π

end

end UEOTQM.ExactCertificate
