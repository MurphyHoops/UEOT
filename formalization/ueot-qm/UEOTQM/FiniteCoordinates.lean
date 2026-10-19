import UEOTQM.Observables

/-!
# Finite certificates and closed quantum response coordinates

A certificate contains finitely many actual record words, the empty-word
index, and an exact expansion of every one-step pullback in those word
effects. These are local algebraic witnesses. Neither all-word sufficiency
nor posterior congruence is a certificate field: both are proved below.

Linear independence is not needed for sufficiency. A checker may additionally
certify independence to obtain a basis, but a redundant closed presentation
has the same record-response semantics. This file proves the mathematical
certificate contract; it does not identify a Python implementation with Lean.
-/

namespace UEOTQM

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι κ O A β : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype O] [Fintype β]

/-- A finite, generated, locally closed observable presentation. The row
convention is `pullback(B_j) = ∑ k, coeff e j k • B_k`, hence `x' = coeff e * x`
before conditioning. Only exact local matrix identities are input. -/
structure FiniteObservablePresentation (I : A → Instrument ι O κ)
    (β : Type*) [Fintype β] where
  word : β → List (A × O)
  unitIndex : β
  unit_word : word unitIndex = []
  coeff : (A × O) → β → β → ℝ
  pullback_eq : ∀ (e : A × O) (j : β),
    heisenberg ((I e.1).kraus e.2) (recordEffect I (word j)) =
      ∑ k, coeff e j k • recordEffect I (word k)

namespace FiniteObservablePresentation

variable {I : A → Instrument ι O κ} (C : FiniteObservablePresentation I β)

def observable (j : β) : Operator ι := recordEffect I (C.word j)

def span : Submodule ℝ (Operator ι) := Submodule.span ℝ (Set.range C.observable)

theorem observable_mem_span (j : β) : C.observable j ∈ C.span :=
  Submodule.subset_span ⟨j, rfl⟩

@[simp] theorem observable_unit : C.observable C.unitIndex = 1 := by
  simp only [observable, C.unit_word, recordEffect]

theorem one_mem_span : (1 : Operator ι) ∈ C.span := by
  rw [← C.observable_unit]
  exact C.observable_mem_span C.unitIndex

theorem pullback_observable (e : A × O) (j : β) :
    heisenberg ((I e.1).kraus e.2) (C.observable j) =
      ∑ k, C.coeff e j k • C.observable k := C.pullback_eq e j

/-- Checking pullback identities only on the finite generating family proves
invariance of its complete real span. -/
theorem span_pullbackClosed : PullbackClosed I C.span := by
  intro e E hE
  change E ∈ Submodule.span ℝ (Set.range C.observable) at hE
  induction hE using Submodule.span_induction with
  | mem E hE =>
    rcases hE with ⟨j, rfl⟩
    rw [C.pullback_observable]
    exact Submodule.sum_mem _ (fun k _ => C.span.smul_mem _ (C.observable_mem_span k))
  | zero =>
    rw [heisenberg_zero]
    exact C.span.zero_mem
  | add E F hE hF ihE ihF =>
    rw [heisenberg_add]
    exact C.span.add_mem ihE ihF
  | smul r E hE ih =>
    rw [heisenberg_smul]
    exact C.span.smul_mem r ih

/-- Generatedness proves one inclusion; the identity and local closure prove
the other. The certificate therefore covers every finite word. -/
theorem span_eq_observableSpace : C.span = observableSpace I := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro E ⟨j, rfl⟩
    exact recordEffect_mem I (C.word j)
  · exact observableSpace_le_of_closed I C.span C.one_mem_span C.span_pullbackClosed

theorem recordEffect_mem_span (w : List (A × O)) : recordEffect I w ∈ C.span := by
  rw [C.span_eq_observableSpace]
  exact recordEffect_mem I w

/-- Homogeneous coordinates on all operators, retaining the trace coordinate. -/
def operatorCoordinates (X : Operator ι) : β → ℝ := fun j => pairing (C.observable j) X

def coordinates (ρ : Density ι) : β → ℝ := C.operatorCoordinates ρ.matrix

theorem operatorCoordinates_unit (X : Operator ι) :
    C.operatorCoordinates X C.unitIndex = mass X := by
  change pairing (C.observable C.unitIndex) X = mass X
  rw [C.observable_unit, pairing_one]

@[simp] theorem coordinates_unit (ρ : Density ι) : C.coordinates ρ C.unitIndex = 1 := by
  exact (C.operatorCoordinates_unit ρ.matrix).trans ρ.mass_one

theorem coordinates_apply (ρ : Density ι) (j : β) :
    C.coordinates ρ j = response I ρ (C.word j) :=
  (response_eq_pairing I ρ (C.word j)).symm

/-- Finite coordinates classify exactly the complete record-response classes. -/
theorem coordinates_eq_iff_response_eq (ρ σ : Density ι) :
    C.coordinates ρ = C.coordinates σ ↔ response I ρ = response I σ := by
  constructor
  · intro h
    apply (response_eq_iff_pairing_observableSpace I ρ σ).mpr
    intro E hE
    have hgen : Set.EqOn (pairingLinear ρ.matrix) (pairingLinear σ.matrix)
        (Set.range C.observable) := by
      rintro F ⟨j, rfl⟩
      exact congrFun h j
    have hE' : E ∈ C.span := by rwa [C.span_eq_observableSpace]
    exact LinearMap.eqOn_span hgen hE'
  · intro h
    funext j
    rw [C.coordinates_apply, C.coordinates_apply, h]

/-- Matrix-vector multiplication with the row convention of `pullback_eq`. -/
def applyBranch (e : A × O) (x : β → ℝ) : β → ℝ :=
  fun j => ∑ k, C.coeff e j k * x k

/-- The finite matrix acts exactly like the actual Kraus branch, without
normalizing or invoking state positivity. -/
theorem operatorCoordinates_branch (e : A × O) (X : Operator ι) :
    C.operatorCoordinates ((I e.1).branch e.2 X) =
      C.applyBranch e (C.operatorCoordinates X) := by
  funext j
  change pairing (recordEffect I (C.word j)) (krausMap ((I e.1).kraus e.2) X) =
    ∑ k, C.coeff e j k * pairing (recordEffect I (C.word k)) X
  rw [pairing_heisenberg, C.pullback_eq]
  simp only [pairing_sum_left, pairing_smul_left]

/-- Chronological unnormalized record evaluation, entirely in finite
coordinates. Mass is retained until conditioning is explicitly requested. -/
def recordCoordinates (C : FiniteObservablePresentation I β) :
    List (A × O) → (β → ℝ) → (β → ℝ)
  | [], x => x
  | e :: w, x => recordCoordinates C w (C.applyBranch e x)

theorem operatorCoordinates_record (w : List (A × O)) (X : Operator ι) :
    C.operatorCoordinates (recordOperator I w X) =
      C.recordCoordinates w (C.operatorCoordinates X) := by
  induction w generalizing X with
  | nil => rfl
  | cons e w ih =>
    simp only [recordOperator, recordCoordinates, ih, C.operatorCoordinates_branch]

/-- Every finite record weight can be read from a sequence of the certified
finite matrices. This is a uniform all-word result. -/
theorem response_eq_recordCoordinates_unit (ρ : Density ι) (w : List (A × O)) :
    response I ρ w = C.recordCoordinates w (C.coordinates ρ) C.unitIndex :=
  (C.operatorCoordinates_unit (recordOperator I w ρ.matrix)).symm.trans
    (congrFun (C.operatorCoordinates_record w ρ.matrix) C.unitIndex)

/-- The distinguished coordinate reads the real branch probability. -/
theorem probability_eq_applyBranch_unit (ρ : Density ι) (e : A × O) :
    (I e.1).probability ρ e.2 = (C.applyBranch e (C.coordinates ρ)) C.unitIndex :=
  (C.operatorCoordinates_unit ((I e.1).branch e.2 ρ.matrix)).symm.trans
    (congrFun (C.operatorCoordinates_branch e ρ.matrix) C.unitIndex)

/-- Conditional coordinate evolution is derived from the actual posterior. -/
theorem coordinates_posterior (ρ : Density ι) (e : A × O)
    (hp : 0 < (I e.1).probability ρ e.2) (j : β) :
    C.coordinates ((I e.1).posterior ρ e.2 hp) j =
      C.applyBranch e (C.coordinates ρ) j / (I e.1).probability ρ e.2 := by
  change pairing (C.observable j) ((I e.1).posterior ρ e.2 hp).matrix = _
  rw [Instrument.posterior_matrix, pairing_smul_right]
  have h := congrFun (C.operatorCoordinates_branch e ρ.matrix) j
  change pairing (C.observable j) ((I e.1).branch e.2 ρ.matrix) =
    C.applyBranch e (C.coordinates ρ) j at h
  rw [h]
  simp only [div_eq_mul_inv, mul_comm]

/-- Algebraic normalized update on ambient coordinate vectors. A physical
interpretation of this formula requires a reachable input and positive mass. -/
def normalizedBranch (e : A × O) (x : β → ℝ) : β → ℝ :=
  fun j => C.applyBranch e x j / C.applyBranch e x C.unitIndex

theorem coordinates_posterior_eq_normalizedBranch (ρ : Density ι) (e : A × O)
    (hp : 0 < (I e.1).probability ρ e.2) :
    C.coordinates ((I e.1).posterior ρ e.2 hp) =
      C.normalizedBranch e (C.coordinates ρ) := by
  funext j
  rw [C.coordinates_posterior]
  change _ = C.applyBranch e (C.coordinates ρ) j /
    C.applyBranch e (C.coordinates ρ) C.unitIndex
  rw [← C.probability_eq_applyBranch_unit]

/-- Positive coordinate updates remain in the same physical reachable image;
the witness is the actual quantum posterior. -/
theorem normalizedBranch_mem_range {x : β → ℝ} (hx : x ∈ Set.range C.coordinates)
    (e : A × O) (hp : 0 < C.applyBranch e x C.unitIndex) :
    C.normalizedBranch e x ∈ Set.range C.coordinates := by
  rcases hx with ⟨ρ, rfl⟩
  have hρ : 0 < (I e.1).probability ρ e.2 := by
    rwa [C.probability_eq_applyBranch_unit]
  exact ⟨(I e.1).posterior ρ e.2 hρ,
    C.coordinates_posterior_eq_normalizedBranch ρ e hρ⟩

/-- A total ambient-vector interface with explicit failure at nonpositive
evidence; its physical meaning is certified on the reachable image. -/
def coordinateUpdate (x : β → ℝ) (e : A × O) : Option (β → ℝ) :=
  if 0 < C.applyBranch e x C.unitIndex then some (C.normalizedBranch e x) else none

/-- The actual matrix update, with a proof-carrying reachable output. The
matrix-vector computation uses only `x`; a density representative occurs
solely inside the proof of membership, not in the value being computed. -/
def closedCoordinateUpdate (x : Set.range C.coordinates) (e : A × O) :
    Option (Set.range C.coordinates) :=
  if hp : 0 < C.applyBranch e x.val C.unitIndex then
    some ⟨C.normalizedBranch e x.val, C.normalizedBranch_mem_range x.property e hp⟩
  else none

@[simp] theorem closedCoordinateUpdate_map_val (x : Set.range C.coordinates) (e : A × O) :
    Option.map Subtype.val (C.closedCoordinateUpdate x e) = C.coordinateUpdate x.val e := by
  unfold closedCoordinateUpdate coordinateUpdate
  split_ifs <;> rfl

theorem coordinateUpdate_eq_posterior (ρ : Density ι) (e : A × O)
    (hp : 0 < (I e.1).probability ρ e.2) :
    C.coordinateUpdate (C.coordinates ρ) e =
      some (C.coordinates ((I e.1).posterior ρ e.2 hp)) := by
  have hcoords : 0 < C.applyBranch e (C.coordinates ρ) C.unitIndex := by
    rwa [← C.probability_eq_applyBranch_unit]
  rw [coordinateUpdate, if_pos hcoords, ← C.coordinates_posterior_eq_normalizedBranch ρ e hp]

theorem coordinateUpdate_eq_none_iff (ρ : Density ι) (e : A × O) :
    C.coordinateUpdate (C.coordinates ρ) e = none ↔ (I e.1).probability ρ e.2 = 0 := by
  unfold coordinateUpdate
  rw [← C.probability_eq_applyBranch_unit]
  split_ifs with hp
  · constructor
    · intro h
      cases h
    · intro h
      exact (hp.ne' h).elim
  · constructor
    · intro _
      exact le_antisymm (le_of_not_gt hp) ((I e.1).probability_nonneg ρ e.2)
    · intro _
      rfl

end FiniteObservablePresentation

end

end UEOTQM
