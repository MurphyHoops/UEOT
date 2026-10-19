import UEOTQM.Instrument
import UEOT.V3.Compression.QuotientDescent
import UEOT.V3.Compression.RecursiveSufficientState

/-!
# Quantum record laws, response quotients and conditional recursive updates

The inputs are the actual Kraus instruments of `Instrument.lean`. The response
of a density operator records the trace of every finite instrument word.
Consequently the family is closed under prefixing an allowed operation. This
closure, not a supplied update-conclusion field, proves recursive congruence.

The quantum model here has a fixed family of instruments acting on the stated
system. An omitted correlated environment is not asserted to be Markovian.
Every zero-probability branch returns `none`; it is not assigned a physical
posterior. The resulting total Option map can consume the already-proved UEOT
Core reachable-state descent theorem without hiding a partial/total mismatch.
-/

namespace UEOTQM

open Matrix Function
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι κ O A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype O]

abbrev Response (A O : Type*) := List (A × O) → ℝ

/-- An unnormalized state after a chronological finite record word. -/
def recordOperator (I : A → Instrument ι O κ) :
    List (A × O) → Operator ι → Operator ι
  | [], X => X
  | e :: w, X => recordOperator I w ((I e.1).branch e.2 X)

theorem recordOperator_posSemidef (I : A → Instrument ι O κ)
    (w : List (A × O)) {X : Operator ι} (hX : X.PosSemidef) :
    (recordOperator I w X).PosSemidef := by
  induction w generalizing X with
  | nil => exact hX
  | cons e w ih =>
    exact ih ((I e.1).branch_posSemidef e.2 hX)

theorem recordOperator_smul (I : A → Instrument ι O κ)
    (w : List (A × O)) (r : ℝ) (X : Operator ι) :
    recordOperator I w (r • X) = r • recordOperator I w X := by
  induction w generalizing X with
  | nil => rfl
  | cons e w ih =>
    simp only [recordOperator, Instrument.branch_smul, ih]

def response (I : A → Instrument ι O κ) (ρ : Density ι) : Response A O :=
  fun w => mass (recordOperator I w ρ.matrix)

theorem response_nonneg (I : A → Instrument ι O κ) (ρ : Density ι)
    (w : List (A × O)) : 0 ≤ response I ρ w :=
  mass_nonneg (recordOperator_posSemidef I w ρ.positive)

@[simp] theorem response_nil (I : A → Instrument ι O κ) (ρ : Density ι) :
    response I ρ [] = 1 := by
  exact ρ.mass_one

@[simp] theorem response_singleton (I : A → Instrument ι O κ) (ρ : Density ι)
    (e : A × O) : response I ρ [e] = (I e.1).probability ρ e.2 := rfl

/-- Sum of all record weights for a fixed finite sequence of controls. -/
def totalRecordMass (I : A → Instrument ι O κ) : List A → Operator ι → ℝ
  | [], X => mass X
  | a :: controls, X => ∑ o, totalRecordMass I controls ((I a).branch o X)

theorem totalRecordMass_eq_mass (I : A → Instrument ι O κ)
    (controls : List A) (X : Operator ι) :
    totalRecordMass I controls X = mass X := by
  induction controls generalizing X with
  | nil => rfl
  | cons a controls ih =>
    simp only [totalRecordMass, ih]
    exact (I a).sum_mass_branch X

theorem totalRecordMass_density (I : A → Instrument ι O κ)
    (controls : List A) (ρ : Density ι) :
    totalRecordMass I controls ρ.matrix = 1 := by
  rw [totalRecordMass_eq_mass, ρ.mass_one]

/-- Canonical indistinguishability uses all declared finite record responses. -/
def responseSetoid (I : A → Instrument ι O κ) : Setoid (Density ι) where
  r ρ σ := response I ρ = response I σ
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def responseClass (I : A → Instrument ι O κ) (ρ : Density ι) :
    Quotient (responseSetoid I) := Quotient.mk (responseSetoid I) ρ

theorem responseClass_surjective (I : A → Instrument ι O κ) :
    Surjective (responseClass I) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro ρ
  exact ⟨ρ, rfl⟩

/-- Actual reuse of M-QD: the quantum record response uniquely factors through
its operational equivalence classes. No Hilbert reconstruction is inferred. -/
theorem existsUnique_responseDecoder (I : A → Instrument ι O κ) :
    ∃! decoder : Quotient (responseSetoid I) → Response A O,
      decoder ∘ responseClass I = response I := by
  apply UEOT.V3.Compression.QuotientDescent.existsUnique_descend
    (responseClass I) (response I) (responseClass_surjective I)
  intro ρ σ h
  exact Quotient.exact h

theorem probability_eq_of_response_eq (I : A → Instrument ι O κ)
    {ρ σ : Density ι} (h : response I ρ = response I σ) (e : A × O) :
    (I e.1).probability ρ e.2 = (I e.1).probability σ e.2 := by
  exact congrFun h [e]

/-- The conditional continuation law is derived from the actual normalized
Kraus branch and the trace of the prefixed record, rather than assumed. -/
theorem response_posterior (I : A → Instrument ι O κ) (ρ : Density ι)
    (e : A × O) (hp : 0 < (I e.1).probability ρ e.2) (w : List (A × O)) :
    response I ((I e.1).posterior ρ e.2 hp) w =
      response I ρ (e :: w) / (I e.1).probability ρ e.2 := by
  unfold response
  rw [Instrument.posterior_matrix, recordOperator_smul, mass_smul]
  simp only [recordOperator, div_eq_mul_inv, mul_comm]

theorem posterior_response_eq (I : A → Instrument ι O κ)
    {ρ σ : Density ι} (h : response I ρ = response I σ) (e : A × O)
    (hρ : 0 < (I e.1).probability ρ e.2)
    (hσ : 0 < (I e.1).probability σ e.2) :
    response I ((I e.1).posterior ρ e.2 hρ) =
      response I ((I e.1).posterior σ e.2 hσ) := by
  funext w
  rw [response_posterior, response_posterior,
    congrFun h (e :: w), probability_eq_of_response_eq I h e]

/-- A total update with explicit failure on zero-evidence branches. -/
def nextResponse (I : A → Instrument ι O κ) (ρ : Density ι)
    (e : A × O) : Option (Response A O) :=
  if hp : 0 < (I e.1).probability ρ e.2 then
    some (response I ((I e.1).posterior ρ e.2 hp))
  else none

theorem nextResponse_eq_none_iff (I : A → Instrument ι O κ)
    (ρ : Density ι) (e : A × O) :
    nextResponse I ρ e = none ↔ (I e.1).probability ρ e.2 = 0 := by
  unfold nextResponse
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

theorem nextResponse_eq_of_response_eq (I : A → Instrument ι O κ)
    {ρ σ : Density ι} (h : response I ρ = response I σ) (e : A × O) :
    nextResponse I ρ e = nextResponse I σ e := by
  have he := probability_eq_of_response_eq I h e
  by_cases hρ : 0 < (I e.1).probability ρ e.2
  · have hσ : 0 < (I e.1).probability σ e.2 := by rw [← he]; exact hρ
    rw [nextResponse, nextResponse, dif_pos hρ, dif_pos hσ]
    exact congrArg some (posterior_response_eq I h e hρ hσ)
  · have hσ : ¬ 0 < (I e.1).probability σ e.2 := by rw [← he]; exact hρ
    rw [nextResponse, nextResponse, dif_neg hρ, dif_neg hσ]

theorem nextResponse_inputFiberCompatible (I : A → Instrument ι O κ) :
    UEOT.V3.Compression.RecursiveSufficientState.InputFiberCompatible
      (response I) (nextResponse I) := by
  intro ρ σ h e
  exact nextResponse_eq_of_response_eq I h e

/-- Actual reuse of the canonical Core recursive theorem, with its total-input
contract satisfied by the proved Option-valued quantum update. -/
theorem existsUnique_reachableResponseUpdate (I : A → Instrument ι O κ) :
    ∃! U : Set.range (response I) → (A × O) → Option (Response A O),
      ∀ ρ e,
        U (UEOT.V3.Compression.RecursiveSufficientState.toReachable (response I) ρ) e =
          nextResponse I ρ e :=
  UEOT.V3.Compression.RecursiveSufficientState.existsUnique_reachableUpdate
    (response I) (nextResponse I) (nextResponse_inputFiberCompatible I)

/-- The positive branch carries the actual posterior as a witness that its
response is reachable. Thus a successful update can be used as the input of
another update on the same reachable-state type. -/
def nextReachableResponse (I : A → Instrument ι O κ) (ρ : Density ι)
    (e : A × O) : Option (Set.range (response I)) :=
  if hp : 0 < (I e.1).probability ρ e.2 then
    some (UEOT.V3.Compression.RecursiveSufficientState.toReachable
      (response I) ((I e.1).posterior ρ e.2 hp))
  else none

/-- Forgetting the reachability witness recovers the original response-valued
interface, including its explicit failure on zero-probability branches. -/
@[simp] theorem nextReachableResponse_map_val (I : A → Instrument ι O κ)
    (ρ : Density ι) (e : A × O) :
    Option.map Subtype.val (nextReachableResponse I ρ e) = nextResponse I ρ e := by
  unfold nextReachableResponse nextResponse
  split_ifs <;> rfl

theorem nextReachableResponse_eq_of_response_eq (I : A → Instrument ι O κ)
    {ρ σ : Density ι} (h : response I ρ = response I σ) (e : A × O) :
    nextReachableResponse I ρ e = nextReachableResponse I σ e := by
  have he := probability_eq_of_response_eq I h e
  by_cases hρ : 0 < (I e.1).probability ρ e.2
  · have hσ : 0 < (I e.1).probability σ e.2 := by rw [← he]; exact hρ
    rw [nextReachableResponse, nextReachableResponse, dif_pos hρ, dif_pos hσ]
    apply congrArg some
    apply Subtype.ext
    exact posterior_response_eq I h e hρ hσ
  · have hσ : ¬ 0 < (I e.1).probability σ e.2 := by rw [← he]; exact hρ
    rw [nextReachableResponse, nextReachableResponse, dif_neg hρ, dif_neg hσ]

theorem nextReachableResponse_inputFiberCompatible (I : A → Instrument ι O κ) :
    UEOT.V3.Compression.RecursiveSufficientState.InputFiberCompatible
      (response I) (nextReachableResponse I) := by
  intro ρ σ h e
  exact nextReachableResponse_eq_of_response_eq I h e

/-- Actual Core descent now yields a closed recursive interface: every
successful output belongs to the same reachable-state type as the input.
Fiber compatibility is proved from the quantum posterior response law. -/
theorem existsUnique_closedReachableUpdate (I : A → Instrument ι O κ) :
    ∃! U : Set.range (response I) → (A × O) → Option (Set.range (response I)),
      ∀ ρ e,
        U (UEOT.V3.Compression.RecursiveSufficientState.toReachable (response I) ρ) e =
          nextReachableResponse I ρ e :=
  UEOT.V3.Compression.RecursiveSufficientState.existsUnique_reachableUpdate
    (response I) (nextReachableResponse I) (nextReachableResponse_inputFiberCompatible I)

end

end UEOTQM
