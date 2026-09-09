import Mathlib.Data.Fin.Tuple.Basic

/-!
# P-PROC-01 foundation — exact finite-history carrier

For a discrete-time controlled process with state type `X` and action type
`A`, a history at time `n`

  H_n = (X_0, A_0, ..., A_{n-1}, X_n)

is represented exactly by a dependent sum whose fiber at `n` contains
`n+1` states and `n` actions.

This carrier has no finite-memory claim: the fiber grows with `n`.
-/

namespace UEOT.V3.FiniteHistory

universe uX uA

def HistoryFiber (X : Type uX) (A : Type uA) (n : ℕ) : Type (max uX uA) :=
  (Fin (n + 1) → X) × (Fin n → A)

def Carrier (X : Type uX) (A : Type uA) : Type (max uX uA) :=
  Sigma (HistoryFiber X A)

namespace Carrier

variable {X : Type uX} {A : Type uA}

def time (h : Carrier X A) : ℕ :=
  h.1

def states (h : Carrier X A) : Fin (h.1 + 1) → X :=
  h.2.1

def actions (h : Carrier X A) : Fin h.1 → A :=
  h.2.2

def current (h : Carrier X A) : X :=
  h.2.1 (Fin.last h.1)

def singleton (x₀ : X) : Carrier X A :=
  ⟨0, (fun _ => x₀), Fin.elim0⟩

def advance (h : Carrier X A) (a : A) (x' : X) : Carrier X A :=
  match h with
  | ⟨n, (xs, as)⟩ =>
      ⟨n + 1, (Fin.snoc xs x', Fin.snoc as a)⟩

@[simp] theorem time_singleton (x₀ : X) :
    time (singleton (A := A) x₀) = 0 := rfl

@[simp] theorem current_singleton (x₀ : X) :
    current (singleton (A := A) x₀) = x₀ := by
  rfl

@[simp] theorem time_advance (h : Carrier X A) (a : A) (x' : X) :
    time (advance h a x') = time h + 1 := by
  cases h
  rfl

@[simp] theorem current_advance (h : Carrier X A) (a : A) (x' : X) :
    current (advance h a x') = x' := by
  rcases h with ⟨n, xs, as⟩
  simp [advance, current, Fin.snoc_last]

theorem states_advance_old
    (n : ℕ) (xs : Fin (n + 1) → X) (as : Fin n → A)
    (a : A) (x' : X) (i : Fin (n + 1)) :
    states (advance (⟨n, (xs, as)⟩ : Carrier X A) a x') i.castSucc = xs i := by
  simp [states, advance, Fin.snoc]

theorem actions_advance_old
    (n : ℕ) (xs : Fin (n + 1) → X) (as : Fin n → A)
    (a : A) (x' : X) (i : Fin n) :
    actions (advance (⟨n, (xs, as)⟩ : Carrier X A) a x') i.castSucc = as i := by
  simp [actions, advance, Fin.snoc]

theorem action_advance_last
    (n : ℕ) (xs : Fin (n + 1) → X) (as : Fin n → A)
    (a : A) (x' : X) :
    actions (advance (⟨n, (xs, as)⟩ : Carrier X A) a x') (Fin.last n) = a := by
  simp [actions, advance, Fin.snoc_last]

theorem state_advance_last
    (n : ℕ) (xs : Fin (n + 1) → X) (as : Fin n → A)
    (a : A) (x' : X) :
    states (advance (⟨n, (xs, as)⟩ : Carrier X A) a x') (Fin.last (n + 1)) = x' := by
  simp [states, advance, Fin.snoc_last]

end Carrier

end UEOT.V3.FiniteHistory
