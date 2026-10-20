import UEOTQM.HistoryChannels
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite causal histories and per-action record budgets

The controller is defined only on the finite horizon. Its history is the whole
outcome word. The actual history-reading CPTP steps retain this word and the
quantum memory; they read/dephase the history rather than implement coherent
control. Both implementations use the same causal action function.
-/

namespace UEOTQM.ActionRecordBudget

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Exactly n recorded outcomes, in chronological order. -/
abbrev History (O : Type*) (n : ℕ) := Fin n → O

/-- A common causal action rule defined at every time in a finite horizon. -/
def Controller (A O : Type*) (N : ℕ) := ∀ t : Fin N, History O t.val → A

namespace Controller

variable {A O : Type*} {N : ℕ}

/-- Keep all control times except the last one. -/
def dropLast (C : Controller A O (N + 1)) : Controller A O N :=
  fun t h => C t.castSucc h

/-- Fix the first recorded outcome and continue the same causal rule. -/
def shift (C : Controller A O (N + 1)) (o : O) : Controller A O N :=
  fun t h => C t.succ (Fin.cons (α := fun _ => O) o h)

theorem dropLast_shift (C : Controller A O (N + 2)) (o : O) :
    dropLast (shift C o) = shift (dropLast C) o := by
  rfl

/-- The actual chronological action/outcome word selected by a history. -/
def word : {N : ℕ} → Controller A O N → History O N → List (A × O)
  | 0, _, _ => []
  | n + 1, C, h => (C 0 Fin.elim0, h 0) :: word (shift C (h 0)) (Fin.tail h)

theorem word_length (C : Controller A O N) (h : History O N) :
    (word C h).length = N := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [word, List.length_cons, ih]

/-- The existing finite adaptive-tree interpreter, with every outcome branch. -/
def protocol : {N : ℕ} → Controller A O N → Adaptive.Protocol A O
  | 0, _ => .stop
  | n + 1, C => .node (C 0 Fin.elim0) (fun o => protocol (shift C o))

/-- An actual bijection, not a probability-only identification of records. -/
def leafEquiv : {N : ℕ} → (C : Controller A O N) → ClassicalQuantumMemory.ProtocolMemory.Leaf (protocol C) ≃ History O N
  | 0, _ => {
      toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := by intro l; cases l; rfl
      right_inv := by intro h; funext i; exact Fin.elim0 i }
  | n + 1, C => {
      toFun := fun l => Fin.cons (α := fun _ => O) l.1 (leafEquiv (shift C l.1) l.2)
      invFun := fun h => ⟨h 0, (leafEquiv (shift C (h 0))).symm (Fin.tail h)⟩
      left_inv := by
        rintro ⟨o, l⟩
        change (⟨o, (leafEquiv (shift C o)).symm (leafEquiv (shift C o) l)⟩ :
          ClassicalQuantumMemory.ProtocolMemory.Leaf (protocol C)) = ⟨o, l⟩
        rw [Equiv.symm_apply_apply]
      right_inv := by
        intro h
        simp [Fin.cons_self_tail] }

theorem protocol_word_eq (C : Controller A O N) (l : ClassicalQuantumMemory.ProtocolMemory.Leaf (protocol C)) :
    (protocol C).word l = word C (leafEquiv C l) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rcases l with ⟨o, l⟩
    change (C 0 Fin.elim0, o) :: (protocol (shift C o)).word l =
      word C (Fin.cons (α := fun _ => O) o (leafEquiv (shift C o) l))
    simp only [word, Fin.cons_zero, Fin.tail_cons, ih]

theorem snoc_head (h : History O (N + 1)) (o : O) :
    Fin.snoc (α := fun _ => O) h o 0 = h 0 := by
  exact Fin.snoc_castSucc (n := N + 1) (α := fun _ => O) o h 0

theorem tail_snoc (h : History O (N + 1)) (o : O) :
    Fin.tail (Fin.snoc (α := fun _ => O) h o) = Fin.snoc (α := fun _ => O) (Fin.tail h) o := by
  conv_lhs => rw [← Fin.cons_self_tail h, ← Fin.cons_snoc_eq_snoc_cons]
  simp

/-- Reading from the front and appending at the end have the same time order. -/
theorem word_snoc (C : Controller A O (N + 1)) (h : History O N) (o : O) :
    word C (Fin.snoc (α := fun _ => O) h o) = word (dropLast C) h ++ [(C (Fin.last N) h, o)] := by
  induction N with
  | zero =>
    have hh : h = Fin.elim0 := by funext i; exact Fin.elim0 i
    subst h
    simp [word, Fin.snoc_zero]
  | succ n ih =>
    change (C 0 Fin.elim0, Fin.snoc (α := fun _ => O) h o 0) ::
        word (shift C (Fin.snoc (α := fun _ => O) h o 0))
          (Fin.tail (Fin.snoc (α := fun _ => O) h o)) =
      ((dropLast C) 0 Fin.elim0, h 0) ::
        word (shift (dropLast C) (h 0)) (Fin.tail h) ++ [(C (Fin.last (n + 1)) h, o)]
    rw [snoc_head, tail_snoc, ih, List.cons_append, dropLast_shift]
    simp [dropLast, shift, Fin.cons_self_tail]


/-- Restrict the same action rule to an earlier, explicitly bounded time. -/
def truncate (C : Controller A O N) (n : ℕ) (hn : n ≤ N) : Controller A O n :=
  fun t h => C ⟨t.val, lt_of_lt_of_le t.isLt hn⟩ h

@[simp] theorem truncate_last (C : Controller A O (N + 1)) :
    C.truncate N (Nat.le_succ N) = C.dropLast := rfl

theorem truncate_dropLast (C : Controller A O (N + 1)) (t : Fin N) :
    C.dropLast.truncate t.val (Nat.le_of_lt t.isLt) =
      C.truncate t.castSucc.val (Nat.le_of_lt t.castSucc.isLt) := rfl

end Controller


/-- A zero-length history carries no extra information. -/
def initialEquiv (O ι : Type*) : ι ≃ (History O 0 × ι) where
  toFun i := (Fin.elim0, i)
  invFun p := p.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨h, i⟩
    apply Prod.ext
    · funext j
      exact Fin.elim0 j
    · rfl

/-- Appending one actual outcome is a bijection of the full output carrier. -/
def extendEquiv (O ι : Type*) (N : ℕ) :
    (History O N × (O × ι)) ≃ (History O (N + 1) × ι) where
  toFun p := (Fin.snoc (α := fun _ => O) p.1 p.2.1, p.2.2)
  invFun p := (Fin.init p.1, (p.1 (Fin.last N), p.2))
  left_inv := by
    rintro ⟨h, o, i⟩
    simp
  right_inv := by
    rintro ⟨h, i⟩
    simp [Fin.snoc_init_self]

section Dynamics

variable {A O ι κ η : Type*} [Fintype O] [DecidableEq O]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype η] {N : ℕ}

/-- Actual history dephasing, selected instrument, and chronological append. -/
def step (f : History O N → A) (I : A → Instrument ι O κ) :
    RectangularChannel (History O N × ι) (History O (N + 1) × ι)
      (Unit × (History O N × (O × κ))) :=
  (HistoryChannels.relabel (extendEquiv O ι N)).comp
    (HistoryChannels.controlled (fun h => ClassicalQuantumMemory.channel (I (f h))))


/-- The supremum includes zero; nonnegative bounds remain valid on empty carriers. -/
theorem step_defect_le_uniform (f : History O N → A)
    (I : A → Instrument ι O κ) (J : A → Instrument ι O η) (ε : ℝ)
    (hε0 : 0 ≤ ε)
    (hε : ∀ h, ClassicalQuantumMemory.defect (I (f h)) (J (f h)) ≤ ε) :
    (step f I).defect (step f J) ≤ ε := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩)
  · exact hε0
  · simp only [step, RectangularChannel.comp_state, HistoryChannels.relabel_state_distance]
    exact HistoryChannels.controlled_state_distance_le_uniform _ _ ρ ε hε

/-- Identical record instruments have zero actual tagged defect. -/
theorem record_defect_self (I : Instrument ι O κ) : ClassicalQuantumMemory.defect I I = 0 := by
  apply le_antisymm ?_ (RectangularChannel.defect_nonneg _ _)
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩) <;> simp

theorem step_state_distance_le_weighted (f : History O N → A)
    (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (ρ : Density (History O N × ι)) :
    effectDistance ((step f I).state ρ) ((step f J).state ρ) ≤
      ∑ h, HistoryChannels.weight ρ h * ClassicalQuantumMemory.defect (I (f h)) (J (f h)) := by
  simp only [step, RectangularChannel.comp_state, HistoryChannels.relabel_state_distance]
  exact HistoryChannels.controlled_state_distance_le_weighted_defect _ _ ρ

theorem step_state_distance_le_uniform (f : History O N → A)
    (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (ρ : Density (History O N × ι)) (ε : ℝ)
    (hε : ∀ h, ClassicalQuantumMemory.defect (I (f h)) (J (f h)) ≤ ε) :
    effectDistance ((step f I).state ρ) ((step f J).state ρ) ≤ ε := by
  simp only [step, RectangularChannel.comp_state, HistoryChannels.relabel_state_distance]
  exact HistoryChannels.controlled_state_distance_le_uniform _ _ ρ ε hε

/-- Every entry of the physical next state is the selected branch of one principal block. -/
theorem step_operator_apply (f : History O N → A) (I : A → Instrument ι O κ)
    (X : Operator (History O N × ι)) (h g : History O (N + 1)) (i j : ι) :
    (step f I).operator X (h, i) (g, j) = if h = g then
      (I (f (Fin.init h))).branch (h (Fin.last N))
        (HistoryChannels.principal X (Fin.init h)) i j else 0 := by
  simp only [step, RectangularChannel.comp_operator, HistoryChannels.relabel_operator_apply]
  change (HistoryChannels.controlled _).operator X
    (Fin.init h, (h (Fin.last N), i)) (Fin.init g, (g (Fin.last N), j)) = _
  rw [HistoryChannels.controlled_operator_apply]
  by_cases heq : Fin.init h = Fin.init g
  · rw [if_pos heq, ClassicalQuantumMemory.channel_operator_apply]
    by_cases hlast : h (Fin.last N) = g (Fin.last N)
    · have hfull : h = g := by
        rw [← Fin.snoc_init_self h, ← Fin.snoc_init_self g, heq, hlast]
      simp [hlast, hfull]
    · have hfull : h ≠ g := by intro h; subst g; exact hlast rfl
      simp [hlast, hfull]
  · have hfull : h ≠ g := by intro h; subst g; exact heq rfl
    simp [heq, hfull]

theorem step_operator_eq_block (f : History O N → A) (I : A → Instrument ι O κ)
    (X : Operator (History O N × ι)) :
    (step f I).operator X = ClassicalQuantumMemory.block (fun h =>
      (I (f (Fin.init h))).branch (h (Fin.last N))
        (HistoryChannels.principal X (Fin.init h))) := by
  ext ⟨h, i⟩ ⟨g, j⟩
  exact step_operator_apply f I X h g i j

/-- The actual finite sequence of channels; no infinite extension of the controller is used. -/
def run (I : A → Instrument ι O κ) : {N : ℕ} →
    Controller A O N → Density ι → Density (History O N × ι)
  | 0, _, ρ => (HistoryChannels.relabel (initialEquiv O ι)).state ρ
  | n + 1, C, ρ => (step (C (Fin.last n)) I).state (run I C.dropLast ρ)

/-- The original interpreter composes from the front in chronological order. -/
theorem recordOperator_append (I : A → Instrument ι O κ)
    (w v : List (A × O)) (X : Operator ι) :
    recordOperator I (w ++ v) X = recordOperator I v (recordOperator I w X) := by
  induction w generalizing X with
  | nil => rfl
  | cons e w ih => exact ih _

/-- The new trajectory retains exactly each old recordOperator block. -/
theorem run_matrix (I : A → Instrument ι O κ) (C : Controller A O N) (ρ : Density ι) :
    (run I C ρ).matrix = ClassicalQuantumMemory.block
      (fun h => recordOperator I (C.word h) ρ.matrix) := by
  induction N with
  | zero =>
    ext ⟨h, i⟩ ⟨g, j⟩
    have hg : h = g := by funext k; exact Fin.elim0 k
    simp [run, HistoryChannels.relabel_state_matrix, initialEquiv,
      ClassicalQuantumMemory.block, Controller.word, recordOperator, hg]
  | succ n ih =>
    change (step (C (Fin.last n)) I).operator (run I C.dropLast ρ).matrix = _
    rw [step_operator_eq_block]
    apply congrArg ClassicalQuantumMemory.block
    funext h
    have hx : HistoryChannels.principal (run I C.dropLast ρ).matrix (Fin.init h) =
        recordOperator I (C.dropLast.word (Fin.init h)) ρ.matrix := by
      rw [ih]
      ext i j
      simp [HistoryChannels.principal, ClassicalQuantumMemory.block]
    rw [hx]
    have hw := C.word_snoc (Fin.init h) (h (Fin.last n))
    rw [Fin.snoc_init_self] at hw
    rw [hw, recordOperator_append]
    rfl


/-- Full quantum-memory states agree with the original tree interpreter after an actual relabelling. -/
theorem run_eq_protocol_state (I : A → Instrument ι O κ)
    (C : Controller A O N) (ρ : Density ι) :
    run I C ρ =
      (HistoryChannels.relabel (C.leafEquiv.prodCongr (Equiv.refl ι))).state
        (ClassicalQuantumMemory.ProtocolMemory.state I C.protocol ρ) := by
  apply Density.ext
  ext ⟨h, i⟩ ⟨g, j⟩
  rw [run_matrix, HistoryChannels.relabel_state_matrix,
    ClassicalQuantumMemory.ProtocolMemory.state_matrix]
  simp [ClassicalQuantumMemory.block, Controller.protocol_word_eq, Equiv.prodCongr]

/-- The terminal quantum marginal is the same genuine old leaf-operator sum. -/
theorem terminal_memory_matrix (I : A → Instrument ι O κ)
    (C : Controller A O N) (ρ : Density ι) :
    ((RectangularChannel.discardLeft ι (History O N)).state (run I C ρ)).matrix =
      ∑ l : ClassicalQuantumMemory.ProtocolMemory.Leaf C.protocol, recordOperator I (C.protocol.word l) ρ.matrix := by
  ext i j
  change (RectangularChannel.discardLeft ι (History O N)).operator (run I C ρ).matrix i j = _
  rw [RectangularChannel.discardLeft_operator_apply, run_matrix]
  simp only [ClassicalQuantumMemory.block_apply_same, Matrix.sum_apply]
  rw [← Equiv.sum_comp C.leafEquiv]
  simp only [Controller.protocol_word_eq]

@[simp] theorem weight_run (I : A → Instrument ι O κ)
    (C : Controller A O N) (ρ : Density ι) (h : History O N) :
    HistoryChannels.weight (run I C ρ) h = response I ρ (C.word h) := by
  change mass (HistoryChannels.principal (run I C ρ).matrix h) = _
  rw [run_matrix]
  apply congrArg mass
  ext i j
  simp [HistoryChannels.principal, ClassicalQuantumMemory.block]

/-- Every original adaptive leaf has its actual recorded probability. -/
theorem weight_run_leaf (I : A → Instrument ι O κ)
    (C : Controller A O N) (ρ : Density ι) (l : ClassicalQuantumMemory.ProtocolMemory.Leaf C.protocol) :
    HistoryChannels.weight (run I C ρ) (C.leafEquiv l) =
      Adaptive.leafProbability I C.protocol ρ l := by
  rw [weight_run, Adaptive.leafProbability_eq_response, Controller.protocol_word_eq]

/-- The common input at each action is the actual J-prefix state, with its own normalized history weights. -/
def actionCost (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (C : Controller A O N) (σ : Density ι) (t : Fin N) : ℝ :=
  ∑ h, HistoryChannels.weight (run J (C.truncate t.val (Nat.le_of_lt t.isLt)) σ) h *
    ClassicalQuantumMemory.defect (I (C t h)) (J (C t h))

theorem actionCost_nonneg (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (C : Controller A O N) (σ : Density ι) (t : Fin N) : 0 ≤ actionCost I J C σ t := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (HistoryChannels.weight_nonneg _ h)
    (RectangularChannel.defect_nonneg _ _)

@[simp] theorem actionCost_castSucc (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (C : Controller A O (N + 1)) (σ : Density ι) (t : Fin N) :
    actionCost I J C σ t.castSucc = actionCost I J C.dropLast σ t := rfl

@[simp] theorem actionCost_last (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (C : Controller A O (N + 1)) (σ : Density ι) :
    actionCost I J C σ (Fin.last N) =
      ∑ h, HistoryChannels.weight (run J C.dropLast σ) h *
        ClassicalQuantumMemory.defect (I (C (Fin.last N) h)) (J (C (Fin.last N) h)) := rfl

/-- A genuine step recurrence: first propagate the input error, then compare actions on one shared input. -/
theorem run_succ_distance_le (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (C : Controller A O (N + 1)) (ρ σ : Density ι) :
    effectDistance (run I C ρ) (run J C σ) ≤
      effectDistance (run I C.dropLast ρ) (run J C.dropLast σ) +
        actionCost I J C σ (Fin.last N) := by
  change effectDistance ((step (C (Fin.last N)) I).state (run I C.dropLast ρ))
    ((step (C (Fin.last N)) J).state (run J C.dropLast σ)) ≤ _
  exact (effectDistance_triangle _
    ((step (C (Fin.last N)) I).state (run J C.dropLast σ)) _).trans
      (add_le_add ((step (C (Fin.last N)) I).state_effectDistance_le _ _)
        (step_state_distance_le_weighted _ I J _))

/-- The proved sum uses actual per-time, per-history action defects, plus any initial-state error. -/
theorem run_distance_le_actionCost_sum (I : A → Instrument ι O κ)
    (J : A → Instrument ι O η) (C : Controller A O N) (ρ σ : Density ι) :
    effectDistance (run I C ρ) (run J C σ) ≤
      effectDistance ρ σ + ∑ t : Fin N, actionCost I J C σ t := by
  induction N with
  | zero => simp [run, HistoryChannels.relabel_state_distance]
  | succ n ih =>
    calc
      effectDistance (run I C ρ) (run J C σ) ≤
          effectDistance (run I C.dropLast ρ) (run J C.dropLast σ) +
            actionCost I J C σ (Fin.last n) := run_succ_distance_le I J C ρ σ
      _ ≤ (effectDistance ρ σ + ∑ t : Fin n, actionCost I J C.dropLast σ t) +
          actionCost I J C σ (Fin.last n) := add_le_add (ih C.dropLast) (le_refl _)
      _ = effectDistance ρ σ + ∑ t : Fin (n + 1), actionCost I J C σ t := by
        rw [Fin.sum_univ_castSucc]
        simp only [actionCost_castSucc, add_assoc]

/-- A verified action bound is averaged using one normalized prefix law. -/
theorem actionCost_le (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (C : Controller A O N) (σ : Density ι) (t : Fin N) (ε : ℝ)
    (hε : ∀ h, ClassicalQuantumMemory.defect (I (C t h)) (J (C t h)) ≤ ε) :
    actionCost I J C σ t ≤ ε := by
  calc
    actionCost I J C σ t ≤
        ∑ h, HistoryChannels.weight (run J (C.truncate t.val (Nat.le_of_lt t.isLt)) σ) h * ε :=
      Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (hε h)
        (HistoryChannels.weight_nonneg _ h))
    _ = ε := by rw [← Finset.sum_mul, HistoryChannels.sum_weight, one_mul]

/-- Fixed finite depth and the same causal controller are explicit in the statement. -/
theorem run_distance_le_budget_sum (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (C : Controller A O N) (ρ σ : Density ι) (ε : Fin N → ℝ)
    (hε : ∀ t h, ClassicalQuantumMemory.defect (I (C t h)) (J (C t h)) ≤ ε t) :
    effectDistance (run I C ρ) (run J C σ) ≤ effectDistance ρ σ + ∑ t, ε t :=
  (run_distance_le_actionCost_sum I J C ρ σ).trans
    (add_le_add (le_refl _) (Finset.sum_le_sum (fun t _ => actionCost_le I J C σ t (ε t) (hε t))))

/-- The record TV is controlled by the same actual per-action sum. -/
theorem record_tv_le_actionCost_sum (I : A → Instrument ι O κ)
    (J : A → Instrument ι O η) (C : Controller A O N) (ρ σ : Density ι) :
    Mixture.tv (HistoryChannels.weights (run I C ρ)) (HistoryChannels.weights (run J C σ)) ≤
      effectDistance ρ σ + ∑ t : Fin N, actionCost I J C σ t :=
  (HistoryChannels.record_tv_le_joint_distance _ _).trans
    (run_distance_le_actionCost_sum I J C ρ σ)

theorem record_tv_le_budget_sum (I : A → Instrument ι O κ)
    (J : A → Instrument ι O η) (C : Controller A O N) (ρ σ : Density ι)
    (ε : Fin N → ℝ)
    (hε : ∀ t h, ClassicalQuantumMemory.defect (I (C t h)) (J (C t h)) ≤ ε t) :
    Mixture.tv (HistoryChannels.weights (run I C ρ)) (HistoryChannels.weights (run J C σ)) ≤
      effectDistance ρ σ + ∑ t, ε t :=
  (HistoryChannels.record_tv_le_joint_distance _ _).trans
    (run_distance_le_budget_sum I J C ρ σ ε hε)

/-- Relabelled full histories and the old adaptive leaves have exactly the same TV. -/
theorem protocol_record_tv_eq (I : A → Instrument ι O κ) (J : A → Instrument ι O η)
    (C : Controller A O N) (ρ σ : Density ι) :
    Mixture.tv (ClassicalQuantumMemory.ProtocolMemory.weights I C.protocol ρ)
      (ClassicalQuantumMemory.ProtocolMemory.weights J C.protocol σ) =
      Mixture.tv (HistoryChannels.weights (run I C ρ)) (HistoryChannels.weights (run J C σ)) := by
  simp only [Mixture.tv, ClassicalQuantumMemory.ProtocolMemory.weights_weight,
    HistoryChannels.weights_weight]
  rw [← Equiv.sum_comp C.leafEquiv]
  simp only [weight_run_leaf]

/-- The original Protocol's full leaf law inherits the derived action-level budget. -/
theorem protocol_record_tv_le_budget_sum (I : A → Instrument ι O κ)
    (J : A → Instrument ι O η) (C : Controller A O N) (ρ σ : Density ι)
    (ε : Fin N → ℝ)
    (hε : ∀ t h, ClassicalQuantumMemory.defect (I (C t h)) (J (C t h)) ≤ ε t) :
    Mixture.tv (ClassicalQuantumMemory.ProtocolMemory.weights I C.protocol ρ)
      (ClassicalQuantumMemory.ProtocolMemory.weights J C.protocol σ) ≤
        effectDistance ρ σ + ∑ t, ε t := by
  rw [protocol_record_tv_eq]
  exact record_tv_le_budget_sum I J C ρ σ ε hε

end Dynamics

end

end UEOTQM.ActionRecordBudget
