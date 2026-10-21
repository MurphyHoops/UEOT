import UEOTQM.ActionRecordBudget
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Absorbing completion of actual finite stopping trees

The original adaptive tree determines both the actions and the stopping rule.
An additional `none` outcome records idle time after stopping. The only idle
Kraus operator is the identity. Active actions and all original leaf operators
are retained; malformed completed records have zero operator blocks.
-/

namespace UEOTQM.StoppingProtocols

open Matrix ActionRecordBudget
open scoped BigOperators ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

section Tree

variable {A O : Type*}

abbrev Leaf (π : Adaptive.Protocol A O) := ClassicalQuantumMemory.ProtocolMemory.Leaf π

/-- The actual finite maximum over all continuations, including zero-probability ones. -/
def height [Fintype O] : Adaptive.Protocol A O → ℕ
  | .stop => 0
  | .node _ next => Finset.univ.sup (fun o => height (next o)) + 1

theorem height_next_le [Fintype O] (a : A) (next : O → Adaptive.Protocol A O)
    (o : O) : height (next o) + 1 ≤ height (.node a next) := by
  exact Nat.add_le_add_right (Finset.le_sup (f := fun o => height (next o)) (Finset.mem_univ o)) 1

/-- `none` means that the original tree has already stopped. -/
def action : Adaptive.Protocol A O → Option A
  | .stop => none
  | .node a _ => some a

/-- A total residual tree; impossible records also receive a defined continuation. -/
def advance : Adaptive.Protocol A O → Option O → Adaptive.Protocol A O
  | .node _ next, some o => next o
  | _, _ => .stop

def follow : Adaptive.Protocol A O → List (Option O) → Adaptive.Protocol A O
  | π, [] => π
  | π, o :: h => follow (advance π o) h

/-- The common original tree is read only through the past outcomes. -/
def controller (π : Adaptive.Protocol A O) (N : ℕ) :
    Controller (Option A) (Option O) N :=
  fun t h => action (follow π (List.ofFn h))

@[simp] theorem controller_truncate (π : Adaptive.Protocol A O) (N n : ℕ) (hn : n ≤ N) :
    (controller π N).truncate n hn = controller π n := rfl

@[simp] theorem controller_dropLast (π : Adaptive.Protocol A O) (N : ℕ) :
    (controller π (N + 1)).dropLast = controller π N := rfl

@[simp] theorem controller_zero (π : Adaptive.Protocol A O) (N : ℕ) :
    controller π (N + 1) 0 Fin.elim0 = action π := by
  simp [controller, follow]

@[simp] theorem controller_shift (π : Adaptive.Protocol A O) (N : ℕ) (o : Option O) :
    (controller π (N + 1)).shift o = controller (advance π o) N := by
  funext t h
  simp [Controller.shift, controller, List.ofFn_cons, follow]

theorem controller_word_succ (π : Adaptive.Protocol A O) (N : ℕ)
    (h : History (Option O) (N + 1)) :
    (controller π (N + 1)).word h =
      (action π, h 0) :: (controller (advance π (h 0)) N).word (Fin.tail h) := by
  simp only [Controller.word, controller_zero, controller_shift]

/-- Original leaves are padded with a distinct idle symbol, never truncated in the theorem below. -/
def encode : (π : Adaptive.Protocol A O) → Leaf π →
    {N : ℕ} → History (Option O) N
  | .stop, _, _, _ => none
  | .node _ _, _, 0, h => Fin.elim0 h
  | .node _ next, l, n + 1, h =>
      Fin.cons (α := fun _ => Option O) (some l.1) (encode (next l.1) l.2 (N := n)) h

/-- Decoding requires a complete original leaf followed only by idle symbols. -/
def decode : (π : Adaptive.Protocol A O) → {N : ℕ} →
    History (Option O) N → Option (Leaf π)
  | .stop, 0, _ => some PUnit.unit
  | .stop, n + 1, h => if h 0 = none then decode .stop (Fin.tail h) else none
  | .node _ _, 0, _ => none
  | .node _ next, n + 1, h =>
      (h 0).bind (fun o => (decode (next o) (Fin.tail h)).map (fun l => ⟨o, l⟩))

/-- Every original leaf fits at any depth at least the actual maximum tree depth. -/
theorem decode_encode [Fintype O] (π : Adaptive.Protocol A O) (l : Leaf π)
    (N : ℕ) (hN : height π ≤ N) :
    decode π (encode π l (N := N)) = some l := by
  induction N generalizing π with
  | zero =>
    cases π with
    | stop => cases l; rfl
    | node a next => simp [height] at hN
  | succ n ih =>
    cases π with
    | stop =>
      cases l
      change (if (none : Option O) = none then
        decode (.stop : Adaptive.Protocol A O) (Fin.tail (fun _ : Fin (n + 1) => none))
        else none) = some PUnit.unit
      rw [if_pos rfl]
      have ht : Fin.tail (fun _ : Fin (n + 1) => (none : Option O)) =
          (fun _ : Fin n => none) := by funext j; rfl
      rw [ht]
      exact ih .stop PUnit.unit (by simp [height])
    | node a next =>
      rcases l with ⟨o, l⟩
      have hn : height (next o) ≤ n := by
        have hh := height_next_le a next o
        omega
      change (decode (next o) (encode (next o) l (N := n))).map
        (fun l => (⟨o, l⟩ : Leaf (.node a next))) = some ⟨o, l⟩
      rw [ih (next o) l hn]
      rfl

/-- A successful decoder has exactly one padded input record. -/
theorem encode_of_decode (π : Adaptive.Protocol A O) {N : ℕ}
    (h : History (Option O) N) (l : Leaf π) (hd : decode π h = some l) :
    encode π l (N := N) = h := by
  induction N generalizing π with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    cases π with
    | stop =>
      cases l
      simp only [decode] at hd
      split_ifs at hd with hh
      · have ht := ih .stop (Fin.tail h) PUnit.unit hd
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [encode] using hh.symm
        · simpa [encode, Fin.tail] using congrFun ht j
    | node a next =>
      simp only [decode, Option.bind_eq_some_iff] at hd
      obtain ⟨o, ho, hm⟩ := hd
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hm
      have ht := ih (next o) (Fin.tail h) k hk
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [encode] using ho.symm
      · simpa [encode, Fin.tail] using congrFun ht j

theorem encode_injective [Fintype O] (π : Adaptive.Protocol A O) (N : ℕ)
    (hN : height π ≤ N) : Function.Injective (encode π (N := N)) := by
  intro l m h
  have hh := congrArg (decode π) h
  simpa only [decode_encode π _ N hN, Option.some.injEq] using hh

/-- Legal completed histories are exactly the image of the original leaf type. -/
theorem decode_eq_some_iff [Fintype O] (π : Adaptive.Protocol A O) {N : ℕ}
    (hN : height π ≤ N) (h : History (Option O) N) (l : Leaf π) :
    decode π h = some l ↔ h = encode π l := by
  constructor
  · exact fun hd => (encode_of_decode π h l hd).symm
  · intro he
    subst h
    exact decode_encode π l N hN

theorem word_length_le_height [Fintype O] (π : Adaptive.Protocol A O) (l : Leaf π) :
    (π.word l).length ≤ height π := by
  induction π with
  | stop => simp [Adaptive.Protocol.word, height]
  | node a next ih =>
    rcases l with ⟨o, l⟩
    have h := (Nat.add_le_add_right (ih o l) 1).trans (height_next_le a next o)
    simpa [Adaptive.Protocol.word] using h

/-- The stopping time is the length of the original word, not the padded horizon. -/
def stopTime (π : Adaptive.Protocol A O) (l : Leaf π) : ℕ := (π.word l).length

theorem stopTime_le [Fintype O] (π : Adaptive.Protocol A O) (l : Leaf π)
    {N : ℕ} (hN : height π ≤ N) : stopTime π l ≤ N :=
  (word_length_le_height π l).trans hN

/-- The complete padded record explicitly contains the original outcomes and the idle suffix. -/
theorem encode_record [Fintype O] (π : Adaptive.Protocol A O) (l : Leaf π)
    (N : ℕ) (hN : height π ≤ N) :
    List.ofFn (encode π l (N := N)) =
      (π.word l).map (fun e => some e.2) ++ List.replicate (N - stopTime π l) none := by
  induction N generalizing π with
  | zero =>
    cases π with
    | stop => simp [encode, Adaptive.Protocol.word, stopTime]
    | node a next => simp [height] at hN
  | succ n ih =>
    cases π with
    | stop => simp [encode, Adaptive.Protocol.word, stopTime, List.ofFn_const, List.replicate_succ]
    | node a next =>
      rcases l with ⟨o, l⟩
      have hn : height (next o) ≤ n := by
        have hh := height_next_le a next o
        omega
      simpa [encode, List.ofFn_cons, Adaptive.Protocol.word, stopTime] using
        congrArg (List.cons (some o)) (ih (next o) l hn)

end Tree

section Instruments

variable {A O ι κ : Type*} [Fintype O] [DecidableEq O]
  [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Active quantum matrices are extended by zero; idle is an actual identity branch. -/
def liftKraus (I : A → Instrument ι O κ) :
    Option A → Option O → Option κ → Operator ι
  | some a, some o, some k => (I a).kraus o k
  | none, none, none => 1
  | _, _, _ => 0

def lift (I : A → Instrument ι O κ) (a : Option A) :
    Instrument ι (Option O) (Option κ) where
  kraus := liftKraus I a
  complete := by
    cases a with
    | none => simp [liftKraus, Fintype.sum_option]
    | some a => simpa [liftKraus, Fintype.sum_option] using (I a).complete

@[simp] theorem lift_branch_active (I : A → Instrument ι O κ) (a : A) (o : O)
    (X : Operator ι) : (lift I (some a)).branch (some o) X = (I a).branch o X := by
  simp [Instrument.branch, krausMap, lift, liftKraus, Fintype.sum_option]

@[simp] theorem lift_branch_active_none (I : A → Instrument ι O κ) (a : A)
    (X : Operator ι) : (lift I (some a)).branch none X = 0 := by
  simp [Instrument.branch, krausMap, lift, liftKraus, Fintype.sum_option]

@[simp] theorem lift_branch_idle (I : A → Instrument ι O κ) (X : Operator ι) :
    (lift I none).branch none X = X := by
  simp [Instrument.branch, krausMap, lift, liftKraus, Fintype.sum_option]

@[simp] theorem lift_branch_idle_some (I : A → Instrument ι O κ) (o : O)
    (X : Operator ι) : (lift I none).branch (some o) X = 0 := by
  simp [Instrument.branch, krausMap, lift, liftKraus, Fintype.sum_option]

theorem record_zero (I : A → Instrument ι O κ) (w : List (A × O)) :
    recordOperator I w 0 = 0 := by
  have h := recordOperator_smul I w (0 : ℝ) (0 : Operator ι)
  simpa using h

/-- Completed histories retain the old leaf operator on every complex input;
histories with an early idle or an outcome after stopping have zero blocks. -/
theorem record_eq_decode (I : A → Instrument ι O κ) (π : Adaptive.Protocol A O)
    {N : ℕ} (hN : height π ≤ N) (h : History (Option O) N) (X : Operator ι) :
    recordOperator (lift I) ((controller π N).word h) X =
      (decode π h).elim 0 (fun l => recordOperator I (π.word l) X) := by
  induction N generalizing π X with
  | zero =>
    cases π with
    | stop => rfl
    | node a next => simp [height] at hN
  | succ n ih =>
    rw [controller_word_succ]
    cases π with
    | stop =>
      cases ho : h 0 with
      | none =>
        simpa [action, recordOperator, advance, decode, ho, lift_branch_idle] using
          ih .stop (by simp [height]) (Fin.tail h) X
      | some o =>
        simp [action, recordOperator, advance, decode, ho, record_zero]
    | node a next =>
      cases ho : h 0 with
      | none => simp [action, recordOperator, advance, decode, ho, record_zero]
      | some o =>
        have hn : height (next o) ≤ n := by
          have hh := height_next_le a next o
          omega
        have hi := ih (next o) hn (Fin.tail h) ((I a).branch o X)
        cases hd : decode (next o) (Fin.tail h) with
        | none =>
          simpa [action, recordOperator, advance, decode, ho, Adaptive.Protocol.word, hd,
            Option.map, Option.elim] using hi
        | some l =>
          simpa [action, recordOperator, advance, decode, ho, Adaptive.Protocol.word, hd,
            Option.map, Option.elim] using hi

theorem record_encode (I : A → Instrument ι O κ) (π : Adaptive.Protocol A O)
    {N : ℕ} (hN : height π ≤ N) (l : Leaf π) (X : Operator ι) :
    recordOperator (lift I) ((controller π N).word (encode π l)) X =
      recordOperator I (π.word l) X := by
  rw [record_eq_decode I π hN, decode_encode π l N hN]
  rfl

/-- Full joint memory matrices, not merely their traces, obey the stopping decoder. -/
theorem run_matrix (I : A → Instrument ι O κ) (π : Adaptive.Protocol A O)
    {N : ℕ} (hN : height π ≤ N) (ρ : Density ι) :
    (ActionRecordBudget.run (lift I) (controller π N) ρ).matrix =
      ClassicalQuantumMemory.block (fun h =>
        (decode π h).elim 0 (fun l => recordOperator I (π.word l) ρ.matrix)) := by
  rw [ActionRecordBudget.run_matrix]
  congr 1
  funext h
  exact record_eq_decode I π hN h ρ.matrix

end Instruments

end

end UEOTQM.StoppingProtocols
