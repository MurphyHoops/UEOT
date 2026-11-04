import Mathlib

/-!
# Exact finite joint-decision solver and its returned table

The state `I` is a permitted information state, not a world record.  It may be
the entire allowed history, including the observed wallet, so it need not be
finite.  A source consumer must derive `prob`, `reward` and `next` from its SAME
joint source.  `reward i a o` is the conditional expected actual reward given
`o`; it is not an independently sampled reward kernel.  Impossible observations
may have arbitrary continuations because their mass is zero.

`actions` is the executable finite list after the pre-execution affordability
test.  This module does not manufacture that test or grant a sensor.  The
returned `Table` is an explicitly new finite outer scheduler; it is not the old
memoryless Register instruction.  All selection uses computable rational
comparisons.  The comparison class includes arbitrary-history randomized
policies with real, not merely rational, action probabilities.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolver

open scoped BigOperators

universe uI uA uO uM

structure Model (I : Type uI) (A : Type uA) (O : Type uO) [Fintype O] where
  actions : I → List A
  actions_nonempty : ∀ i, actions i ≠ []
  prob : I → A → O → ℚ
  reward : I → A → O → ℚ
  next : I → A → O → I
  prob_nonneg : ∀ i a, a ∈ actions i → ∀ o, 0 ≤ prob i a o
  prob_sum_one : ∀ i a, a ∈ actions i → ∑ o, prob i a o = 1
  discount : ℚ
  discount_nonneg : 0 ≤ discount

/-- A finite, observation-indexed outer decision table.  The chosen action is
stored at the node, and the next row uses only the permitted observation. -/
inductive Table (A : Type uA) (O : Type uO) : ℕ → Type (max uA uO)
  | halt : Table A O 0
  | node {n : ℕ} (action : A) (children : O → Table A O n) : Table A O (n + 1)

variable {I : Type uI} {A : Type uA} {O : Type uO} [Fintype O]

/-- Concrete rational comparison, with the earlier action winning ties. -/
def selectBest (score : A → ℚ) (a : A) : List A → A
  | [] => a
  | b :: bs =>
      let c := selectBest score b bs
      if score a < score c then c else a

theorem selectBest_mem (score : A → ℚ) :
    ∀ (xs : List A) (a : A), selectBest score a xs ∈ a :: xs := by
  intro xs
  induction xs with
  | nil => intro a; simp [selectBest]
  | cons b bs ih =>
      intro a
      dsimp only [selectBest]
      split
      · exact List.mem_cons_of_mem a (ih b)
      · exact List.mem_cons_self

theorem le_selectBest_left (score : A → ℚ) (a : A) (xs : List A) :
    score a ≤ score (selectBest score a xs) := by
  cases xs with
  | nil => exact le_rfl
  | cons b bs =>
      dsimp only [selectBest]
      split
      · exact le_of_lt ‹_›
      · exact le_rfl

theorem le_selectBest_mem (score : A → ℚ) :
    ∀ (xs : List A) (a b : A), b ∈ xs → score b ≤ score (selectBest score a xs) := by
  intro xs
  induction xs with
  | nil => intro a b hb; cases hb
  | cons c cs ih =>
      intro a b hb
      have hc : score (selectBest score c cs) ≤ score (selectBest score a (c :: cs)) := by
        dsimp only [selectBest]
        split
        · exact le_rfl
        · exact le_of_not_gt ‹_›
      rcases List.mem_cons.mp hb with hbc | hbs
      · subst b
        exact (le_selectBest_left score c cs).trans hc
      · exact (ih c b hbs).trans hc

/-- An executable maximum selector for an explicit nonempty list. -/
def chooseBest (score : A → ℚ) (xs : List A) (hne : xs ≠ []) : A :=
  match xs, hne with
  | [], h => False.elim (h rfl)
  | a :: as, _ => selectBest score a as

theorem chooseBest_mem (score : A → ℚ) (xs : List A) (hne : xs ≠ []) :
    chooseBest score xs hne ∈ xs := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a as => exact selectBest_mem score as a

theorem le_chooseBest (score : A → ℚ) (xs : List A) (hne : xs ≠ [])
    (a : A) (ha : a ∈ xs) :
    score a ≤ score (chooseBest score xs hne) := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons b bs =>
      rcases List.mem_cons.mp ha with hab | hbs
      · subst a
        exact le_selectBest_left score b bs
      · exact le_selectBest_mem score bs b a hbs

/-- The finite table interpreter's exact value, with terminal payoff zero. -/
def value (M : Model I A O) : {n : ℕ} → I → Table A O n → ℚ
  | _, _, .halt => 0
  | _, i, .node a children =>
      ∑ o, M.prob i a o * (M.reward i a o + M.discount * value M (M.next i a o) (children o))

/-- Membership of every row, including zero-probability off-path rows. -/
def Feasible (M : Model I A O) : {n : ℕ} → I → Table A O n → Prop
  | _, _, .halt => True
  | _, i, .node a children =>
      a ∈ M.actions i ∧ ∀ o, Feasible M (M.next i a o) (children o)

def qValue (M : Model I A O) (v : I → ℚ) (i : I) (a : A) : ℚ :=
  ∑ o, M.prob i a o * (M.reward i a o + M.discount * v (M.next i a o))

/-- This function returns the actual table, not only a symbolic optimum. -/
def solve (M : Model I A O) : (n : ℕ) → I → Table A O n
  | 0, _ => .halt
  | n + 1, i =>
      let children := fun a o => solve M n (M.next i a o)
      let score := fun a =>
        ∑ o, M.prob i a o *
          (M.reward i a o + M.discount * value M (M.next i a o) (children a o))
      let a := chooseBest score (M.actions i) (M.actions_nonempty i)
      .node a (children a)

def optimalValue (M : Model I A O) (n : ℕ) (i : I) : ℚ :=
  value M i (solve M n i)

def chosenAction (M : Model I A O) (n : ℕ) (i : I) : A :=
  chooseBest (qValue M (optimalValue M n) i) (M.actions i) (M.actions_nonempty i)

@[simp] theorem solve_zero (M : Model I A O) (i : I) : solve M 0 i = .halt := rfl

theorem solve_succ (M : Model I A O) (n : ℕ) (i : I) :
    solve M (n + 1) i = .node (chosenAction M n i)
      (fun o => solve M n (M.next i (chosenAction M n i) o)) := rfl

@[simp] theorem optimalValue_zero (M : Model I A O) (i : I) :
    optimalValue M 0 i = 0 := rfl

theorem optimalValue_succ (M : Model I A O) (n : ℕ) (i : I) :
    optimalValue M (n + 1) i = qValue M (optimalValue M n) i (chosenAction M n i) := rfl

theorem chosenAction_mem (M : Model I A O) (n : ℕ) (i : I) :
    chosenAction M n i ∈ M.actions i :=
  chooseBest_mem _ _ _

theorem qValue_le_optimalValue (M : Model I A O) (n : ℕ) (i : I) (a : A)
    (ha : a ∈ M.actions i) :
    qValue M (optimalValue M n) i a ≤ optimalValue M (n + 1) i :=
  le_chooseBest _ _ _ a ha

theorem solve_feasible (M : Model I A O) :
    ∀ (n : ℕ) (i : I), Feasible M i (solve M n i) := by
  intro n
  induction n with
  | zero => intro i; trivial
  | succ n ih =>
      intro i
      rw [solve_succ]
      exact ⟨chosenAction_mem M n i, fun o => ih _⟩

/-- Every other permitted deterministic table is dominated by THIS returned
table, at every finite horizon and every permitted information state. -/
theorem value_le_solve (M : Model I A O) :
    ∀ (n : ℕ) (i : I) (p : Table A O n), Feasible M i p → value M i p ≤ optimalValue M n i := by
  intro n
  induction n with
  | zero => intro i p hp; cases p; exact le_rfl
  | succ n ih =>
      intro i p hp
      cases p with
      | node a children =>
          obtain ⟨ha, hchildren⟩ := hp
          calc
            value M i (.node a children) ≤ qValue M (optimalValue M n) i a := by
              apply Finset.sum_le_sum
              intro o ho
              apply mul_le_mul_of_nonneg_left _ (M.prob_nonneg i a ha o)
              apply add_le_add le_rfl
              exact mul_le_mul_of_nonneg_left (ih _ _ (hchildren o)) M.discount_nonneg
            _ ≤ optimalValue M (n + 1) i := qValue_le_optimalValue M n i a ha

/-- Arbitrary causal memory and real randomized action probabilities.
`Memory` can be the complete permitted history; the consumer must not put
unobserved world information in it.  The transition remains the SAME model
conditional on this allowed memory. -/
structure CausalPolicy (M : Model I A O) [Fintype A] where
  Memory : Type uM
  info : Memory → I
  advance : Memory → A → O → Memory
  info_advance : ∀ h a o, info (advance h a o) = M.next (info h) a o
  actionProb : Memory → A → ℝ
  actionProb_nonneg : ∀ h a, 0 ≤ actionProb h a
  actionProb_sum_one : ∀ h, ∑ a, actionProb h a = 1
  actionProb_supported : ∀ h a, actionProb h a ≠ 0 → a ∈ M.actions (info h)

noncomputable def causalValue (M : Model I A O) [Fintype A] (pi : CausalPolicy M) :
    ℕ → pi.Memory → ℝ
  | 0, _ => 0
  | n + 1, h =>
      ∑ a, pi.actionProb h a * ∑ o, (M.prob (pi.info h) a o : ℝ) *
        ((M.reward (pi.info h) a o : ℝ) + (M.discount : ℝ) * causalValue M pi n (pi.advance h a o))

/-- The exact returned rational table dominates ALL same-information causal
randomized policies, including full-history policies with real weights. -/
theorem causalValue_le_solve (M : Model I A O) [Fintype A] (pi : CausalPolicy M) :
    ∀ (n : ℕ) (h : pi.Memory), causalValue M pi n h ≤ (optimalValue M n (pi.info h) : ℝ) := by
  intro n
  induction n with
  | zero => intro h; simp [causalValue]
  | succ n ih =>
      intro h
      have haction (a : A) (ha : a ∈ M.actions (pi.info h)) :
          (∑ o, (M.prob (pi.info h) a o : ℝ) *
            ((M.reward (pi.info h) a o : ℝ) +
              (M.discount : ℝ) * causalValue M pi n (pi.advance h a o))) ≤
            (optimalValue M (n + 1) (pi.info h) : ℝ) := by
        calc
          _ ≤ ∑ o, (M.prob (pi.info h) a o : ℝ) *
              ((M.reward (pi.info h) a o : ℝ) +
                (M.discount : ℝ) * (optimalValue M n (M.next (pi.info h) a o) : ℝ)) := by
            apply Finset.sum_le_sum
            intro o ho
            apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast M.prob_nonneg _ _ ha o)
            apply add_le_add le_rfl
            apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast M.discount_nonneg)
            simpa only [pi.info_advance] using ih (pi.advance h a o)
          _ = (qValue M (optimalValue M n) (pi.info h) a : ℝ) := by
            simp only [qValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_add]
          _ ≤ (optimalValue M (n + 1) (pi.info h) : ℝ) := by
            exact_mod_cast qValue_le_optimalValue M n (pi.info h) a ha
      calc
        causalValue M pi (n + 1) h ≤
            ∑ a, pi.actionProb h a * (optimalValue M (n + 1) (pi.info h) : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases hz : pi.actionProb h a = 0
          · simp [hz]
          · exact mul_le_mul_of_nonneg_left
              (haction a (pi.actionProb_supported h a hz)) (pi.actionProb_nonneg h a)
        _ = (optimalValue M (n + 1) (pi.info h) : ℝ) := by
          rw [← Finset.sum_mul, pi.actionProb_sum_one, one_mul]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolver
