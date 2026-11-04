import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolver

/-!
# Strict finite caching of the original exact solver

This is an implementation acceleration, not another optimizing policy.  A
strict finite list materializes each observation child once and each action
score once.  The original order and strict comparison resolve ties exactly as
in `solve`.  The final theorem identifies both the value and the returned table
with the original functions, including every impossible observation row.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFastSolver

open scoped BigOperators
open FiniteJointDecisionSolver

universe uI uA uO uX

variable {O : Type uO} {X : Type uX} [DecidableEq O]

/-- Total lookup into a materialized association list; the membership proof
is erased and does not require a default payload to be evaluated. -/
def lookupCached : (rows : List (O × X)) → (o : O) → o ∈ rows.map Prod.fst → X
  | [], _, h => False.elim (by simpa using h)
  | (p, x) :: rows, o, h =>
      if ho : o = p then x
      else lookupCached rows o (by
        simp only [List.map_cons, List.mem_cons] at h
        exact h.resolve_left ho)

theorem lookupCached_map (f : O → X) :
    ∀ (os : List O) (o : O) (h : o ∈ (os.map (fun p => (p, f p))).map Prod.fst),
      lookupCached (os.map (fun p => (p, f p))) o h = f o := by
  intro os
  induction os with
  | nil => intro o h; simp at h
  | cons p ps ih =>
      intro o h
      simp only [List.map_cons, lookupCached]
      split
      · next heq => simpa only [heq]
      · exact ih o _

/-- `noinline` keeps the list outside the returned lookup closure in generated
code.  The function is extensionally identical to its argument. -/
@[noinline] def cache (os : List O) (complete : ∀ o, o ∈ os) (f : O → X) : O → X :=
  let rows := os.map (fun o => (o, f o))
  fun o => lookupCached rows o (by
    simpa [rows, List.map_map, Function.comp_def] using complete o)

@[simp] theorem cache_apply (os : List O) (complete : ∀ o, o ∈ os)
    (f : O → X) (o : O) : cache os complete f o = f o := by
  unfold cache
  exact lookupCached_map f _ o _

variable {A : Type uA}

/-- All scores are already evaluated before this comparison traversal. -/
def selectScored (x : ℚ × X) : List (ℚ × X) → ℚ × X
  | [] => x
  | y :: ys =>
      let best := selectScored y ys
      if x.1 < best.1 then best else x

theorem selectScored_map (f : A → ℚ × X) :
    ∀ (xs : List A) (a : A),
      selectScored (f a) (xs.map f) = f (selectBest (fun b => (f b).1) a xs) := by
  intro xs
  induction xs with
  | nil => intro a; rfl
  | cons b bs ih =>
      intro a
      simp only [List.map_cons, selectScored, selectBest, ih]
      split <;> rfl

/-- Materialize the action list once; preserve the original first-tie rule. -/
@[noinline] def chooseScored (f : A → ℚ × X) (xs : List A) (hne : xs ≠ []) : ℚ × X :=
  let rows := xs.map f
  match rows, (show rows ≠ [] by simpa [rows] using hne) with
  | [], h => False.elim (h rfl)
  | x :: rest, _ => selectScored x rest

theorem chooseScored_eq (f : A → ℚ × X) (xs : List A) (hne : xs ≠ []) :
    chooseScored f xs hne = f (chooseBest (fun a => (f a).1) xs hne) := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a as => exact selectScored_map f as a

variable {I : Type uI} [Fintype O]

/-- Cache a value/table pair for each observation, then retain the exact score
and those very same child tables in the candidate payload. -/
def actionData (M : Model I A O) (os : List O) (complete : ∀ o, o ∈ os) :
    (n : ℕ) → (I → ℚ × Table A O n) →
    I → A → ℚ × (A × (O → Table A O n))
  | 0, _, i, a =>
      (∑ o, M.prob i a o * M.reward i a o, (a, fun _ => .halt))
  | n + 1, rec, i, a =>
      let children := cache os complete (fun o => rec (M.next i a o))
      (∑ o, M.prob i a o * (M.reward i a o + M.discount * (children o).1),
        (a, fun o => (children o).2))

theorem actionData_spec (M : Model I A O) (os : List O) (complete : ∀ o, o ∈ os)
    (n : ℕ) (rec : I → ℚ × Table A O n)
    (hr : ∀ i, rec i = (optimalValue M n i, solve M n i)) (i : I) (a : A) :
    actionData M os complete n rec i a =
      (qValue M (optimalValue M n) i a, (a, fun o => solve M n (M.next i a o))) := by
  cases n with
  | zero => simp [actionData, qValue, optimalValue, value]
  | succ n =>
      simp only [actionData, cache_apply, hr]
      rfl

/-- Strictly cached executable implementation of the original return object. -/
def fastSolve (M : Model I A O) (os : List O) (complete : ∀ o, o ∈ os) :
    (n : ℕ) → I → ℚ × Table A O n
  | 0, _ => (0, .halt)
  | n + 1, i =>
      let best := chooseScored (actionData M os complete n (fastSolve M os complete n) i)
        (M.actions i) (M.actions_nonempty i)
      (best.1, .node best.2.1 best.2.2)

/-- Equality of the exact value AND the whole returned table.  This includes
all counterfactual observation branches, not only positive-probability ones. -/
theorem fastSolve_eq (M : Model I A O) (os : List O) (complete : ∀ o, o ∈ os) :
    ∀ (n : ℕ) (i : I), fastSolve M os complete n i = (optimalValue M n i, solve M n i) := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
      intro i
      have hdata : actionData M os complete n (fastSolve M os complete n) i =
          fun a => (qValue M (optimalValue M n) i a,
            (a, fun o => solve M n (M.next i a o))) := by
        funext a
        exact actionData_spec M os complete n (fastSolve M os complete n) ih i a
      rw [fastSolve, hdata, chooseScored_eq]
      rfl

theorem fastSolve_value (M : Model I A O) (os : List O) (complete : ∀ o, o ∈ os)
    (n : ℕ) (i : I) :
    (fastSolve M os complete n i).1 = optimalValue M n i := by rw [fastSolve_eq]

theorem fastSolve_table (M : Model I A O) (os : List O) (complete : ∀ o, o ∈ os)
    (n : ℕ) (i : I) :
    (fastSolve M os complete n i).2 = solve M n i := by rw [fastSolve_eq]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFastSolver
