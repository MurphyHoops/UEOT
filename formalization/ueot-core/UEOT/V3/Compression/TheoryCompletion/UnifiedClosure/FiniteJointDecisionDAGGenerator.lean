import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAG

/-!
# A memoized candidate DAG and its proved exact acceptance boundary

Every fresh canonical (remaining,state) key is completed once and appended to
one array.  A hash map shares that array index across all alternative-action
branches and across different histories.  Children have strictly smaller
remaining horizon and are completed before their parent.  No tree expansion,
old `solve`, old `fastSolve`, or proof-only `denote` is evaluated by generation.

The generator is deliberately outside the soundness boundary: the existing
exact rational checker checks ALL alternative positive branches and key
uniqueness. A successful `certify` produces proofs about this exact array and
root index. A malformed candidate, faulty memo index, omitted branch, altered
value or invalid root is rejected. Public model inputs are closed over by M;
`generate` always starts with a fresh empty memo, so no cross-input cache leaks.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAGGenerator

open scoped BigOperators
open FiniteJointDecisionSolver FiniteJointDecisionSupportedPolicy FiniteJointDecisionDAG

universe uI uA uO

variable {I : Type uI} {A : Type uA} {O : Type uO}
variable [Fintype O] [Fintype A] [DecidableEq I] [DecidableEq A] [DecidableEq O]

abbrev Edge (A : Type uA) (O : Type uO) := A × O × ℕ

def edgeLookup : List (Edge A O) → A → O → Option ℕ
  | [], _, _ => none
  | (a', o', k) :: rest, a, o =>
      if a = a' ∧ o = o' then some k else edgeLookup rest a o

structure BuildState (I : Type uI) (A : Type uA) (O : Type uO) [BEq I] [Hashable I] where
  nodes : Graph I A O
  memo : Std.HashMap (ℕ × I) ℕ
  hits : ℕ
  expansions : ℕ

variable [BEq I] [Hashable I]

def emptyState : BuildState I A O := ⟨#[], {}, 0, 0⟩

def insertNode (r : Node I A O) (s : BuildState I A O) : ℕ × BuildState I A O :=
  let j := s.nodes.size
  (j, ⟨s.nodes.push r, s.memo.insert (key r) j, s.hits, s.expansions + 1⟩)

/-- Explicit observation enumeration controls construction only. Completeness
is independently enforced by the checker quantifying over the original O. -/
def build (M : Model I A O) (observations : List O) :
    (n : ℕ) → I → BuildState I A O → ℕ × BuildState I A O
  | 0, i, s =>
      match s.memo.get? (0, i) with
      | some j => (j, { s with hits := s.hits + 1 })
      | none =>
          insertNode ⟨0, i, safeAction M i, 0, fun _ _ => none⟩ s
  | n + 1, i, s =>
      match s.memo.get? (n + 1, i) with
      | some j => (j, { s with hits := s.hits + 1 })
      | none =>
          let expanded : List (Edge A O) × BuildState I A O :=
            (M.actions i).foldl
              (fun acc a => observations.foldl
                (fun acc o =>
                  if 0 < M.prob i a o then
                    let child := build M observations n (M.next i a o) acc.2
                    ((a, o, child.1) :: acc.1, child.2)
                  else acc)
                acc)
              ([], s)
          let provisional : Node I A O :=
            ⟨n + 1, i, safeAction M i, 0, edgeLookup expanded.1⟩
          let a := chooseBest (score M expanded.2.nodes provisional)
            (M.actions i) (M.actions_nonempty i)
          let v := score M expanded.2.nodes provisional a
          insertNode { provisional with choice := a, value := v } expanded.2

structure Candidate (I : Type uI) (A : Type uA) (O : Type uO) where
  graph : Graph I A O
  root : ℕ
  cacheHits : ℕ
  computedNodes : ℕ
  memoEntries : ℕ

/-- The actual planning entry point. It never calls the old exponential tree
generator, and its returned array retains all proof-graph nodes exactly once. -/
def generate (M : Model I A O) (observations : List O) (H : ℕ) (initial : I) :
    Candidate I A O :=
  let result := build M observations H initial emptyState
  ⟨result.2.nodes, result.1, result.2.hits, result.2.expansions, result.2.memo.size⟩

/-- A successful checked product binds the exact graph, root and public input.
All proofs here are supplied by `certify`, not by an external Python oracle. -/
structure Certified (M : Model I A O) (H : ℕ) (initial : I) where
  graph : Graph I A O
  root : Fin graph.size
  good : Good M graph
  remaining : (graph[root.val]).remaining = H
  initial_state : (graph[root.val]).state = initial

def certify (M : Model I A O) (H : ℕ) (initial : I) (c : Candidate I A O) :
    Option (Certified M H initial) :=
  if hc : check M c.graph = true then
    if hr : c.root < c.graph.size then
      if hi : (c.graph[c.root]'hr).remaining = H ∧ (c.graph[c.root]'hr).state = initial then
        some ⟨c.graph, ⟨c.root, hr⟩, check_sound M c.graph hc, hi.1, hi.2⟩
      else none
    else none
  else none

/-- Failure is explicit and carries no optimality claim. -/
def plan (M : Model I A O) (observations : List O) (H : ℕ) (initial : I) :
    Option (Certified M H initial) :=
  certify M H initial (generate M observations H initial)

theorem certified_value (M : Model I A O) (H : ℕ) (initial : I)
    (c : Certified M H initial) :
    (c.graph[c.root.val]).value = optimalValue M H initial := by
  simpa only [c.initial_state] using
    node_value_eq_optimal M c.graph c.good H c.root c.remaining

theorem certified_policy_value (M : Model I A O) (H : ℕ) (initial : I)
    (c : Certified M H initial) :
    value M initial (denote M c.graph H initial (some c.root.val)) =
      (c.graph[c.root.val]).value := by
  simpa only [c.initial_state] using
    denote_value_eq_node M c.graph c.good H c.root c.remaining

theorem certified_policy_feasible (M : Model I A O) (H : ℕ) (initial : I)
    (c : Certified M H initial) :
    Feasible M initial (denote M c.graph H initial (some c.root.val)) :=
  denote_feasible M c.graph H initial (some c.root.val)

theorem certified_randomized_upper (M : Model I A O) (H : ℕ) (initial : I)
    (c : Certified M H initial) (pi : RawCausalPolicy M) (h : pi.Memory)
    (hi : pi.info h = initial) (ha : SupportedAdmissible M pi H h) :
    rawValue M pi H h ≤ ((c.graph[c.root.val]).value : ℝ) :=
  rawValue_le_node M c.graph c.good H c.root c.remaining pi h
    (hi.trans c.initial_state.symm) ha

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAGGenerator
