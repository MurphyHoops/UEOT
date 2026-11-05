import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSupportedPolicy

/-!
# Exact certificates for a shared finite decision DAG

The artifact is an array of nodes, not a recursively expanded observation tree.
Each node records one remaining-horizon/state key and finite edge references.
The checker inspects every legal action and every positive-probability receipt,
including the alternatives not selected by the execution policy.  Its soundness
is proved against the existing exact solver and the existing supported real
full-history comparison class.

`denote` is a proof-only denotation used to reuse old source and wallet theorems.
The actual controller below reads node indices directly; the generator and
output driver never evaluate `denote`.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAG

open scoped BigOperators
open FiniteJointDecisionSolver FiniteJointDecisionSupportedPolicy

universe uI uA uO uMem

structure Node (I : Type uI) (A : Type uA) (O : Type uO) where
  remaining : ℕ
  state : I
  choice : A
  value : ℚ
  next : A → O → Option ℕ

abbrev Graph (I : Type uI) (A : Type uA) (O : Type uO) := Array (Node I A O)

variable {I : Type uI} {A : Type uA} {O : Type uO}
variable [Fintype O] [Fintype A] [DecidableEq I] [DecidableEq A] [DecidableEq O]

def key (r : Node I A O) : ℕ × I := (r.remaining, r.state)

def edgeValue (G : Graph I A O) (r : Node I A O) (a : A) (o : O) : ℚ :=
  match r.next a o with
  | none => 0
  | some k => if hk : k < G.size then (G[k]'hk).value else 0

def score (M : Model I A O) (G : Graph I A O) (r : Node I A O) (a : A) : ℚ :=
  ∑ o, M.prob r.state a o *
    (M.reward r.state a o + M.discount * edgeValue G r a o)

/-- This check includes the target state, not merely an arbitrary child value. -/
def EdgeValid (M : Model I A O) (G : Graph I A O)
    (r : Node I A O) (a : A) (o : O) : Prop :=
  match r.next a o with
  | none => False
  | some k =>
      if hk : k < G.size then
        (G[k]'hk).remaining + 1 = r.remaining ∧
        (G[k]'hk).state = M.next r.state a o
      else False

instance edgeValid_decidable (M : Model I A O) (G : Graph I A O)
    (r : Node I A O) (a : A) (o : O) : Decidable (EdgeValid M G r a o) := by
  unfold EdgeValid
  split
  · infer_instance
  · split <;> infer_instance

def NodeValid (M : Model I A O) (G : Graph I A O) (r : Node I A O) : Prop :=
  match r.remaining with
  | 0 => r.value = 0
  | _ + 1 =>
      r.choice = chooseBest (score M G r) (M.actions r.state) (M.actions_nonempty r.state) ∧
      r.value = score M G r r.choice ∧
      ∀ a, a ∈ M.actions r.state → ∀ o, 0 < M.prob r.state a o →
        EdgeValid M G r a o

instance nodeValid_decidable (M : Model I A O) (G : Graph I A O)
    (r : Node I A O) : Decidable (NodeValid M G r) := by
  unfold NodeValid
  split <;> infer_instance

/-- The finite proof graph has no duplicate keys, and all its rows pass. -/
def Good (M : Model I A O) (G : Graph I A O) : Prop :=
  Function.Injective (fun j : Fin G.size => key (G[j.val])) ∧
  ∀ j : Fin G.size, NodeValid M G (G[j.val])

instance good_decidable (M : Model I A O) (G : Graph I A O) : Decidable (Good M G) := by
  unfold Good Function.Injective
  infer_instance

/-- Executable exact rational verification. No Python result is trusted. -/
def check (M : Model I A O) (G : Graph I A O) : Bool := decide (Good M G)

theorem check_sound (M : Model I A O) (G : Graph I A O) (h : check M G = true) :
    Good M G := of_decide_eq_true h

theorem good_of_check (M : Model I A O) (G : Graph I A O) :
    check M G = true ↔ Good M G := by simp [check]

theorem valid_succ (M : Model I A O) (G : Graph I A O) (r : Node I A O)
    (n : ℕ) (hn : r.remaining = n + 1) (hv : NodeValid M G r) :
    r.choice = chooseBest (score M G r) (M.actions r.state) (M.actions_nonempty r.state) ∧
    r.value = score M G r r.choice ∧
    ∀ a, a ∈ M.actions r.state → ∀ o, 0 < M.prob r.state a o →
      EdgeValid M G r a o := by
  simpa only [NodeValid, hn] using hv

theorem valid_choice_mem (M : Model I A O) (G : Graph I A O) (r : Node I A O)
    (n : ℕ) (hn : r.remaining = n + 1) (hv : NodeValid M G r) :
    r.choice ∈ M.actions r.state := by
  rw [(valid_succ M G r n hn hv).1]
  exact chooseBest_mem _ _ _

theorem edgeValid_witness (M : Model I A O) (G : Graph I A O)
    (r : Node I A O) (a : A) (o : O) (h : EdgeValid M G r a o) :
    ∃ k : Fin G.size, r.next a o = some k.val ∧
      (G[k.val]).remaining + 1 = r.remaining ∧ (G[k.val]).state = M.next r.state a o := by
  cases he : r.next a o with
  | none => simp [EdgeValid, he] at h
  | some k =>
      by_cases hk : k < G.size
      · exact ⟨⟨k, hk⟩, rfl, by simpa only [EdgeValid, he, dif_pos hk] using h⟩
      · simp [EdgeValid, he, hk] at h

theorem edgeValue_at (G : Graph I A O) (r : Node I A O) (a : A) (o : O)
    (k : Fin G.size) (he : r.next a o = some k.val) :
    edgeValue G r a o = (G[k.val]).value := by
  simp [edgeValue, he, k.isLt]

/-- Zero-probability successors need no graph node. Every positive alternative
does, and its already established exact value supplies the same Bellman score. -/
theorem score_eq_qValue (M : Model I A O) (G : Graph I A O)
    (r : Node I A O) (n : ℕ) (hn : r.remaining = n + 1)
    (hv : NodeValid M G r)
    (ih : ∀ k : Fin G.size, (G[k.val]).remaining = n →
      (G[k.val]).value = optimalValue M n (G[k.val]).state)
    (a : A) (ha : a ∈ M.actions r.state) :
    score M G r a = qValue M (optimalValue M n) r.state a := by
  unfold score qValue
  apply Finset.sum_congr rfl
  intro o ho
  by_cases hz : M.prob r.state a o = 0
  · simp [hz]
  · have hp : 0 < M.prob r.state a o := by
      rcases eq_or_lt_of_le (M.prob_nonneg r.state a ha o) with heq | hp
      · exact (hz heq.symm).elim
      · exact hp
    obtain ⟨k, he, hr, hs⟩ := edgeValid_witness M G r a o
      ((valid_succ M G r n hn hv).2.2 a ha o hp)
    have hk : (G[k.val]).remaining = n := by omega
    rw [edgeValue_at G r a o k he, ih k hk, hs]

/-- The checker proves exact optimal values at ALL certified nodes, including
the nodes needed solely to bound legal alternatives to the chosen policy. -/
theorem node_value_eq_optimal (M : Model I A O) (G : Graph I A O) (hg : Good M G) :
    ∀ (n : ℕ) (j : Fin G.size), (G[j.val]).remaining = n →
      (G[j.val]).value = optimalValue M n (G[j.val]).state := by
  intro n
  induction n with
  | zero =>
      intro j hn
      have hv := hg.2 j
      simpa only [NodeValid, hn, optimalValue_zero] using hv
  | succ n ih =>
      intro j hn
      let r := G[j.val]
      have hv : NodeValid M G r := hg.2 j
      have hv' := valid_succ M G r n hn hv
      have hm := valid_choice_mem M G r n hn hv
      have hs := score_eq_qValue M G r n hn hv ih
      apply le_antisymm
      · rw [hv'.2.1, hs r.choice hm]
        exact qValue_le_optimalValue M n r.state r.choice hm
      · calc
          optimalValue M (n + 1) r.state =
              qValue M (optimalValue M n) r.state (chosenAction M n r.state) := rfl
          _ = score M G r (chosenAction M n r.state) :=
            (hs _ (chosenAction_mem M n r.state)).symm
          _ ≤ score M G r
              (chooseBest (score M G r) (M.actions r.state) (M.actions_nonempty r.state)) :=
            le_chooseBest _ _ _ _ (chosenAction_mem M n r.state)
          _ = r.value := by rw [← hv'.1, ← hv'.2.1]

theorem selectBest_congr_on (s t : A → ℚ) :
    ∀ (xs : List A) (a : A), (∀ b, b ∈ a :: xs → s b = t b) →
      selectBest s a xs = selectBest t a xs := by
  intro xs
  induction xs with
  | nil => intro a h; rfl
  | cons b bs ih =>
      intro a h
      have ht := ih b (fun c hc => h c (List.mem_cons_of_mem a hc))
      have ha := h a List.mem_cons_self
      have hb := h (selectBest t b bs)
        (List.mem_cons_of_mem a (selectBest_mem t bs b))
      change (if s a < s (selectBest s b bs) then selectBest s b bs else a) =
        (if t a < t (selectBest t b bs) then selectBest t b bs else a)
      rw [ht, ha, hb]

theorem chooseBest_congr_on (s t : A → ℚ) (xs : List A) (hne : xs ≠ [])
    (h : ∀ a, a ∈ xs → s a = t a) : chooseBest s xs hne = chooseBest t xs hne := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a as => exact selectBest_congr_on s t as a h

/-- The original action order and first-tie rule are retained on graph support. -/
theorem node_choice_eq_chosen (M : Model I A O) (G : Graph I A O) (hg : Good M G)
    (n : ℕ) (j : Fin G.size) (hn : (G[j.val]).remaining = n + 1) :
    (G[j.val]).choice = chosenAction M n (G[j.val]).state := by
  have hv := hg.2 j
  rw [(valid_succ M G (G[j.val]) n hn hv).1]
  exact chooseBest_congr_on _ _ _ _
    (score_eq_qValue M G (G[j.val]) n hn hv (node_value_eq_optimal M G hg n))

/-- Safe total behavior outside the checked graph. In the Register consumer,
the first action is stop, so this is the registered root-idle commitment. -/
def safeAction (M : Model I A O) (i : I) : A :=
  chooseBest (fun _ => 0) (M.actions i) (M.actions_nonempty i)

theorem safeAction_mem (M : Model I A O) (i : I) : safeAction M i ∈ M.actions i :=
  chooseBest_mem _ _ _

/-- Direct finite-state control. It reads a stored action, never a tree. -/
def controllerAction (M : Model I A O) (G : Graph I A O)
    (n : ℕ) (i : I) (cursor : Option ℕ) : A :=
  match cursor with
  | none => safeAction M i
  | some j =>
      if hj : j < G.size then
        let r := G[j]'hj
        if r.remaining = n ∧ r.state = i ∧ r.choice ∈ M.actions i then r.choice
        else safeAction M i
      else safeAction M i

/-- Only a supported receipt follows a stored edge. An impossible receipt
enters the safe total fallback, with the actual world continuing to run. -/
def controllerNext (M : Model I A O) (G : Graph I A O)
    (n : ℕ) (i : I) (cursor : Option ℕ) (a : A) (o : O) : Option ℕ :=
  match cursor with
  | none => none
  | some j =>
      if hj : j < G.size then
        let r := G[j]'hj
        if r.remaining = n ∧ r.state = i ∧ r.choice = a ∧ 0 < M.prob i a o then
          r.next a o
        else none
      else none

theorem controllerAction_mem (M : Model I A O) (G : Graph I A O)
    (n : ℕ) (i : I) (cursor : Option ℕ) :
    controllerAction M G n i cursor ∈ M.actions i := by
  cases cursor with
  | none => exact safeAction_mem M i
  | some j =>
      simp only [controllerAction]
      split
      · split
        · exact ‹_ ∧ _ ∧ _›.2.2
        · exact safeAction_mem M i
      · exact safeAction_mem M i

theorem controllerAction_at (M : Model I A O) (G : Graph I A O)
    (n : ℕ) (j : Fin G.size) (hn : (G[j.val]).remaining = n)
    (ha : (G[j.val]).choice ∈ M.actions (G[j.val]).state) :
    controllerAction M G n (G[j.val]).state (some j.val) = (G[j.val]).choice := by
  simp [controllerAction, j.isLt, hn, ha]

theorem controllerNext_at (M : Model I A O) (G : Graph I A O)
    (n : ℕ) (j : Fin G.size) (hn : (G[j.val]).remaining = n) (o : O)
    (hp : 0 < M.prob (G[j.val]).state (G[j.val]).choice o) :
    controllerNext M G n (G[j.val]).state (some j.val) (G[j.val]).choice o =
      (G[j.val]).next (G[j.val]).choice o := by
  simp [controllerNext, j.isLt, hn, hp]

/-- Proof denotation only. This function is deliberately absent from the
runtime generator, serializer and direct native graph interpreter. -/
def denote (M : Model I A O) (G : Graph I A O) :
    (n : ℕ) → I → Option ℕ → Table A O n
  | 0, _, _ => .halt
  | n + 1, i, cursor =>
      let a := controllerAction M G (n + 1) i cursor
      .node a (fun o => denote M G n (M.next i a o)
        (controllerNext M G (n + 1) i cursor a o))

/-- Safety is global, including unknown indices and zero-probability rows. -/
theorem denote_feasible (M : Model I A O) (G : Graph I A O) :
    ∀ (n : ℕ) (i : I) (cursor : Option ℕ), Feasible M i (denote M G n i cursor) := by
  intro n
  induction n with
  | zero => intro i cursor; trivial
  | succ n ih =>
      intro i cursor
      exact ⟨controllerAction_mem M G (n + 1) i cursor, fun o => ih _ _⟩

/-- The chosen execution graph attains its own checked node value. Alternative
edges were also checked, which is why this value is globally optimal. -/
theorem denote_value_eq_node (M : Model I A O) (G : Graph I A O) (hg : Good M G) :
    ∀ (n : ℕ) (j : Fin G.size), (G[j.val]).remaining = n →
      value M (G[j.val]).state (denote M G n (G[j.val]).state (some j.val)) = (G[j.val]).value := by
  intro n
  induction n with
  | zero =>
      intro j hn
      have hv : (G[j.val]).value = 0 := by simpa only [NodeValid, hn] using hg.2 j
      simpa only [denote, value] using hv.symm
  | succ n ih =>
      intro j hn
      have hv := valid_succ M G (G[j.val]) n hn (hg.2 j)
      have ha := valid_choice_mem M G (G[j.val]) n hn (hg.2 j)
      have hact := controllerAction_at M G (n + 1) j hn ha
      simp only [denote, value, hact]
      rw [hv.2.1]
      unfold score
      apply Finset.sum_congr rfl
      intro o ho
      by_cases hz : M.prob (G[j.val]).state (G[j.val]).choice o = 0
      · simp [hz]
      · have hp : 0 < M.prob (G[j.val]).state (G[j.val]).choice o := by
          rcases eq_or_lt_of_le (M.prob_nonneg (G[j.val]).state (G[j.val]).choice ha o) with heq | hp
          · exact (hz heq.symm).elim
          · exact hp
        obtain ⟨k, he, hr, hs⟩ := edgeValid_witness M G (G[j.val]) (G[j.val]).choice o
          (hv.2.2 _ ha o hp)
        have hk : (G[k.val]).remaining = n := by omega
        rw [controllerNext_at M G (n + 1) j hn o hp, he,
          edgeValue_at G (G[j.val]) (G[j.val]).choice o k he]
        simpa only [hs] using congrArg
          (fun v : ℚ => M.prob (G[j.val]).state (G[j.val]).choice o *
            (M.reward (G[j.val]).state (G[j.val]).choice o + M.discount * v)) (ih k hk)

theorem denote_optimal (M : Model I A O) (G : Graph I A O) (hg : Good M G)
    (n : ℕ) (j : Fin G.size) (hn : (G[j.val]).remaining = n) :
    value M (G[j.val]).state (denote M G n (G[j.val]).state (some j.val)) =
      optimalValue M n (G[j.val]).state :=
  (denote_value_eq_node M G hg n j hn).trans (node_value_eq_optimal M G hg n j hn)

/-- Full-history real randomization remains in the comparison class. The
competitor need not use the finite controller's memory or selected edges. -/
theorem rawValue_le_node (M : Model I A O) (G : Graph I A O) (hg : Good M G)
    (n : ℕ) (j : Fin G.size) (hn : (G[j.val]).remaining = n)
    (pi : RawCausalPolicy M) (h : pi.Memory) (hi : pi.info h = (G[j.val]).state)
    (ha : SupportedAdmissible M pi n h) :
    rawValue M pi n h ≤ ((G[j.val]).value : ℝ) := by
  rw [node_value_eq_optimal M G hg n j hn]
  simpa only [hi] using rawValue_le_solve M pi n h ha

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAG
