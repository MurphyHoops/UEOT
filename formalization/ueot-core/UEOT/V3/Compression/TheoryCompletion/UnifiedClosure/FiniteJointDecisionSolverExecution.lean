import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolver

/-!
# Finite table execution, explicit rows, and prefix payment

These results concern the actual `solve` output.  The finite tape law is the
table interpreter driven by the permitted observation kernel.  A source-facing
consumer still has to prove that this kernel and conditional reward are the
pushforward of its real primitive; neither is granted by the generic solver.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolver

open scoped BigOperators

universe uI uA uO

variable {I : Type uI} {A : Type uA} {O : Type uO} [Fintype O]

abbrev Tape (O : Type uO) : ℕ → Type uO
  | 0 => PUnit
  | n + 1 => O × Tape O n

instance tapeFintype (O : Type uO) [Fintype O] : (n : ℕ) → Fintype (Tape O n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd O (Tape O n) _ (tapeFintype O n)

def tapeWeight (M : Model I A O) : {n : ℕ} → I → Table A O n → Tape O n → ℚ
  | 0, _, .halt, _ => 1
  | _n + 1, i, .node a children, (o, w) =>
      M.prob i a o * tapeWeight M (M.next i a o) (children o) w

def tapePayoff (M : Model I A O) : {n : ℕ} → I → Table A O n → Tape O n → ℚ
  | 0, _, .halt, _ => 0
  | _n + 1, i, .node a children, (o, w) =>
      M.reward i a o + M.discount * tapePayoff M (M.next i a o) (children o) w

def tapeExpectation (M : Model I A O) {n : ℕ} (i : I) (p : Table A O n) : ℚ :=
  ∑ w : Tape O n, tapeWeight M i p w * tapePayoff M i p w

theorem tapeWeight_nonneg (M : Model I A O) :
    ∀ (n : ℕ) (i : I) (p : Table A O n), Feasible M i p →
      ∀ w, 0 ≤ tapeWeight M i p w := by
  intro n
  induction n with
  | zero => intro i p hp w; cases p; exact zero_le_one
  | succ n ih =>
      intro i p hp w
      cases p with
      | node a children =>
          rcases w with ⟨o, w⟩
          exact mul_nonneg (M.prob_nonneg i a hp.1 o) (ih _ _ (hp.2 o) w)

theorem tapeWeight_sum_one (M : Model I A O) :
    ∀ (n : ℕ) (i : I) (p : Table A O n), Feasible M i p →
      ∑ w : Tape O n, tapeWeight M i p w = 1 := by
  intro n
  induction n with
  | zero => intro i p hp; cases p; simp [Tape, tapeWeight]
  | succ n ih =>
      intro i p hp
      cases p with
      | node a children =>
          change (∑ w : O × Tape O n, _) = 1
          rw [Fintype.sum_prod_type]
          simp only [tapeWeight, ← Finset.mul_sum]
          simp_rw [ih _ _ (hp.2 _), mul_one]
          exact M.prob_sum_one i a hp.1

private theorem weighted_affine {S : Type*} [Fintype S] (p : S → ℚ)
    (hm : ∑ s, p s = 1) (c d : ℚ) (v : S → ℚ) :
    (∑ s, p s * (c + d * v s)) = c + d * ∑ s, p s * v s := by
  calc
    _ = (∑ s, p s) * c + d * (∑ s, p s * v s) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = _ := by rw [hm, one_mul]

/-- Exact expectation of this table's finite execution law. -/
theorem tapeExpectation_eq_value (M : Model I A O) :
    ∀ (n : ℕ) (i : I) (p : Table A O n), Feasible M i p →
      tapeExpectation M i p = value M i p := by
  intro n
  induction n with
  | zero => intro i p hp; cases p; simp [tapeExpectation, Tape, tapePayoff, value]
  | succ n ih =>
      intro i p hp
      cases p with
      | node a children =>
          change (∑ w : O × Tape O n, _) = _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro o ho
          simp only [tapeWeight, tapePayoff]
          let j := M.next i a o
          let W := tapeWeight M j (children o)
          let V := tapePayoff M j (children o)
          let q := M.prob i a o
          let r := M.reward i a o
          change (∑ w, q * W w * (r + M.discount * V w)) =
            q * (r + M.discount * value M j (children o))
          calc
            _ = q * ∑ w, W w * (r + M.discount * V w) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro w hw
              ring
            _ = q * (r + M.discount * ∑ w, W w * V w) := by
              rw [weighted_affine W (tapeWeight_sum_one M n j (children o) (hp.2 o))]
            _ = q * (r + M.discount * value M j (children o)) := by
              rw [show (∑ w, W w * V w) = value M j (children o) from
                ih j (children o) (hp.2 o)]

/-- A source-facing consumer can use this exact returned-table identity. -/
theorem returned_table_execution (M : Model I A O) (n : ℕ) (i : I) :
    (∑ w : Tape O n, tapeWeight M i (solve M n i) w = 1) ∧
      tapeExpectation M i (solve M n i) = optimalValue M n i :=
  ⟨tapeWeight_sum_one M n i _ (solve_feasible M n i),
    tapeExpectation_eq_value M n i _ (solve_feasible M n i)⟩

/-- Runtime lookup uses only the sequence of permitted observations. -/
def lookup : {n : ℕ} → Table A O n → List O → Option A
  | _, .halt, _ => none
  | _, .node a _, [] => some a
  | _, .node _ children, o :: os => lookup (children o) os

/-- A concrete export of the table.  `observations` is an explicit complete
enumeration; using a list avoids a noncomputable choice of enumeration. -/
def rows (observations : List O) : {n : ℕ} → Table A O n → List (List O × A)
  | _, .halt => []
  | _, .node a children =>
      ([], a) :: observations.flatMap (fun o =>
        (rows observations (children o)).map (fun row => (o :: row.1, row.2)))

omit [Fintype O] in
theorem rows_sound (observations : List O) :
    ∀ (n : ℕ) (p : Table A O n) (row : List O × A),
      row ∈ rows observations p → lookup p row.1 = some row.2 := by
  intro n
  induction n with
  | zero => intro p row hr; cases p; cases hr
  | succ n ih =>
      intro p row hr
      cases p with
      | node a children =>
          rcases List.mem_cons.mp hr with hrow | hr
          · subst row
            rfl
          · obtain ⟨o, ho, hmap⟩ := List.mem_flatMap.mp hr
            obtain ⟨r, hchild, heq⟩ := List.mem_map.mp hmap
            subst row
            exact ih (children o) r hchild

omit [Fintype O] in
theorem rows_complete (observations : List O) (hobs : ∀ o, o ∈ observations) :
    ∀ (n : ℕ) (p : Table A O n) (history : List O) (a : A),
      lookup p history = some a → (history, a) ∈ rows observations p := by
  intro n
  induction n with
  | zero => intro p history a h; cases p; cases h
  | succ n ih =>
      intro p history a h
      cases p with
      | node b children =>
          cases history with
          | nil =>
              have hab : b = a := Option.some.inj h
              subst a
              exact List.mem_cons_self
          | cons o os =>
              apply List.mem_cons_of_mem
              apply List.mem_flatMap.mpr
              refine ⟨o, hobs o, ?_⟩
              apply List.mem_map.mpr
              exact ⟨(os, a), ih (children o) os a h, rfl⟩

/-- The serialized rows describe exactly THIS returned scheduler, including
all its off-path rows, without exporting hidden source state. -/
theorem rows_exact (observations : List O) (hobs : ∀ o, o ∈ observations)
    {n : ℕ} (p : Table A O n) (history : List O) (a : A) :
    (history, a) ∈ rows observations p ↔ lookup p history = some a :=
  ⟨rows_sound observations n p (history, a), rows_complete observations hobs n p history a⟩

/-- The prepayment is a function of information available BEFORE the outcome.
The actual fee and balance transition are required only on source-supported
observations.  A consumer must derive these fields from the same primitive. -/
structure WalletContract (M : Model I A O) where
  balance : I → ℚ
  prepay : I → A → ℚ
  cost : I → A → O → ℚ
  prepay_nonneg : ∀ i a, 0 ≤ prepay i a
  affordable : ∀ i a, a ∈ M.actions i → prepay i a ≤ balance i
  cost_nonneg : ∀ i a, a ∈ M.actions i → ∀ o, 0 < M.prob i a o → 0 ≤ cost i a o
  cost_le_prepay : ∀ i a, a ∈ M.actions i → ∀ o,
    0 < M.prob i a o → cost i a o ≤ prepay i a
  balance_next : ∀ i a, a ∈ M.actions i → ∀ o,
    0 < M.prob i a o → balance (M.next i a o) = balance i - cost i a o

def PrepaidAlong (M : Model I A O) (C : WalletContract M) :
    {n : ℕ} → I → Table A O n → Tape O n → Prop
  | 0, _, .halt, _ => True
  | _n + 1, i, .node a children, (o, w) =>
      C.prepay i a ≤ C.balance i ∧ PrepaidAlong M C (M.next i a o) (children o) w

theorem feasible_prepaid (M : Model I A O) (C : WalletContract M) :
    ∀ (n : ℕ) (i : I) (p : Table A O n), Feasible M i p →
      ∀ w, PrepaidAlong M C i p w := by
  intro n
  induction n with
  | zero => intro i p hp w; cases p; trivial
  | succ n ih =>
      intro i p hp w
      cases p with
      | node a children =>
          rcases w with ⟨o, w⟩
          exact ⟨C.affordable i a hp.1, ih _ _ (hp.2 o) w⟩

/-- Information after `k` steps of this table's execution; `k` is clipped at
the finite horizon, which does not describe any post-horizon physical run. -/
def prefixInfo (M : Model I A O) :
    {n : ℕ} → I → Table A O n → Tape O n → ℕ → I
  | 0, i, .halt, _, _ => i
  | _n + 1, i, .node _ _, _, 0 => i
  | _n + 1, i, .node a children, (o, w), k + 1 =>
      prefixInfo M (M.next i a o) (children o) w k

def prefixCost (M : Model I A O) (C : WalletContract M) :
    {n : ℕ} → I → Table A O n → Tape O n → ℕ → ℚ
  | 0, _, .halt, _, _ => 0
  | _n + 1, _, .node _ _, _, 0 => 0
  | _n + 1, i, .node a children, (o, w), k + 1 =>
      C.cost i a o + prefixCost M C (M.next i a o) (children o) w k

/-- Exact pathwise accounting and no overdraft at EVERY execution prefix.
Expected costs cannot be substituted for the prepayment premise. -/
theorem feasible_prefix_ledger (M : Model I A O) (C : WalletContract M) :
    ∀ (n : ℕ) (i : I) (p : Table A O n), Feasible M i p → 0 ≤ C.balance i →
      ∀ w, 0 < tapeWeight M i p w → ∀ k,
        C.balance (prefixInfo M i p w k) = C.balance i - prefixCost M C i p w k ∧
        0 ≤ prefixCost M C i p w k ∧ prefixCost M C i p w k ≤ C.balance i := by
  intro n
  induction n with
  | zero =>
      intro i p hp hi w hw k
      cases p
      exact ⟨by simp [prefixInfo, prefixCost], le_rfl, hi⟩
  | succ n ih =>
      intro i p hp hi w hw k
      cases p with
      | node a children =>
          rcases w with ⟨o, w⟩
          have hprob : 0 ≤ M.prob i a o := M.prob_nonneg i a hp.1 o
          have hpos : 0 < M.prob i a o ∧
              0 < tapeWeight M (M.next i a o) (children o) w := by
            rcases mul_pos_iff.mp hw with h | h
            · exact h
            · exact ((not_lt_of_ge hprob) h.1).elim
          have hc := C.cost_nonneg i a hp.1 o hpos.1
          have hpre := C.affordable i a hp.1
          have hbound := C.cost_le_prepay i a hp.1 o hpos.1
          have hnext := C.balance_next i a hp.1 o hpos.1
          have hi' : 0 ≤ C.balance (M.next i a o) := by linarith
          cases k with
          | zero => exact ⟨by simp [prefixInfo, prefixCost], le_rfl, hi⟩
          | succ k =>
              have htail := ih (M.next i a o) (children o) (hp.2 o) hi' w hpos.2 k
              simp only [prefixInfo, prefixCost]
              exact ⟨by linarith [htail.1], add_nonneg hc htail.2.1,
                by linarith [htail.2.2]⟩

/-- THIS returned strategy's execution satisfies prepayment and its one wallet
at every supported prefix, provided the source supplies the wallet contract. -/
theorem returned_table_prefix_payment (M : Model I A O) (C : WalletContract M)
    (n : ℕ) (i : I) (hi : 0 ≤ C.balance i) (w : Tape O n)
    (hw : 0 < tapeWeight M i (solve M n i) w) :
    PrepaidAlong M C i (solve M n i) w ∧ ∀ k,
      C.balance (prefixInfo M i (solve M n i) w k) =
        C.balance i - prefixCost M C i (solve M n i) w k ∧
      0 ≤ prefixCost M C i (solve M n i) w k ∧
      prefixCost M C i (solve M n i) w k ≤ C.balance i :=
  ⟨feasible_prepaid M C n i _ (solve_feasible M n i) w,
    feasible_prefix_ledger M C n i _ (solve_feasible M n i) hi w hw⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolver
