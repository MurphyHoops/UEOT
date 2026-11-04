import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionBelief
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolverExecution

/-!
# The exact finite solver on one hidden primitive source

The world is never passed to the scheduler.  Its information state consists of
the joint posterior and registered public memory.  This file derives the value
and entire permitted trace law of every table from direct primitive expansion.
The same bridge is proved for arbitrary-history randomized policies with real
action probabilities.  Thus the solver's optimum is an optimum of the actual
hidden-source process, not only a Bellman model supplied without a bridge.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFilteredModel

open scoped BigOperators
open FiniteJointDecisionBelief FiniteJointDecisionSolver

universe uW uA uO uM uH

variable {W : Type uW} {A : Type uA} {O : Type uO} {Z : Type} {M : Type uM}
variable [Fintype Z] [Fintype O] [DecidableEq O]

def filteredModel (K : Source W A O Z)
    (actions : Belief W × M → List A) (hne : ∀ i, actions i ≠ [])
    (advance : M → A → O → M) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d) :
    Model (Belief W × M) A O where
  actions := actions
  actions_nonempty := hne
  prob i a o := mass K i.1 a o
  reward _ a o := gain a o
  next i a o := (posterior K i.1 a o, advance i.2 a o)
  prob_nonneg i a _ o := mass_nonneg K i.1 a o
  prob_sum_one i a _ := mass_total K i.1 a
  discount := d
  discount_nonneg := hd

/-- Direct execution of THIS table by the real hidden primitive.  The only
branch supplied to the table is `K.observe`; it never receives the world. -/
def sourceValue (K : Source W A O Z) (gain : A → O → ℚ) (d : ℚ) :
    {n : ℕ} → Table A O n → W → ℚ
  | 0, .halt, _ => 0
  | _n + 1, .node a children, w =>
      ∑ z, K.chance w z * (gain a (K.observe w a z) + d *
        sourceValue K gain d (children (K.observe w a z)) (K.next w a z))

theorem primitive_expectation (K : Source W A O Z) (b : Belief W) (a : A)
    (f : O → W → ℚ) :
    expect b (fun w => ∑ z, K.chance w z * f (K.observe w a z) (K.next w a z)) =
      ∑ o, mass K b a o * expect (posterior K b a o) (f o) := by
  rw [total_expectation, Fintype.sum_prod_type]
  simp only [expect, Finset.mul_sum, mul_assoc]

/-- SAME-table value equals the primitive execution's actual expected reward. -/
theorem value_eq_source (K : Source W A O Z)
    (actions : Belief W × M → List A) (hne : ∀ i, actions i ≠ [])
    (advance : M → A → O → M) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d) :
    ∀ (n : ℕ) (p : Table A O n) (b : Belief W) (m : M),
      value (filteredModel K actions hne advance gain d hd) (b, m) p =
        expect b (sourceValue K gain d p) := by
  intro n
  induction n with
  | zero => intro p b m; cases p; simp [value, sourceValue, expect_const]
  | succ n ih =>
      intro p b m
      cases p with
      | node a children =>
          change (∑ o, mass K b a o * (gain a o + d *
            value (filteredModel K actions hne advance gain d hd)
              (posterior K b a o, advance m a o) (children o))) = _
          simp_rw [ih]
          have hsrc : sourceValue K gain d (.node a children) =
              (fun w => ∑ z, K.chance w z * (gain a (K.observe w a z) +
                d * sourceValue K gain d (children (K.observe w a z)) (K.next w a z))) := by
            funext w
            rfl
          rw [hsrc, primitive_expectation K b a
            (fun o w => gain a o + d * sourceValue K gain d (children o) w)]
          simp only [expect_add, expect_const, expect_mul]

/-- All finite visible-trace tests evaluated by direct primitive expansion.
For a deterministic table its own actions are recoverable from this observation
tape and the table, so this determines the full permitted action/receipt law. -/
def sourceTraceExpectation (K : Source W A O Z) :
    {n : ℕ} → Table A O n → (Tape O n → ℚ) → W → ℚ
  | 0, .halt, test, _ => test PUnit.unit
  | _n + 1, .node a children, test, w =>
      ∑ z, K.chance w z *
        sourceTraceExpectation K (children (K.observe w a z))
          (fun rest => test (K.observe w a z, rest)) (K.next w a z)

def traceExpectation (N : Model (Belief W × M) A O) {n : ℕ}
    (i : Belief W × M) (p : Table A O n) (test : Tape O n → ℚ) : ℚ :=
  ∑ tape, tapeWeight N i p tape * test tape

theorem traceExpectation_succ (N : Model (Belief W × M) A O)
    (i : Belief W × M) {n : ℕ} (a : A) (children : O → Table A O n)
    (test : Tape O (n + 1) → ℚ) :
    traceExpectation N i (.node a children) test =
      ∑ o, N.prob i a o * traceExpectation N (N.next i a o) (children o)
        (fun rest => test (o, rest)) := by
  unfold traceExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro o ho
  simp only [tapeWeight, Finset.mul_sum, mul_assoc]

/-- Equality for EVERY finite trace test: the observed interpreter law is the
pushforward of the SAME original hidden primitive, including zero-mass rows. -/
theorem traceExpectation_eq_source (K : Source W A O Z)
    (actions : Belief W × M → List A) (hne : ∀ i, actions i ≠ [])
    (advance : M → A → O → M) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d) :
    ∀ (n : ℕ) (p : Table A O n) (b : Belief W) (m : M) (test : Tape O n → ℚ),
      traceExpectation (filteredModel K actions hne advance gain d hd) (b, m) p test =
        expect b (sourceTraceExpectation K p test) := by
  intro n
  induction n with
  | zero =>
      intro p b m test
      cases p
      simp [traceExpectation, tapeWeight, sourceTraceExpectation, expect_const, Tape]
  | succ n ih =>
      intro p b m test
      cases p with
      | node a children =>
          rw [traceExpectation_succ]
          change (∑ o, mass K b a o *
            traceExpectation (filteredModel K actions hne advance gain d hd)
              (posterior K b a o, advance m a o) (children o) (fun rest => test (o, rest))) = _
          simp_rw [ih]
          exact (primitive_expectation K b a
            (fun o w => sourceTraceExpectation K (children o) (fun rest => test (o, rest)) w)).symm

noncomputable def expectReal (b : Belief W) (f : W → ℝ) : ℝ :=
  ∑ x, (b.weight x : ℝ) * f (b.state x)

theorem expectReal_const (b : Belief W) (c : ℝ) : expectReal b (fun _ => c) = c := by
  rw [expectReal, ← Finset.sum_mul]
  have hm : ∑ x, (b.weight x : ℝ) = 1 := by exact_mod_cast b.total
  rw [hm, one_mul]

theorem expectReal_add (b : Belief W) (f g : W → ℝ) :
    expectReal b (fun w => f w + g w) = expectReal b f + expectReal b g := by
  simp [expectReal, mul_add, Finset.sum_add_distrib]

theorem expectReal_mul (b : Belief W) (c : ℝ) (f : W → ℝ) :
    expectReal b (fun w => c * f w) = c * expectReal b f := by
  simp only [expectReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem expectReal_sum {T : Type*} [Fintype T] (b : Belief W) (f : T → W → ℝ) :
    expectReal b (fun w => ∑ t, f t w) = ∑ t, expectReal b (f t) := by
  simp only [expectReal, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectReal_of_rat (b : Belief W) (f : W → ℚ) :
    expectReal b (fun w => (f w : ℝ)) = (expect b f : ℝ) := by
  simp only [expectReal, expect, Rat.cast_sum, Rat.cast_mul]

/-- The posterior identity for arbitrary real continuation values; this is
needed because competitor action probabilities need not be rational. -/
theorem posterior_identity_real (K : Source W A O Z) (b : Belief W) (a : A) (o : O)
    (f : W → ℝ) :
    (mass K b a o : ℝ) * expectReal (posterior K b a o) f =
      ∑ x : b.Atom × Z, (joint K b a o x : ℝ) * f (K.next (b.state x.1) a x.2) := by
  by_cases h : mass K b a o = 0
  · simp only [h, Rat.cast_zero, zero_mul]
    symm
    exact Finset.sum_eq_zero fun x _ => by rw [joint_zero K b a o h x]; simp
  · rw [posterior, dif_neg h]
    dsimp only [expectReal]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hr : (mass K b a o : ℝ) ≠ 0 := by exact_mod_cast h
    simp only [normalizeWeights_apply]
    push_cast
    field_simp [hr]

theorem total_expectation_real (K : Source W A O Z) (b : Belief W) (a : A)
    (f : O → W → ℝ) :
    (∑ o, (mass K b a o : ℝ) * expectReal (posterior K b a o) (f o)) =
      ∑ x : b.Atom × Z, (b.weight x.1 : ℝ) * (K.chance (b.state x.1) x.2 : ℝ) *
        f (K.observe (b.state x.1) a x.2) (K.next (b.state x.1) a x.2) := by
  simp_rw [posterior_identity_real]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (K.observe (b.state x.1) a x.2)]
  · simp [joint]
  · intro o ho hne
    simp [joint, Ne.symm hne]
  · simp

theorem primitive_expectation_real (K : Source W A O Z) (b : Belief W) (a : A)
    (f : O → W → ℝ) :
    expectReal b (fun w => ∑ z, (K.chance w z : ℝ) * f (K.observe w a z) (K.next w a z)) =
      ∑ o, (mass K b a o : ℝ) * expectReal (posterior K b a o) (f o) := by
  rw [total_expectation_real, Fintype.sum_prod_type]
  simp only [expectReal, Finset.mul_sum, mul_assoc]

/-- The competing causal policy runs against the original hidden source.
Its probabilities are functions of its permitted memory, not of `w`. -/
noncomputable def sourceCausalValue (K : Source W A O Z) (gain : A → O → ℚ) (d : ℚ)
    {N : Model (Belief W × M) A O} [Fintype A] (pi : CausalPolicy N) :
    ℕ → pi.Memory → W → ℝ
  | 0, _, _ => 0
  | n + 1, h, w =>
      ∑ a, pi.actionProb h a * ∑ z, (K.chance w z : ℝ) *
        ((gain a (K.observe w a z) : ℝ) + (d : ℝ) *
          sourceCausalValue K gain d pi n (pi.advance h a (K.observe w a z)) (K.next w a z))

/-- Exact source bridge for EVERY same-information causal randomized policy. -/
theorem sourceCausalValue_eq_model (K : Source W A O Z)
    (actions : Belief W × M → List A) (hne : ∀ i, actions i ≠ [])
    (advance : M → A → O → M) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d)
    [Fintype A] (pi : CausalPolicy (filteredModel K actions hne advance gain d hd)) :
    ∀ (n : ℕ) (h : pi.Memory),
      expectReal (pi.info h).1 (sourceCausalValue K gain d pi n h) =
        causalValue (filteredModel K actions hne advance gain d hd) pi n h := by
  intro n
  induction n with
  | zero => intro h; simp [sourceCausalValue, causalValue, expectReal_const]
  | succ n ih =>
      intro h
      simp only [sourceCausalValue, causalValue]
      rw [expectReal_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [expectReal_mul]
      rw [primitive_expectation_real K (pi.info h).1 a
        (fun o w => (gain a o : ℝ) + (d : ℝ) *
          sourceCausalValue K gain d pi n (pi.advance h a o) w)]
      apply congrArg (fun t : ℝ => pi.actionProb h a * t)
      apply Finset.sum_congr rfl
      intro o ho
      rw [expectReal_add, expectReal_const, expectReal_mul]
      change (mass K (pi.info h).1 a o : ℝ) * ((gain a o : ℝ) + (d : ℝ) *
        expectReal (posterior K (pi.info h).1 a o)
          (sourceCausalValue K gain d pi n (pi.advance h a o))) =
        (mass K (pi.info h).1 a o : ℝ) * ((gain a o : ℝ) + (d : ℝ) *
          causalValue (filteredModel K actions hne advance gain d hd) pi n (pi.advance h a o))
      apply congrArg (fun t : ℝ => (mass K (pi.info h).1 a o : ℝ) *
        ((gain a o : ℝ) + (d : ℝ) * t))
      have hb := congrArg Prod.fst (pi.info_advance h a o)
      change (pi.info (pi.advance h a o)).1 = posterior K (pi.info h).1 a o at hb
      rw [← hb]
      exact ih (pi.advance h a o)

/-- The numerical result is the actual payoff of THIS returned strategy. -/
theorem returned_source_value (K : Source W A O Z)
    (actions : Belief W × M → List A) (hne : ∀ i, actions i ≠ [])
    (advance : M → A → O → M) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d)
    (n : ℕ) (i : Belief W × M) :
    expect i.1 (sourceValue K gain d
      (solve (filteredModel K actions hne advance gain d hd) n i)) =
        optimalValue (filteredModel K actions hne advance gain d hd) n i :=
  (value_eq_source K actions hne advance gain d hd n _ i.1 i.2).symm

/-- Actual hidden-source optimality, against arbitrary real randomized causal
policies subject to the SAME permitted information and prepaid action menu. -/
theorem actual_causal_le_returned (K : Source W A O Z)
    (actions : Belief W × M → List A) (hne : ∀ i, actions i ≠ [])
    (advance : M → A → O → M) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d)
    [Fintype A] (pi : CausalPolicy (filteredModel K actions hne advance gain d hd))
    (n : ℕ) (h : pi.Memory) :
    expectReal (pi.info h).1 (sourceCausalValue K gain d pi n h) ≤
      (expect (pi.info h).1 (sourceValue K gain d
        (solve (filteredModel K actions hne advance gain d hd) n (pi.info h))) : ℝ) := by
  rw [sourceCausalValue_eq_model, returned_source_value]
  exact causalValue_le_solve _ pi n h

/-- The probability weight of a concrete ORIGINAL noise tape. -/
def sourceTapeWeight (K : Source W A O Z) :
    {n : ℕ} → Table A O n → W → Tape Z n → ℚ
  | 0, .halt, _, _ => 1
  | _n + 1, .node a children, w, (z, rest) =>
      K.chance w z * sourceTapeWeight K (children (K.observe w a z)) (K.next w a z) rest

/-- The original noise tape's visible pushforward under THIS table. -/
def observedTape (K : Source W A O Z) :
    {n : ℕ} → Table A O n → W → Tape Z n → Tape O n
  | 0, .halt, _, _ => PUnit.unit
  | _n + 1, .node a children, w, (z, rest) =>
      (K.observe w a z, observedTape K (children (K.observe w a z)) (K.next w a z) rest)

theorem sourceTrace_eq_noiseExpectation (K : Source W A O Z) :
    ∀ (n : ℕ) (p : Table A O n) (w : W) (test : Tape O n → ℚ),
      sourceTraceExpectation K p test w =
        ∑ noise : Tape Z n, sourceTapeWeight K p w noise * test (observedTape K p w noise) := by
  intro n
  induction n with
  | zero =>
      intro p w test
      cases p
      simp [sourceTraceExpectation, sourceTapeWeight, observedTape, Tape]
  | succ n ih =>
      intro p w test
      cases p with
      | node a children =>
          change (∑ z, K.chance w z * sourceTraceExpectation K (children (K.observe w a z))
            (fun rest => test (K.observe w a z, rest)) (K.next w a z)) = _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro z hz
          rw [ih]
          simp only [sourceTapeWeight, observedTape, Finset.mul_sum, mul_assoc]

/-- A positive actual primitive branch has a positive mass receipt and an
actual positive posterior atom. This is a world-side proof, not a new sensor. -/
theorem actual_branch_in_posterior (K : Source W A O Z) (b : Belief W) (a : A)
    (x : b.Atom) (z : Z) (hx : 0 < b.weight x) (hz : 0 < K.chance (b.state x) z) :
    0 < mass K b a (K.observe (b.state x) a z) ∧
      ∃ y : (posterior K b a (K.observe (b.state x) a z)).Atom,
        (posterior K b a (K.observe (b.state x) a z)).state y = K.next (b.state x) a z ∧
        0 < (posterior K b a (K.observe (b.state x) a z)).weight y := by
  let o := K.observe (b.state x) a z
  have hj : 0 < joint K b a o (x, z) := by simpa [joint, o] using mul_pos hx hz
  have hm : 0 < mass K b a o :=
    hj.trans_le (Finset.single_le_sum (fun y _ => joint_nonneg K b a o y) (Finset.mem_univ (x, z)))
  refine ⟨hm, ?_⟩
  change ∃ y : (posterior K b a o).Atom,
    (posterior K b a o).state y = K.next (b.state x) a z ∧ 0 < (posterior K b a o).weight y
  rw [posterior, dif_neg (ne_of_gt hm)]
  exact ⟨(x, z), rfl, div_pos hj hm⟩

/-- A genuinely supported initial atom/noise path has positive probability
under the observed table interpreter. Thus prefix payment proved for that
interpreter applies to EVERY supported actual source path. -/
theorem observedTape_supported (K : Source W A O Z)
    (actions : Belief W × M → List A) (hne : ∀ i, actions i ≠ [])
    (advance : M → A → O → M) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d) :
    ∀ (n : ℕ) (p : Table A O n) (b : Belief W) (m : M) (x : b.Atom) (noise : Tape Z n),
      0 < b.weight x → 0 < sourceTapeWeight K p (b.state x) noise →
      0 < tapeWeight (filteredModel K actions hne advance gain d hd) (b, m) p
        (observedTape K p (b.state x) noise) := by
  intro n
  induction n with
  | zero => intro p b m x noise hx hw; cases p; exact zero_lt_one
  | succ n ih =>
      intro p b m x noise hx hw
      cases p with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          have hpositive : 0 < K.chance (b.state x) z ∧
              0 < sourceTapeWeight K (children (K.observe (b.state x) a z))
                (K.next (b.state x) a z) rest := by
            rcases mul_pos_iff.mp hw with h | h
            · exact h
            · exact ((not_lt_of_ge (K.nonneg (b.state x) z)) h.1).elim
          obtain ⟨hm, y, hy, hyp⟩ := actual_branch_in_posterior K b a x z hx hpositive.1
          have hrest : 0 < sourceTapeWeight K (children (K.observe (b.state x) a z))
              ((posterior K b a (K.observe (b.state x) a z)).state y) rest := by
            rw [hy]
            exact hpositive.2
          have ht := ih (children (K.observe (b.state x) a z))
            (posterior K b a (K.observe (b.state x) a z))
            (advance m a (K.observe (b.state x) a z)) y rest hyp hrest
          rw [hy] at ht
          exact mul_pos hm ht

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFilteredModel
