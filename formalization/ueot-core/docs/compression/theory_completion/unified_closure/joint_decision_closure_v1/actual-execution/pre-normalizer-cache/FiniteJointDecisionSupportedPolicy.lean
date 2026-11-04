import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFilteredModel

/-!
# All policies feasible on actual supported histories

The computable solver still returns a table legal at every row. A competing
policy need only obey the menu on histories with positive source probability.
This file closes that quantifier explicitly: zero-probability counterfactual
rows are ignored in the proof, rather than silently narrowing the competitor
class to globally legal tables. Real action probabilities and complete allowed
action/observation history are included.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSupportedPolicy

open scoped BigOperators
open FiniteJointDecisionSolver FiniteJointDecisionBelief FiniteJointDecisionFilteredModel

universe uI uA uO uMem uW uPublic

variable {I : Type uI} {A : Type uA} {O : Type uO}
variable [Fintype O] [Fintype A]

/-- The legal deterministic comparison class only constrains actual supported
continuations. Impossible observation rows may contain arbitrary requests. -/
def SupportedFeasible (M : Model I A O) : {H : ℕ} → I → Table A O H → Prop
  | _, _, .halt => True
  | _, i, .node a children =>
      a ∈ M.actions i ∧ ∀ o, 0 < M.prob i a o → SupportedFeasible M (M.next i a o) (children o)

theorem supported_value_le_solve (M : Model I A O) :
    ∀ (H : ℕ) (i : I) (table : Table A O H), SupportedFeasible M i table →
      value M i table ≤ optimalValue M H i := by
  intro H
  induction H with
  | zero => intro i table ht; cases table; exact le_rfl
  | succ H ih =>
      intro i table ht
      cases table with
      | node a children =>
          calc
            value M i (.node a children) ≤ qValue M (optimalValue M H) i a := by
              apply Finset.sum_le_sum
              intro o ho
              by_cases hz : M.prob i a o = 0
              · simp [hz]
              · have hpos : 0 < M.prob i a o := by
                  rcases eq_or_lt_of_le (M.prob_nonneg i a ht.1 o) with heq | hp
                  · exact (hz heq.symm).elim
                  · exact hp
                apply mul_le_mul_of_nonneg_left _ (M.prob_nonneg i a ht.1 o)
                apply add_le_add le_rfl
                exact mul_le_mul_of_nonneg_left (ih _ _ (ht.2 o hpos)) M.discount_nonneg
            _ ≤ optimalValue M (H+1) i := qValue_le_optimalValue M H i a ht.1

/-- A raw causal kernel has no global menu condition. The separate supported
admissibility predicate below imposes that condition precisely where the
actual finite experiment can reach. The kernel never receives hidden world w. -/
structure RawCausalPolicy (M : Model I A O) where
  Memory : Type uMem
  info : Memory → I
  advance : Memory → A → O → Memory
  info_advance : ∀ h a o, info (advance h a o) = M.next (info h) a o
  actionProb : Memory → A → ℝ
  actionProb_nonneg : ∀ h a, 0 ≤ actionProb h a
  actionProb_sum_one : ∀ h, ∑ a, actionProb h a = 1

noncomputable def rawValue (M : Model I A O) (pi : RawCausalPolicy M) :
    ℕ → pi.Memory → ℝ
  | 0, _ => 0
  | H+1, h =>
      ∑ a, pi.actionProb h a * ∑ o, (M.prob (pi.info h) a o : ℝ) *
        ((M.reward (pi.info h) a o : ℝ) + (M.discount : ℝ) * rawValue M pi H (pi.advance h a o))

def SupportedAdmissible (M : Model I A O) (pi : RawCausalPolicy M) : ℕ → pi.Memory → Prop
  | 0, _ => True
  | H+1, h => ∀ a, pi.actionProb h a ≠ 0 →
      a ∈ M.actions (pi.info h) ∧ ∀ o, 0 < M.prob (pi.info h) a o →
        SupportedAdmissible M pi H (pi.advance h a o)

/-- Complete visible action/observation histories are explicitly represented,
so the causal comparison class is not limited to a fixed finite-memory model. -/
def historyInfo (M : Model I A O) (initial : I) (history : List (A × O)) : I :=
  history.foldl (fun i e => M.next i e.1 e.2) initial

theorem historyInfo_append (M : Model I A O) (initial : I) (history : List (A × O)) (a : A) (o : O) :
    historyInfo M initial (history ++ [(a,o)]) = M.next (historyInfo M initial history) a o := by
  simp [historyInfo, List.foldl_append]

def fullHistoryPolicy (M : Model I A O) (initial : I)
    (prob : List (A × O) → A → ℝ) (hn : ∀ h a, 0 ≤ prob h a)
    (ht : ∀ h, ∑ a, prob h a = 1) : RawCausalPolicy M where
  Memory := List (A × O)
  info := historyInfo M initial
  advance := fun h a o => h ++ [(a,o)]
  info_advance := historyInfo_append M initial
  actionProb := prob
  actionProb_nonneg := hn
  actionProb_sum_one := ht

/-- Real randomized policies feasible only on ACTUAL supported prefixes are
dominated by the same computable returned deterministic table. -/
theorem rawValue_le_solve (M : Model I A O) (pi : RawCausalPolicy M) :
    ∀ H (h : pi.Memory), SupportedAdmissible M pi H h →
      rawValue M pi H h ≤ (optimalValue M H (pi.info h) : ℝ) := by
  intro H
  induction H with
  | zero => intro h hh; simp [rawValue, optimalValue_zero]
  | succ H ih =>
      intro h hh
      have haction (a : A) (ha : pi.actionProb h a ≠ 0) :
          (∑ o, (M.prob (pi.info h) a o : ℝ) *
            ((M.reward (pi.info h) a o : ℝ) + (M.discount : ℝ) *
              rawValue M pi H (pi.advance h a o))) ≤
            (optimalValue M (H+1) (pi.info h) : ℝ) := by
        obtain ⟨hlegal, hnext⟩ := hh a ha
        calc
          _ ≤ ∑ o, (M.prob (pi.info h) a o : ℝ) *
              ((M.reward (pi.info h) a o : ℝ) + (M.discount : ℝ) *
                (optimalValue M H (M.next (pi.info h) a o) : ℝ)) := by
            apply Finset.sum_le_sum
            intro o ho
            by_cases hz : M.prob (pi.info h) a o = 0
            · simp [hz]
            · have hpos : 0 < M.prob (pi.info h) a o := by
                rcases eq_or_lt_of_le (M.prob_nonneg (pi.info h) a hlegal o) with heq | hp
                · exact (hz heq.symm).elim
                · exact hp
              apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast M.prob_nonneg (pi.info h) a hlegal o)
              apply add_le_add le_rfl
              apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast M.discount_nonneg)
              simpa only [pi.info_advance] using ih (pi.advance h a o) (hnext o hpos)
          _ = (qValue M (optimalValue M H) (pi.info h) a : ℝ) := by
            simp only [qValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_add]
          _ ≤ (optimalValue M (H+1) (pi.info h) : ℝ) := by
            exact_mod_cast qValue_le_optimalValue M H (pi.info h) a hlegal
      calc
        rawValue M pi (H+1) h ≤ ∑ a, pi.actionProb h a * (optimalValue M (H+1) (pi.info h) : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases hz : pi.actionProb h a = 0
          · simp [hz]
          · exact mul_le_mul_of_nonneg_left (haction a hz) (pi.actionProb_nonneg h a)
        _ = (optimalValue M (H+1) (pi.info h) : ℝ) := by
          rw [← Finset.sum_mul, pi.actionProb_sum_one, one_mul]

variable {W : Type uW} {Z : Type} {Public : Type uPublic}
variable [Fintype Z] [DecidableEq O]

/-- Direct hidden-primitive execution of a raw real randomized causal kernel.
No menu restriction is built into this value; supported admissibility is a
separate hypothesis of the final theorem. -/
noncomputable def rawSourceValue (K : Source W A O Z) (gain : A → O → ℚ) (d : ℚ)
    {N : Model (Belief W × Public) A O} (pi : RawCausalPolicy N) :
    ℕ → pi.Memory → W → ℝ
  | 0, _, _ => 0
  | H+1, h, w =>
      ∑ a, pi.actionProb h a * ∑ z, (K.chance w z : ℝ) *
        ((gain a (K.observe w a z) : ℝ) + (d : ℝ) *
          rawSourceValue K gain d pi H (pi.advance h a (K.observe w a z)) (K.next w a z))

theorem rawSourceValue_eq_model (K : Source W A O Z)
    (actions : Belief W × Public → List A) (hne : ∀ i, actions i ≠ [])
    (advance : Public → A → O → Public) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d)
    (pi : RawCausalPolicy (filteredModel K actions hne advance gain d hd)) :
    ∀ H (h : pi.Memory),
      expectReal (pi.info h).1 (rawSourceValue K gain d pi H h) =
        rawValue (filteredModel K actions hne advance gain d hd) pi H h := by
  intro H
  induction H with
  | zero => intro h; simp [rawSourceValue, rawValue, expectReal_const]
  | succ H ih =>
      intro h
      simp only [rawSourceValue, rawValue]
      rw [expectReal_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [expectReal_mul]
      rw [primitive_expectation_real K (pi.info h).1 a
        (fun o w => (gain a o : ℝ) + (d : ℝ) *
          rawSourceValue K gain d pi H (pi.advance h a o) w)]
      apply congrArg (fun t : ℝ => pi.actionProb h a * t)
      apply Finset.sum_congr rfl
      intro o ho
      rw [expectReal_add, expectReal_const, expectReal_mul]
      change (mass K (pi.info h).1 a o : ℝ) * ((gain a o : ℝ) + (d : ℝ) *
        expectReal (posterior K (pi.info h).1 a o) (rawSourceValue K gain d pi H (pi.advance h a o))) =
        (mass K (pi.info h).1 a o : ℝ) * ((gain a o : ℝ) + (d : ℝ) *
          rawValue (filteredModel K actions hne advance gain d hd) pi H (pi.advance h a o))
      apply congrArg (fun t : ℝ => (mass K (pi.info h).1 a o : ℝ) * ((gain a o : ℝ) + (d : ℝ) * t))
      have hb := congrArg Prod.fst (pi.info_advance h a o)
      change (pi.info (pi.advance h a o)).1 = posterior K (pi.info h).1 a o at hb
      rw [← hb]
      exact ih (pi.advance h a o)

/-- Actual-source Bayes optimality against ALL real full-history causal kernels
that obey the same budget/action protocol on positive-probability prefixes.
The returned table remains the original exact computable solve output. -/
theorem supported_actual_causal_le_returned (K : Source W A O Z)
    (actions : Belief W × Public → List A) (hne : ∀ i, actions i ≠ [])
    (advance : Public → A → O → Public) (gain : A → O → ℚ) (d : ℚ) (hd : 0 ≤ d)
    (pi : RawCausalPolicy (filteredModel K actions hne advance gain d hd))
    (H : ℕ) (h : pi.Memory)
    (hh : SupportedAdmissible (filteredModel K actions hne advance gain d hd) pi H h) :
    expectReal (pi.info h).1 (rawSourceValue K gain d pi H h) ≤
      (expect (pi.info h).1 (sourceValue K gain d
        (solve (filteredModel K actions hne advance gain d hd) H (pi.info h))) : ℝ) := by
  rw [rawSourceValue_eq_model, returned_source_value]
  exact rawValue_le_solve _ pi H h hh

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSupportedPolicy
