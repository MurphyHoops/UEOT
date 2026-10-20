import UEOTQM.ActionRecordBudget

/-!
# Exact rational controls for causal action-record budgets

Every instrument is a complete Kraus family on a qubit memory. The biased
record uses four rational amplitudes 1/2, three tagged 0 and one tagged 1.
No floating-point square root or empirical data enter this witness.
-/

namespace UEOTQM.ActionRecordBudgetExamples

open Matrix ActionRecordBudget HistoryChannels
open scoped BigOperators ComplexOrder

noncomputable section

abbrev Qubit := Fin 2
abbrev Label := Fin 2

def certain (tag : Label) : Instrument Qubit Label (Fin 4) where
  kraus o k := if o = tag then if k = 0 then 1 else 0 else 0
  complete := by
    fin_cases tag <;> simp [Fin.sum_univ_succ]

theorem certain_branch (tag o : Label) (X : Operator Qubit) :
    (certain tag).branch o X = if o = tag then X else 0 := by
  by_cases ho : o = tag <;>
    simp [Instrument.branch, krausMap, certain, ho, Fin.sum_univ_succ]

theorem certain_probability (tag o : Label) (ρ : Density Qubit) :
    (certain tag).probability ρ o = if o = tag then 1 else 0 := by
  by_cases ho : o = tag <;>
    simp [Instrument.probability, certain_branch, ho, mass, ρ.trace_one]

def halfK : Operator Qubit := (1 / 2 : ℂ) • (1 : Operator Qubit)

theorem halfK_gram : halfKᴴ * halfK = (1 / 4 : ℝ) • (1 : Operator Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfK, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two, Complex.real_smul]

theorem halfK_conjugation (X : Operator Qubit) :
    halfK * X * halfKᴴ = (1 / 4 : ℝ) • X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfK, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two, Complex.real_smul] <;> ring

/-- Four actual rational Kraus matrices: three report zero, one reports one. -/
def biasedKraus (o : Label) : Fin 4 → Operator Qubit :=
  if o = 0 then ![halfK, halfK, halfK, 0] else ![0, 0, 0, halfK]

def biased : Instrument Qubit Label (Fin 4) where
  kraus := biasedKraus
  complete := by
    norm_num [biasedKraus, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, halfK_gram]
    module

theorem biased_branch (o : Label) (X : Operator Qubit) :
    biased.branch o X = (if o = 0 then (3 / 4 : ℝ) else 1 / 4) • X := by
  fin_cases o <;>
    norm_num [Instrument.branch, krausMap, biased, biasedKraus, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, halfK_conjugation] <;> module

theorem biased_probability (o : Label) (ρ : Density Qubit) :
    biased.probability ρ o = if o = 0 then 3 / 4 else 1 / 4 := by
  by_cases ho : o = 0 <;> simp [Instrument.probability, biased_branch, ho, mass_smul, ρ.mass_one]

def rhoZero : Density Qubit where
  matrix := Matrix.diagonal (fun i => if i = 0 then (1 : ℂ) else 0)
  positive := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> norm_num
  trace_one := by simp [Matrix.trace, Fin.sum_univ_two]


theorem joint_probability_certain (E : Effect (Label × Qubit)) (tag : Label)
    (ρ : Density Qubit) :
    E.probability (ClassicalQuantumMemory.state (certain tag) ρ) =
      (HistoryChannels.restrictEffect E tag).probability ρ := by
  change pairing E.matrix (ClassicalQuantumMemory.state (certain tag) ρ).matrix = _
  rw [ClassicalQuantumMemory.state_matrix, HistoryChannels.pairing_block]
  fin_cases tag <;>
    simp [certain_branch, Fin.sum_univ_two, Effect.probability, HistoryChannels.restrictEffect,
      pairing, mass]

theorem joint_probability_biased (E : Effect (Label × Qubit)) (ρ : Density Qubit) :
    E.probability (ClassicalQuantumMemory.state biased ρ) =
      (3 / 4 : ℝ) * (HistoryChannels.restrictEffect E 0).probability ρ +
      (1 / 4 : ℝ) * (HistoryChannels.restrictEffect E 1).probability ρ := by
  change pairing E.matrix (ClassicalQuantumMemory.state biased ρ).matrix = _
  rw [ClassicalQuantumMemory.state_matrix, HistoryChannels.pairing_block]
  simp [biased_branch, Fin.sum_univ_two, pairing_smul_right, Effect.probability,
    HistoryChannels.restrictEffect]

/-- The upper bound quantifies over all legal joint effects and every input density. -/
theorem biased_joint_distance_le_quarter (ρ : Density Qubit) :
    effectDistance (ClassicalQuantumMemory.state (certain 0) ρ)
      (ClassicalQuantumMemory.state biased ρ) ≤ 1 / 4 := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  rw [joint_probability_certain, joint_probability_biased]
  have h0 := (HistoryChannels.restrictEffect E 0).probability_nonneg ρ
  have h1 := (HistoryChannels.restrictEffect E 1).probability_nonneg ρ
  have h0' := (HistoryChannels.restrictEffect E 0).probability_le_one ρ
  have h1' := (HistoryChannels.restrictEffect E 1).probability_le_one ρ
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem biased_joint_distance_exact (ρ : Density Qubit) :
    effectDistance (ClassicalQuantumMemory.state (certain 0) ρ)
      (ClassicalQuantumMemory.state biased ρ) = 1 / 4 := by
  apply le_antisymm (biased_joint_distance_le_quarter ρ)
  have h := (ClassicalQuantumMemory.eventEffect Qubit ({0} : Finset Label)).probability_sub_le_effectDistance
    (ClassicalQuantumMemory.state (certain 0) ρ) (ClassicalQuantumMemory.state biased ρ)
  norm_num [ClassicalQuantumMemory.event_probability, RecordProbability.eventProbability,
    ClassicalQuantumMemory.weights, certain_probability, biased_probability] at h
  exact h

/-- The exact action defect is a supremum theorem, not one tested input. -/
theorem biased_record_defect_exact : ClassicalQuantumMemory.defect (certain 0) biased = 1 / 4 := by
  apply le_antisymm
  · apply csSup_le (Set.insert_nonempty 0 _)
    rintro x (rfl | ⟨ρ, rfl⟩)
    · norm_num
    · exact biased_joint_distance_le_quarter ρ
  · have h := (ClassicalQuantumMemory.channel (certain 0)).state_distance_le_defect
      (ClassicalQuantumMemory.channel biased) rhoZero
    change effectDistance (ClassicalQuantumMemory.state (certain 0) rhoZero)
      (ClassicalQuantumMemory.state biased rhoZero) ≤ ClassicalQuantumMemory.defect (certain 0) biased at h
    rw [biased_joint_distance_exact] at h
    exact h

/-- At time zero choose the initial action; at time one report the observed first label. -/
def feedback : Controller (Option Label) Label 2 :=
  fun t h => if ht : t.val = 0 then none else some (h ⟨0, Nat.pos_of_ne_zero ht⟩)

def exactActions : Option Label → Instrument Qubit Label (Fin 4)
  | none => certain 0
  | some o => certain o

def approximateActions : Option Label → Instrument Qubit Label (Fin 4)
  | none => biased
  | some o => certain o

theorem feedback_word (h : History Label 2) :
    feedback.word h = [(none, h 0), (some (h 0), h 1)] := rfl

def budget : Fin 2 → ℝ := ![1 / 4, 0]

theorem budget_nonneg (t : Fin 2) : 0 ≤ budget t := by
  fin_cases t <;> norm_num [budget]

/-- Only the first action differs; both use exactly the same causal feedback rule. -/
theorem action_defects_bounded (t : Fin 2) (h : History Label t.val) :
    ClassicalQuantumMemory.defect (exactActions (feedback t h))
      (approximateActions (feedback t h)) ≤ budget t := by
  fin_cases t
  · simp [feedback, exactActions, approximateActions, budget, biased_record_defect_exact]
  · simp [feedback, exactActions, approximateActions, budget, record_defect_self]

theorem first_actionCost_exact (ρ : Density Qubit) :
    actionCost exactActions approximateActions feedback ρ 0 = 1 / 4 := by
  simp only [actionCost, feedback, Fin.val_zero, dite_true, exactActions,
    approximateActions, biased_record_defect_exact]
  rw [← Finset.sum_mul, HistoryChannels.sum_weight, one_mul]

theorem second_actionCost_exact (ρ : Density Qubit) :
    actionCost exactActions approximateActions feedback ρ 1 = 0 := by
  simp [actionCost, feedback, exactActions, approximateActions, record_defect_self]

theorem actionCost_sum_exact (ρ : Density Qubit) :
    (∑ t : Fin 2, actionCost exactActions approximateActions feedback ρ t) = 1 / 4 := by
  simp [Fin.sum_univ_two, first_actionCost_exact, second_actionCost_exact]

theorem two_step_budget_bound (ρ σ : Density Qubit) :
    effectDistance (run exactActions feedback ρ) (run approximateActions feedback σ) ≤
      effectDistance ρ σ + 1 / 4 := by
  simpa only [actionCost_sum_exact] using
    run_distance_le_actionCost_sum exactActions approximateActions feedback ρ σ

def zeroHistory : History Label 2 := ![0, 0]

theorem exact_zero_history_probability (ρ : Density Qubit) :
    HistoryChannels.weight (run exactActions feedback ρ) zeroHistory = 1 := by
  simp [weight_run, feedback_word, zeroHistory, response, recordOperator, exactActions,
    certain_branch, mass, ρ.trace_one]

theorem approximate_zero_history_probability (ρ : Density Qubit) :
    HistoryChannels.weight (run approximateActions feedback ρ) zeroHistory = 3 / 4 := by
  simp [weight_run, feedback_word, zeroHistory, response, recordOperator, approximateActions,
    biased_branch, certain_branch, mass_smul, ρ.mass_one]

/-- The full two-step history law saturates the derived sum 1/4+0. -/
theorem two_step_record_tv_exact (ρ : Density Qubit) :
    Mixture.tv (HistoryChannels.weights (run exactActions feedback ρ))
      (HistoryChannels.weights (run approximateActions feedback ρ)) = 1 / 4 := by
  apply le_antisymm
  · simpa only [effectDistance_self, zero_add, actionCost_sum_exact] using
      record_tv_le_actionCost_sum exactActions approximateActions feedback ρ ρ
  · have h := RecordProbability.eventProbability_abs_sub_le_tv
      (HistoryChannels.weights (run exactActions feedback ρ))
      (HistoryChannels.weights (run approximateActions feedback ρ)) {zeroHistory}
    simp only [RecordProbability.eventProbability, Finset.sum_singleton, HistoryChannels.weights_weight] at h
    rw [exact_zero_history_probability, approximate_zero_history_probability] at h
    norm_num at h
    exact h


/-- A concrete enumeration of the four full two-step histories. -/
def historyPairEquiv : (Label × Label) ≃ History Label 2 where
  toFun p := ![p.1, p.2]
  invFun h := (h 0, h 1)
  left_inv := by rintro ⟨o, p⟩; rfl
  right_inv := by intro h; funext t; fin_cases t <;> rfl

theorem exact_terminal_memory (ρ : Density Qubit) :
    (RectangularChannel.discardLeft Qubit (History Label 2)).state
      (run exactActions feedback ρ) = ρ := by
  apply Density.ext
  ext i j
  change (RectangularChannel.discardLeft Qubit (History Label 2)).operator
    (run exactActions feedback ρ).matrix i j = _
  rw [RectangularChannel.discardLeft_operator_apply, run_matrix]
  simp only [ClassicalQuantumMemory.block_apply_same]
  rw [← Equiv.sum_comp historyPairEquiv]
  simp [historyPairEquiv, Fintype.sum_prod_type, Fin.sum_univ_two, feedback_word,
    recordOperator, exactActions, certain_branch]

theorem approximate_terminal_memory (ρ : Density Qubit) :
    (RectangularChannel.discardLeft Qubit (History Label 2)).state
      (run approximateActions feedback ρ) = ρ := by
  apply Density.ext
  ext i j
  change (RectangularChannel.discardLeft Qubit (History Label 2)).operator
    (run approximateActions feedback ρ).matrix i j = _
  rw [RectangularChannel.discardLeft_operator_apply, run_matrix]
  simp only [ClassicalQuantumMemory.block_apply_same]
  rw [← Equiv.sum_comp historyPairEquiv]
  norm_num [historyPairEquiv, Fintype.sum_prod_type, Fin.sum_univ_two, feedback_word,
    recordOperator, approximateActions, biased_branch, certain_branch, Complex.real_smul]
  ring

/-- The negative control changes the first record to one, keeping the same subsequent controller. -/
def flippedActions : Option Label → Instrument Qubit Label (Fin 4)
  | none => certain 1
  | some o => certain o

theorem certain_unlabelled_channel (tag : Label) (X : Operator Qubit) :
    (certain tag).channel X = X := by
  simp [Instrument.channel, certain_branch]

theorem certain_unlabelled_state (tag : Label) (ρ : Density Qubit) :
    (certain tag).channelState ρ = ρ := by
  apply Density.ext
  exact certain_unlabelled_channel tag ρ.matrix

/-- Every unlabelled action channel is identical, on every matrix input. -/
theorem negative_actions_unlabelled_same (a : Option Label) (X : Operator Qubit) :
    (exactActions a).channel X = (flippedActions a).channel X := by
  cases a <;> simp [exactActions, flippedActions, certain_unlabelled_channel]

theorem negative_unlabelled_defect_zero (a : Option Label) :
    channelDefect (exactActions a).channelState (flippedActions a).channelState = 0 := by
  have h : (exactActions a).channelState = (flippedActions a).channelState := by
    funext ρ
    apply Density.ext
    exact negative_actions_unlabelled_same a ρ.matrix
  rw [h, channelDefect_self]

def oneHistory : History Label 2 := ![1, 1]

theorem flipped_zero_history_probability (ρ : Density Qubit) :
    HistoryChannels.weight (run flippedActions feedback ρ) zeroHistory = 0 := by
  simp [weight_run, feedback_word, zeroHistory, response, recordOperator, flippedActions,
    certain_branch, mass]

theorem flipped_one_history_probability (ρ : Density Qubit) :
    HistoryChannels.weight (run flippedActions feedback ρ) oneHistory = 1 := by
  simp [weight_run, feedback_word, oneHistory, response, recordOperator, flippedActions,
    certain_branch, mass, ρ.trace_one]

/-- Deleting labels hides a maximal difference of the actual complete record laws. -/
theorem negative_two_step_record_tv (ρ : Density Qubit) :
    Mixture.tv (HistoryChannels.weights (run exactActions feedback ρ))
      (HistoryChannels.weights (run flippedActions feedback ρ)) = 1 := by
  apply le_antisymm (Mixture.tv_le_one _ _)
  have h := RecordProbability.eventProbability_abs_sub_le_tv
    (HistoryChannels.weights (run exactActions feedback ρ))
    (HistoryChannels.weights (run flippedActions feedback ρ)) {zeroHistory}
  simp only [RecordProbability.eventProbability, Finset.sum_singleton, HistoryChannels.weights_weight] at h
  rw [exact_zero_history_probability, flipped_zero_history_probability] at h
  norm_num at h
  exact h

theorem flipped_terminal_memory (ρ : Density Qubit) :
    (RectangularChannel.discardLeft Qubit (History Label 2)).state
      (run flippedActions feedback ρ) = ρ := by
  apply Density.ext
  ext i j
  change (RectangularChannel.discardLeft Qubit (History Label 2)).operator
    (run flippedActions feedback ρ).matrix i j = _
  rw [RectangularChannel.discardLeft_operator_apply, run_matrix]
  simp only [ClassicalQuantumMemory.block_apply_same]
  rw [← Equiv.sum_comp historyPairEquiv]
  simp [historyPairEquiv, Fintype.sum_prod_type, Fin.sum_univ_two, feedback_word,
    recordOperator, flippedActions, certain_branch]

/-- The feedback separates records while preserving exactly the same quantum memory. -/
theorem negative_terminal_memories_equal (ρ : Density Qubit) :
    (RectangularChannel.discardLeft Qubit (History Label 2)).state (run exactActions feedback ρ) =
      (RectangularChannel.discardLeft Qubit (History Label 2)).state (run flippedActions feedback ρ) := by
  rw [exact_terminal_memory, flipped_terminal_memory]

def secondZeroEvent : Finset (History Label 2) := Finset.univ.filter (fun h => h 1 = 0)

theorem exact_second_record_zero (ρ : Density Qubit) :
    RecordProbability.eventProbability (HistoryChannels.weights (run exactActions feedback ρ))
      secondZeroEvent = 1 := by
  simp only [RecordProbability.eventProbability, secondZeroEvent, Finset.sum_filter]
  rw [← Equiv.sum_comp historyPairEquiv]
  simp [historyPairEquiv, Fintype.sum_prod_type, Fin.sum_univ_two, HistoryChannels.weights_weight,
    weight_run, feedback_word, response, recordOperator, exactActions, certain_branch, mass, ρ.trace_one]

theorem flipped_second_record_zero (ρ : Density Qubit) :
    RecordProbability.eventProbability (HistoryChannels.weights (run flippedActions feedback ρ))
      secondZeroEvent = 0 := by
  simp only [RecordProbability.eventProbability, secondZeroEvent, Finset.sum_filter]
  rw [← Equiv.sum_comp historyPairEquiv]
  simp [historyPairEquiv, Fintype.sum_prod_type, Fin.sum_univ_two, HistoryChannels.weights_weight,
    weight_run, feedback_word, response, recordOperator, flippedActions, certain_branch, mass, ρ.trace_one]

/-- The original complete adaptive tree, not merely the new record representation, has the same exact TV. -/
theorem original_protocol_record_tv_exact (ρ : Density Qubit) :
    Mixture.tv (ClassicalQuantumMemory.ProtocolMemory.weights exactActions feedback.protocol ρ)
      (ClassicalQuantumMemory.ProtocolMemory.weights approximateActions feedback.protocol ρ) = 1 / 4 := by
  rw [protocol_record_tv_eq, two_step_record_tv_exact]

theorem original_protocol_negative_tv (ρ : Density Qubit) :
    Mixture.tv (ClassicalQuantumMemory.ProtocolMemory.weights exactActions feedback.protocol ρ)
      (ClassicalQuantumMemory.ProtocolMemory.weights flippedActions feedback.protocol ρ) = 1 := by
  rw [protocol_record_tv_eq, negative_two_step_record_tv]

end

end UEOTQM.ActionRecordBudgetExamples

#print axioms UEOTQM.ActionRecordBudgetExamples.Qubit
#print axioms UEOTQM.ActionRecordBudgetExamples.Label
#print axioms UEOTQM.ActionRecordBudgetExamples.certain
#print axioms UEOTQM.ActionRecordBudgetExamples.certain_branch
#print axioms UEOTQM.ActionRecordBudgetExamples.certain_probability
#print axioms UEOTQM.ActionRecordBudgetExamples.halfK
#print axioms UEOTQM.ActionRecordBudgetExamples.halfK_gram
#print axioms UEOTQM.ActionRecordBudgetExamples.halfK_conjugation
#print axioms UEOTQM.ActionRecordBudgetExamples.biasedKraus
#print axioms UEOTQM.ActionRecordBudgetExamples.biased
#print axioms UEOTQM.ActionRecordBudgetExamples.biased_branch
#print axioms UEOTQM.ActionRecordBudgetExamples.biased_probability
#print axioms UEOTQM.ActionRecordBudgetExamples.rhoZero
#print axioms UEOTQM.ActionRecordBudgetExamples.joint_probability_certain
#print axioms UEOTQM.ActionRecordBudgetExamples.joint_probability_biased
#print axioms UEOTQM.ActionRecordBudgetExamples.biased_joint_distance_le_quarter
#print axioms UEOTQM.ActionRecordBudgetExamples.biased_joint_distance_exact
#print axioms UEOTQM.ActionRecordBudgetExamples.biased_record_defect_exact
#print axioms UEOTQM.ActionRecordBudgetExamples.feedback
#print axioms UEOTQM.ActionRecordBudgetExamples.exactActions
#print axioms UEOTQM.ActionRecordBudgetExamples.approximateActions
#print axioms UEOTQM.ActionRecordBudgetExamples.feedback_word
#print axioms UEOTQM.ActionRecordBudgetExamples.budget
#print axioms UEOTQM.ActionRecordBudgetExamples.budget_nonneg
#print axioms UEOTQM.ActionRecordBudgetExamples.action_defects_bounded
#print axioms UEOTQM.ActionRecordBudgetExamples.first_actionCost_exact
#print axioms UEOTQM.ActionRecordBudgetExamples.second_actionCost_exact
#print axioms UEOTQM.ActionRecordBudgetExamples.actionCost_sum_exact
#print axioms UEOTQM.ActionRecordBudgetExamples.two_step_budget_bound
#print axioms UEOTQM.ActionRecordBudgetExamples.zeroHistory
#print axioms UEOTQM.ActionRecordBudgetExamples.exact_zero_history_probability
#print axioms UEOTQM.ActionRecordBudgetExamples.approximate_zero_history_probability
#print axioms UEOTQM.ActionRecordBudgetExamples.two_step_record_tv_exact
#print axioms UEOTQM.ActionRecordBudgetExamples.historyPairEquiv
#print axioms UEOTQM.ActionRecordBudgetExamples.exact_terminal_memory
#print axioms UEOTQM.ActionRecordBudgetExamples.approximate_terminal_memory
#print axioms UEOTQM.ActionRecordBudgetExamples.flippedActions
#print axioms UEOTQM.ActionRecordBudgetExamples.certain_unlabelled_channel
#print axioms UEOTQM.ActionRecordBudgetExamples.certain_unlabelled_state
#print axioms UEOTQM.ActionRecordBudgetExamples.negative_actions_unlabelled_same
#print axioms UEOTQM.ActionRecordBudgetExamples.negative_unlabelled_defect_zero
#print axioms UEOTQM.ActionRecordBudgetExamples.oneHistory
#print axioms UEOTQM.ActionRecordBudgetExamples.flipped_zero_history_probability
#print axioms UEOTQM.ActionRecordBudgetExamples.flipped_one_history_probability
#print axioms UEOTQM.ActionRecordBudgetExamples.negative_two_step_record_tv
#print axioms UEOTQM.ActionRecordBudgetExamples.flipped_terminal_memory
#print axioms UEOTQM.ActionRecordBudgetExamples.negative_terminal_memories_equal
#print axioms UEOTQM.ActionRecordBudgetExamples.secondZeroEvent
#print axioms UEOTQM.ActionRecordBudgetExamples.exact_second_record_zero
#print axioms UEOTQM.ActionRecordBudgetExamples.flipped_second_record_zero
#print axioms UEOTQM.ActionRecordBudgetExamples.original_protocol_record_tv_exact
#print axioms UEOTQM.ActionRecordBudgetExamples.original_protocol_negative_tv
