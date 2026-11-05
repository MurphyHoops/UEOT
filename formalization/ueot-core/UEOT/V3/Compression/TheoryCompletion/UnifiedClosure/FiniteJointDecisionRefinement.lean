import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSupportedPolicy

/-!
# Supported finite-model transfer for the concrete Register representation

This is a small adapter for the existing finite Bellman theorem, not a new
solver. The Register consumer proves every one-step premise from its primitive,
receipt observer and count posterior. Only positive observation successors need
to be related; impossible branches do not impose an extra physical identity.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionRefinement

open scoped BigOperators
open FiniteJointDecisionSolver FiniteJointDecisionSupportedPolicy

universe uI uJ uA uO
variable {I : Type uI} {J : Type uJ} {A : Type uA} {O : Type uO} [Fintype O]

structure StepRefinement (M : Model I A O) (N : Model J A O) (R : I → J → Prop) where
  actions : ∀ i j, R i j → M.actions i = N.actions j
  prob : ∀ i j, R i j → ∀ a, a ∈ M.actions i → ∀ o, M.prob i a o = N.prob j a o
  reward : ∀ i j, R i j → ∀ a o, M.reward i a o = N.reward j a o
  discount : M.discount = N.discount
  next : ∀ i j, R i j → ∀ a, a ∈ M.actions i → ∀ o,
    0 < M.prob i a o → R (M.next i a o) (N.next j a o)

variable {M : Model I A O} {N : Model J A O} {R : I → J → Prop}

theorem feasible_supported (M : Model I A O) :
    ∀ {H : ℕ} (i : I) (p : Table A O H), Feasible M i p → SupportedFeasible M i p := by
  intro H
  induction H with
  | zero => intro i p hp; cases p; trivial
  | succ H ih =>
      intro i p hp
      cases p with
      | node a children => exact ⟨hp.1, fun o _ => ih _ _ (hp.2 o)⟩

theorem supported_feasible_transfer (T : StepRefinement M N R) :
    ∀ {H : ℕ} (i : I) (j : J), R i j → ∀ p : Table A O H,
      SupportedFeasible N j p → SupportedFeasible M i p := by
  intro H
  induction H with
  | zero => intro i j hij p hp; cases p; trivial
  | succ H ih =>
      intro i j hij p hp
      cases p with
      | node a children =>
          have ha : a ∈ M.actions i := by rw [T.actions i j hij]; exact hp.1
          refine ⟨ha, fun o ho => ?_⟩
          exact ih _ _ (T.next i j hij a ha o ho) _
            (hp.2 o (by rw [← T.prob i j hij a ha o]; exact ho))

theorem value_transfer (T : StepRefinement M N R) :
    ∀ {H : ℕ} (i : I) (j : J), R i j → ∀ p : Table A O H,
      SupportedFeasible N j p → value M i p = value N j p := by
  intro H
  induction H with
  | zero => intro i j hij p hp; cases p; rfl
  | succ H ih =>
      intro i j hij p hp
      cases p with
      | node a children =>
          have ha : a ∈ M.actions i := by rw [T.actions i j hij]; exact hp.1
          simp only [value]
          apply Finset.sum_congr rfl
          intro o _
          have hprob := T.prob i j hij a ha o
          by_cases hz : M.prob i a o = 0
          · simp [hz, ← hprob]
          · have ho : 0 < M.prob i a o := lt_of_le_of_ne (M.prob_nonneg i a ha o) (Ne.symm hz)
            rw [hprob, T.reward i j hij a o, T.discount,
              ih _ _ (T.next i j hij a ha o ho) _
                (hp.2 o (by rw [← hprob]; exact ho))]

/-- Equality of the full permitted receipt-tape law, not merely its mean.
The immediate reward/fee/birth/next-summary tests are supplied by the concrete
source theorem; this transports all finite adaptive receipt continuations. -/
theorem tapeWeight_transfer (T : StepRefinement M N R) :
    ∀ {H : ℕ} (i : I) (j : J), R i j → ∀ p : Table A O H,
      SupportedFeasible N j p → ∀ w : Tape O H,
        tapeWeight M i p w = tapeWeight N j p w := by
  intro H
  induction H with
  | zero => intro i j hij p hp w; cases p; rfl
  | succ H ih =>
      intro i j hij p hp w
      cases p with
      | node a children =>
          rcases w with ⟨o, rest⟩
          have ha : a ∈ M.actions i := by rw [T.actions i j hij]; exact hp.1
          have hprob := T.prob i j hij a ha o
          simp only [tapeWeight]
          by_cases hz : M.prob i a o = 0
          · simp [hz, ← hprob]
          · have ho : 0 < M.prob i a o := lt_of_le_of_ne (M.prob_nonneg i a ha o) (Ne.symm hz)
            rw [hprob, ih _ _ (T.next i j hij a ha o ho) _
              (hp.2 o (by rw [← hprob]; exact ho)) rest]

/-- The original finite Bellman maximum is invariant under the proved
supported one-step representation. Every legal alternative is used here. -/
theorem optimalValue_transfer (T : StepRefinement M N R) :
    ∀ H (i : I) (j : J), R i j → optimalValue M H i = optimalValue N H j := by
  intro H
  induction H with
  | zero => intro i j hij; rfl
  | succ H ih =>
      intro i j hij
      have hq (a : A) (ha : a ∈ M.actions i) :
          qValue M (optimalValue M H) i a = qValue N (optimalValue N H) j a := by
        unfold qValue
        apply Finset.sum_congr rfl
        intro o _
        have hprob := T.prob i j hij a ha o
        by_cases hz : M.prob i a o = 0
        · simp [hz, ← hprob]
        · have ho : 0 < M.prob i a o := lt_of_le_of_ne (M.prob_nonneg i a ha o) (Ne.symm hz)
          rw [hprob, T.reward i j hij a o, T.discount,
            ih _ _ (T.next i j hij a ha o ho)]
      apply le_antisymm
      · rw [optimalValue_succ, hq _ (chosenAction_mem M H i)]
        apply qValue_le_optimalValue
        rw [← T.actions i j hij]
        exact chosenAction_mem M H i
      · have ha : chosenAction N H j ∈ M.actions i := by
          rw [T.actions i j hij]
          exact chosenAction_mem N H j
        rw [optimalValue_succ, ← hq _ ha]
        exact qValue_le_optimalValue M H i _ ha

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionRefinement
