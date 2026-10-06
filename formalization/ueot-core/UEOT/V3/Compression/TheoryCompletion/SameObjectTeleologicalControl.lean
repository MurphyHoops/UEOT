import UEOT.V3.Compression.TheoryCompletion.SameObjectEffectiveState
import UEOT.V3.Compression.TheoryCompletion.TeleologicalGauge
import UEOT.V3.Compression.AgencyGodGoaAssembly

/-!
# P2.3 preflight — same-parent teleological control realization

A P1 teleological contract does not itself supply a scalar reward on state-action
pairs. The bridge is explicit: each state-action choice is interpreted as one
admissible future, and a numerical objective is required to represent the
declared contract. The control transition law is taken from the same parent
token that owns the process history.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Function
open UEOT.V3.Compression.AgencyGodGoaAssembly

universe uP uX uA uF

/-- Explicit contract-to-control realization for one parent token.

This is an adapter/interface, not a theorem that Objecthood alone determines
purpose or a reward representation. -/
structure ParentTeleologicalControlRealization
    (Parent : Type uP) (X : Type uX) (A : Type uA)
    (Future : Type uF) where
  parent : Parent
  contract : TeleologicalContract Future
  actionFuture :
    X → A → AdmissibleFuture contract.admissible
  objective :
    NumericalObjective (AdmissibleFuture contract.admissible)
  objective_represents :
    ObjectiveRepresentsContract contract objective
  rewardBound : ℝ
  reward_abs_le :
    ∀ x a, |objective (actionFuture x a)| ≤ rewardBound
  discount : ℝ
  discount_pos : 0 < discount
  discount_lt_one : discount < 1

namespace ParentTeleologicalControlRealization

variable
    {Parent : Type uP} {X : Type uX} {A : Type uA}
    {Future : Type uF}

/-- The induced reward order is exactly the declared contract order after the
explicit state-action-to-admissible-future interpretation. -/
theorem inducedRewardOrder_iff_contractPreference
    (R : ParentTeleologicalControlRealization Parent X A Future)
    (x : X) (a : A) (y : X) (b : A) :
    InducedPreference R.objective (R.actionFuture x a) (R.actionFuture y b) ↔
      R.contract.prefers (R.actionFuture x a) (R.actionFuture y b) :=
  R.objective_represents _ _

/-- P2.3 adapter. The history-level transition comes from exactly the selected
parent dynamics; the reward is not supplied independently but is the
contract-valid objective evaluated on the declared action future.

Sufficiency through OwnHistory.current follows because both reward and
transition depend on history only through that same current state. -/
noncomputable def toHistoryControlSpec
    [Fintype X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future) :
    HistoryControlSpec
      (OwnHistory R.parent X A) X A
      (OwnHistory.current :
        OwnHistory R.parent X A → X) := by
  classical
  refine
    { transition := fun h a y =>
        ((dynamics R.parent h.current a) y).toReal
      reward := fun h a =>
        R.objective (R.actionFuture h.current a)
      rewardBound := R.rewardBound
      discount := R.discount
      transition_nonneg := ?_
      transition_sum_one := ?_
      reward_abs_le := ?_
      discount_pos := R.discount_pos
      discount_lt_one := R.discount_lt_one
      sufficient := ?_ }
  · intro h a y
    exact ENNReal.toReal_nonneg
  · intro h a
    have hsum :=
      congrArg ENNReal.toReal
        (PMF.tsum_coe (dynamics R.parent h.current a))
    rw [tsum_fintype,
      ENNReal.toReal_sum
        (fun y _ =>
          PMF.apply_ne_top (dynamics R.parent h.current a) y)] at hsum
    simpa using hsum
  · intro h a
    exact R.reward_abs_le h.current a
  · intro h h' hcurrent a
    simp only
    rw [hcurrent]

/-- The transition component of the induced history control model is literally
the same parent's PMF dynamics, converted to finite real probabilities. -/
@[simp] theorem toHistoryControlSpec_transition
    [Fintype X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future)
    (h : OwnHistory R.parent X A) (a : A) (y : X) :
    (R.toHistoryControlSpec dynamics).transition h a y =
      ((dynamics R.parent h.current a) y).toReal :=
  rfl

/-- The reward component is exactly the chosen numerical representation of the
same declared teleological contract. -/
@[simp] theorem toHistoryControlSpec_reward
    [Fintype X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future)
    (h : OwnHistory R.parent X A) (a : A) :
    (R.toHistoryControlSpec dynamics).reward h a =
      R.objective (R.actionFuture h.current a) :=
  rfl

end ParentTeleologicalControlRealization

end UEOT.V3.Compression.TheoryCompletion
