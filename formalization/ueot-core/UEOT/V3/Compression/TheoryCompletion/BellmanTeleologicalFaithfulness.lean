import UEOT.V3.Compression.TheoryCompletion.SameObjectGOD
import UEOT.V3.FiniteDiscountedPolicyResolvent
import UEOT.V3.FiniteDiscountedOccupancyRegret

/-!
# P2.4b preflight — local teleological order does not imply Bellman faithfulness
-/

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.FiniteDiscountedControl

private def localOrdinalReward : Fin 3 → ℝ := ![0, 1, 2]
private def localNonlinearReward : Fin 3 → ℝ := ![0, 1, 4]

theorem localRewards_same_action_order (a b : Fin 3) :
    localOrdinalReward a ≤ localOrdinalReward b ↔
      localNonlinearReward a ≤ localNonlinearReward b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [localOrdinalReward, localNonlinearReward]

private noncomputable def ordinalBellmanModel :
    Model Unit (fun _ : Unit => Fin 3) where
  transition := fun _ _ _ => 1
  reward := fun _ a => localOrdinalReward a
  rewardBound := 2
  discount := 1 / 2
  transition_nonneg := by intro _ _ _; norm_num
  transition_sum_one := by intro _ _; simp
  reward_abs_le := by
    intro _ a
    fin_cases a <;> norm_num [localOrdinalReward]
  discount_pos := by norm_num
  discount_lt_one := by norm_num

private noncomputable def nonlinearBellmanModel :
    Model Unit (fun _ : Unit => Fin 3) where
  transition := fun _ _ _ => 1
  reward := fun _ a => localNonlinearReward a
  rewardBound := 4
  discount := 1 / 2
  transition_nonneg := by intro _ _ _; norm_num
  transition_sum_one := by intro _ _; simp
  reward_abs_le := by
    intro _ a
    fin_cases a <;> norm_num [localNonlinearReward]
  discount_pos := by norm_num
  discount_lt_one := by norm_num

private def middlePolicyProb : Fin 3 → ℝ := ![0, 1, 0]
private noncomputable def endpointPolicyProb : Fin 3 → ℝ := ![(1 / 2 : ℝ), 0, (1 / 2 : ℝ)]

private noncomputable def middlePolicy :
    StationaryPolicy (fun _ : Unit => Fin 3) where
  prob := fun _ => middlePolicyProb
  prob_nonneg := by
    intro _ a
    fin_cases a <;> norm_num [middlePolicyProb]
  prob_sum_one := by
    intro _
    norm_num [middlePolicyProb, Fin.sum_univ_succ]

private noncomputable def endpointPolicy :
    StationaryPolicy (fun _ : Unit => Fin 3) where
  prob := fun _ => endpointPolicyProb
  prob_nonneg := by
    intro _ a
    fin_cases a <;> norm_num [endpointPolicyProb]
  prob_sum_one := by
    intro _
    norm_num [endpointPolicyProb, Fin.sum_univ_succ]

private theorem ordinal_middle_value :
    ordinalBellmanModel.policyValue middlePolicy () = 2 := by
  have hfixed :
      ordinalBellmanModel.policyBellman middlePolicy (fun _ : Unit => (2 : ℝ)) =
        (fun _ : Unit => (2 : ℝ)) := by
    funext x
    cases x
    norm_num [Model.policyBellman, Model.policyReward, Model.policyExpect,
      Model.policyTransition, ordinalBellmanModel, middlePolicy,
      middlePolicyProb, localOrdinalReward, Fin.sum_univ_succ]
  have huniq :=
    ordinalBellmanModel.policyValue_unique middlePolicy hfixed
  exact (congrFun huniq ()).symm

private theorem ordinal_endpoint_value :
    ordinalBellmanModel.policyValue endpointPolicy () = 2 := by
  have hfixed :
      ordinalBellmanModel.policyBellman endpointPolicy (fun _ : Unit => (2 : ℝ)) =
        (fun _ : Unit => (2 : ℝ)) := by
    funext x
    cases x
    norm_num [Model.policyBellman, Model.policyReward, Model.policyExpect,
      Model.policyTransition, ordinalBellmanModel, endpointPolicy,
      endpointPolicyProb, localOrdinalReward, Fin.sum_univ_succ]
  have huniq :=
    ordinalBellmanModel.policyValue_unique endpointPolicy hfixed
  exact (congrFun huniq ()).symm

private theorem nonlinear_middle_value :
    nonlinearBellmanModel.policyValue middlePolicy () = 2 := by
  have hfixed :
      nonlinearBellmanModel.policyBellman middlePolicy (fun _ : Unit => (2 : ℝ)) =
        (fun _ : Unit => (2 : ℝ)) := by
    funext x
    cases x
    norm_num [Model.policyBellman, Model.policyReward, Model.policyExpect,
      Model.policyTransition, nonlinearBellmanModel, middlePolicy,
      middlePolicyProb, localNonlinearReward, Fin.sum_univ_succ]
  have huniq :=
    nonlinearBellmanModel.policyValue_unique middlePolicy hfixed
  exact (congrFun huniq ()).symm

private theorem nonlinear_endpoint_value :
    nonlinearBellmanModel.policyValue endpointPolicy () = 4 := by
  have hfixed :
      nonlinearBellmanModel.policyBellman endpointPolicy (fun _ : Unit => (4 : ℝ)) =
        (fun _ : Unit => (4 : ℝ)) := by
    funext x
    cases x
    norm_num [Model.policyBellman, Model.policyReward, Model.policyExpect,
      Model.policyTransition, nonlinearBellmanModel, endpointPolicy,
      endpointPolicyProb, localNonlinearReward, Fin.sum_univ_succ]
  have huniq :=
    nonlinearBellmanModel.policyValue_unique endpointPolicy hfixed
  exact (congrFun huniq ()).symm

/-- P2 Bellman-faithfulness no-go. Pointwise-equivalent local reward order does
not determine the ordering of long-horizon stationary policy values. Therefore
P2 needs an explicit policy-level dynamic-consistency/faithfulness certificate
before Bellman GOD may be identified with the original teleological contract. -/
theorem local_reward_order_does_not_determine_policy_value_order :
    (∀ a b : Fin 3,
      localOrdinalReward a ≤ localOrdinalReward b ↔
        localNonlinearReward a ≤ localNonlinearReward b) ∧
    ordinalBellmanModel.policyValue middlePolicy () =
      ordinalBellmanModel.policyValue endpointPolicy () ∧
    nonlinearBellmanModel.policyValue middlePolicy () <
      nonlinearBellmanModel.policyValue endpointPolicy () := by
  refine ⟨localRewards_same_action_order, ordinal_middle_value.trans ordinal_endpoint_value.symm, ?_⟩
  rw [nonlinear_middle_value, nonlinear_endpoint_value]
  norm_num

end UEOT.V3.Compression.TheoryCompletion

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.FiniteDiscountedControl

namespace ParentTeleologicalControlRealization

universe uP uX uA uF

variable
    {Parent : Type uP} {X : Type uX} {A : Type uA}
    {Future : Type uF}

/-- Policy-level dynamic-consistency certificate for the local P2.3 realization.

It interprets every stationary randomized policy, from every physical start
state, as an admissible future of the same P1 contract, and requires exact
ordering agreement between infinite discounted policy value and that contract.

This extra certificate is necessary: the local-reward-order boundary above
proves that local reward ordering alone cannot supply it. -/
structure BellmanTeleologicalFaithfulness
    [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future) where
  policyFuture :
    X → StationaryPolicy (fun _ : X => A) →
      AdmissibleFuture R.contract.admissible
  represents_policy_order :
    ∀ x π rho,
      (R.toControlModel dynamics).policyValue π x ≤
          (R.toControlModel dynamics).policyValue rho x ↔
        R.contract.prefers (policyFuture x π) (policyFuture x rho)

/-- Under the explicit Bellman-faithfulness certificate, the canonical greedy
stationary policy is not merely reward-optimal: its interpreted future is
contract-maximal against every stationary randomized policy from the same
physical start state. -/
theorem greedyPolicy_contract_maximal
    [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
    (dynamics : Parent → X → A → PMF X)
    (R : ParentTeleologicalControlRealization Parent X A Future)
    (F : BellmanTeleologicalFaithfulness dynamics R)
    (x : X) (π : StationaryPolicy (fun _ : X => A)) :
    R.contract.prefers
      (F.policyFuture x π)
      (F.policyFuture x
        (StationaryPolicy.ofSelector (R.toControlModel dynamics).greedyAction)) := by
  apply (F.represents_policy_order x π
    (StationaryPolicy.ofSelector (R.toControlModel dynamics).greedyAction)).1
  let M := R.toControlModel dynamics
  have hπ :
      M.policyValue π x ≤ M.optimalValue x := by
    have h :=
      CausalPolicy.infiniteValue_le_optimal
        π.toCausalPolicy M (t := 0) x
    rw [M.stationary_infiniteValue_eq_policyValue π (t := 0) x] at h
    exact h
  have hgreedy :
      M.policyValue (StationaryPolicy.ofSelector M.greedyAction) x =
        M.optimalValue x := by
    exact congrFun M.policyValue_ofSelector_greedy_eq_optimal x
  simpa [M] using hπ.trans_eq hgreedy.symm

end ParentTeleologicalControlRealization

end UEOT.V3.Compression.TheoryCompletion
