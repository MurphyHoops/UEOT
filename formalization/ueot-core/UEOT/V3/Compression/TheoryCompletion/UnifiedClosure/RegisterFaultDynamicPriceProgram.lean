import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPrice

/-!
Original promise: the all-price dynamic verdict must belong to the actual submitted/returned program, parent and complete birth/fee path law.
Existing source: dynamic Bellman classification and original actualValue/recordPathLaw, semantic synthesize, all-fine-causal and original P9/GOD interfaces.
Reduced premise: derive all-price optimal-row projection, actual GOD transport and the literal returned program's native infinite-record integral; no separate desired ranking or policy witness.
Family/boundary: SAME original fixed-port fault model and evaluation; parameter-indexed exact case distinction is not a new finite-data algorithm or access to unknown parameters by the old probe selector.
Consumer: original PreservesGOD/transport_object_property and actual_god_value on SAME retained Organism/history, with exact synthesis result and all failures/fees retained.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPriceProgram
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open RegisterInstructionPurposeScale RegisterFaultDynamicPrice
noncomputable section

section Source
variable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
variable (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)

theorem actual_optimal_value_projection (x : State n) :
    (model i noise m price epsilon he d hd).optimalValue x=
      (model (0 : Fin 1) noise m price epsilon he d hd).optimalValue (projectState i x) := by
  rw [←dynamic_value_eq_optimal i noise m price epsilon he d hd,
    ←dynamic_value_eq_optimal 0 noise m price epsilon he d hd]
  simp only [dynamicValue]
  split_ifs <;> rfl

theorem actual_optimal_q_projection (x : State n) (a : Action) :
    (model i noise m price epsilon he d hd).qValue
      (model i noise m price epsilon he d hd).optimalValue x a=
    (model (0 : Fin 1) noise m price epsilon he d hd).qValue
      (model (0 : Fin 1) noise m price epsilon he d hd).optimalValue (projectState i x) a := by
  rw [←dynamic_value_eq_optimal i noise m price epsilon he d hd,
    ←dynamic_value_eq_optimal 0 noise m price epsilon he d hd,qValue_source,qValue_source]
  simp only [dynamicValue]
  by_cases hc : RepairRegion m price epsilon d
  · simp only [if_pos hc,value,active_update,projectState_apply,Function.update_apply]
  · simp only [if_neg hc,idleValue,active_update,projectState_apply,Function.update_apply]

theorem actual_all_price_god_action (x : State n) (a : Action) :
    a∈BellmanGODCorrespondence (model i noise m price epsilon he d hd) x ↔
      a∈BellmanGODCorrespondence (model (0 : Fin 1) noise m price epsilon he d hd) (projectState i x) := by
  simp only [mem_bellmanGODCorrespondence_iff,
    actual_optimal_q_projection i noise m price epsilon he d hd,
    actual_optimal_value_projection i noise m price epsilon he d hd]

theorem actual_all_price_god_selector (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) :
    IsBellmanGODSelector (model i noise m price epsilon he d hd) (interpret p) ↔
      IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret q) := by
  constructor
  · intro h y
    have hh:=(actual_all_price_god_action i noise m price epsilon he d hd
      (representative i y) (interpret p (representative i y))).mp (h _)
    have ha : interpret q y=interpret p (representative i y) := by
      simpa using (synthesize_actual i p q hs).2 (representative i y)
    have hy : projectState i (representative i y)=y := by
      ext j
      have hj : j=(0 : Fin 1):=Subsingleton.elim _ _
      subst j
      simp [projectState,representative]
    rw [hy,←ha] at hh
    exact hh
  · intro h x
    have hh:=h (projectState i x)
    rw [(synthesize_actual i p q hs).2] at hh
    exact (actual_all_price_god_action i noise m price epsilon he d hd x (interpret p x)).mpr hh

/-- Original P9/GOD, with the previous price<=1 source restriction removed
by the actual Bellman derivation, not by weakening the GOD predicate. -/
theorem actual_all_price_preserves_god :
    PreservesGOD (RegisterInstructionGODScale.godScale i)
      (fun obj=>IsBellmanGODSelector (model i noise m price epsilon he d hd) (interpret obj.2.val.1))
      (fun obj=>IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret obj.2)) := by
  intro obj h
  exact (actual_all_price_god_selector i noise m price epsilon he d hd _ _ obj.2.property).mp h
end Source

/-- The original finite semantic checker returns THIS actual coarse AST for
both branches. No new coarse program is selected from an existence theorem. -/
theorem dynamic_synthesis {n : ℕ} (i : Fin n) (m : Mechanism)
    (price epsilon : NNReal) (d : ℝ) :
    synthesize i (dynamicProgram i m price epsilon d)=
      some (returnedProgram i (dynamicProgram i m price epsilon d)) := by
  unfold dynamicProgram
  split_ifs
  · exact compiled_synthesis i m.goal
  · simp [synthesize,finiteCheck,interpret]

/-- SAME parent/history and SAME actual returned q: original P9 is called,
then native actual complete-record payoff integrals attain the full fine
causal optimum at EVERY registered nonnegative price. -/
theorem dynamic_actual_program_and_returned_value {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (o : Organism n) (hp : o.program=m.goal) :
    let p:=dynamicProgram i m price epsilon d
    let q:=returnedProgram i p
    synthesize i p=some q ∧
    IsBellmanGODSelector (model i noise m price epsilon he d hd) (interpret p) ∧
    IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret q) ∧
    actualValue i noise m epsilon he price d o p=(model i noise m price epsilon he d hd).optimalValue o.physical ∧
    actualValue (0 : Fin 1) noise m epsilon he price d (projectOrganism i o) q=
      (model i noise m price epsilon he d hd).optimalValue o.physical := by
  let p:=dynamicProgram i m price epsilon d
  let q:=returnedProgram i p
  have hs:=dynamic_synthesis i m price epsilon d
  let pq : Accepted i:=⟨(p,q),hs⟩
  have hf:=dynamic_program_god i noise m price epsilon he d hd
  have hq : IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret q) :=
    transport_object_property (RegisterInstructionGODScale.godScale i)
      (fun obj=>IsBellmanGODSelector (model i noise m price epsilon he d hd) (interpret obj.2.val.1))
      (fun obj=>IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret obj.2))
      (fine:=(o,pq)) (coarse:=((RegisterInstructionGODScale.godScale i).objectMap (o,pq))) rfl
      (actual_all_price_preserves_god i noise m price epsilon he d hd) hf
  have hv:=RegisterInstructionGODScale.actual_god_value i noise m price epsilon he d hd o hp p hf
  exact ⟨hs,hf,hq,hv,(actual_value_transport i noise m epsilon he price d o p q hs).symm.trans hv⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPriceProgram
