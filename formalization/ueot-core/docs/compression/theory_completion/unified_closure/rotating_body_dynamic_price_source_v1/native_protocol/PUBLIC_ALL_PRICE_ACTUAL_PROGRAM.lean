import UEOT
namespace IndependentDynamicPrice
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultDynamicPrice RegisterFaultDynamicPriceProgram RegisterInstructionPurposeScale
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
noncomputable section
local instance {n : ℕ} : MeasurableSpace (RegisterFaultJointRecord.ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (RegisterFaultJointRecord.ModeRecord n):=⟨fun _=>trivial⟩

theorem half_ok : (1/2 : NNReal)≤1 :=by exact_mod_cast (by norm_num : (1/2 : ℝ)≤1)
theorem quarter_ok : (1/4 : NNReal)≤1 :=by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
def low : Mechanism:=⟨false,5⟩
def high : Mechanism:=⟨false,8⟩
def edge : Mechanism:=⟨false,32/5⟩
def bad : Organism 3:=⟨[true,false,true],fun _=>true,false⟩
def good : Organism 3:=⟨[true,false,true],fun j=>if j=2 then false else true,false⟩
def chosen : Instruction 3:=dynamicProgram 2 low (1/4) (1/2) (3/4)
def hidden : Instruction 3:=.test 0 true chosen chosen
def q : Instruction 1:=returnedProgram 2 hidden

theorem hidden_interpret (x : State 3) : interpret hidden x=interpret chosen x :=by simp [hidden,interpret]
theorem hidden_synthesis : synthesize 2 hidden=some q :=by
  have hs:=dynamic_synthesis (2 : Fin 3) low (1/4) (1/2) (3/4)
  have hc:=any_implementation_forces_check (2 : Fin 3) hidden
    (interpret (returnedProgram 2 chosen)) (fun x=>by
      rw [hidden_interpret]
      exact (synthesize_actual 2 chosen _ hs).2 x)
  simp only [synthesize,hc,if_true,q]

theorem low_region : RepairRegion low (1/4) (1/2) (3/4) :=by norm_num [RepairRegion,low,repairChance]
example : chosen=compile (2 : Fin 3) false :=by
  norm_num [chosen,dynamicProgram,RepairRegion,low,repairChance]

theorem low_optimum (noise : PMF Bool) :
    (model (2 : Fin 3) noise low (1/4) (1/2) half_ok (3/4) (by norm_num)).optimalValue bad.physical=7/16 :=by
  rw [←repair_value_eq_optimal 2 noise low (1/4) (1/2) half_ok (3/4) (by norm_num) low_region]
  norm_num [value,goodValue,badValue,repairChance,low,bad]

-- Joint original synthesis/P9/GOD/native whole-record values of THIS hidden
-- submitted AST and THIS returned q, at nonzero noise with pricedcost>1.
theorem common_actual_consumers (noise : PMF Bool) :
    synthesize 2 hidden=some q ∧
    IsBellmanGODSelector (model (2 : Fin 3) noise low (1/4) (1/2) half_ok (3/4) (by norm_num)) (interpret hidden) ∧
    IsBellmanGODSelector (model (0 : Fin 1) noise low (1/4) (1/2) half_ok (3/4) (by norm_num)) (interpret q) ∧
    actualValue 2 noise low (1/2) half_ok (1/4) (3/4) bad hidden=7/16 ∧
    actualValue (0 : Fin 1) noise low (1/2) half_ok (1/4) (3/4) (projectOrganism 2 bad) q=7/16 :=by
  have hf : IsBellmanGODSelector (model (2 : Fin 3) noise low (1/4) (1/2) half_ok (3/4) (by norm_num)) (interpret hidden) :=by
    intro x
    rw [hidden_interpret]
    exact dynamic_program_god 2 noise low (1/4) (1/2) half_ok (3/4) (by norm_num) x
  have hq := (actual_all_price_god_selector 2 noise low (1/4) (1/2) half_ok (3/4) (by norm_num) hidden q hidden_synthesis).mp hf
  have hv := RegisterInstructionGODScale.actual_god_value 2 noise low (1/4) (1/2) half_ok
    (3/4) (by norm_num) bad rfl hidden hf
  have ht := actual_value_transport 2 noise low (1/2) half_ok (1/4) (3/4) bad hidden q hidden_synthesis
  exact ⟨hidden_synthesis,hf,hq,hv.trans (low_optimum noise),ht.symm.trans (hv.trans (low_optimum noise))⟩

example (noise : PMF Bool) :
    Integrable (RegisterFaultInfiniteRecord.streamPayoff (n:=3) (1/4) (3/4))
      (RegisterFaultInfiniteRecord.recordPathLaw (2 : Fin 3) noise low (1/2) half_ok (astPolicy hidden) ⟨0,bad.physical,bad⟩) ∧
    Integrable (RegisterFaultInfiniteRecord.streamPayoff (n:=1) (1/4) (3/4))
      (RegisterFaultInfiniteRecord.recordPathLaw (0 : Fin 1) noise low (1/2) half_ok (astPolicy q)
        ⟨0,(projectOrganism 2 bad).physical,projectOrganism 2 bad⟩) :=
  ⟨actual_value_integrable 2 noise low (1/2) half_ok (1/4) (3/4) (by norm_num) bad hidden,
    actual_value_integrable 0 noise low (1/2) half_ok (1/4) (3/4) (by norm_num) (projectOrganism 2 bad) q⟩

example (noise : PMF Bool) :
    PreservesGOD (RegisterInstructionGODScale.godScale (2 : Fin 3))
      (fun obj=>IsBellmanGODSelector (model 2 noise low (1/4) (1/2) half_ok (3/4) (by norm_num)) (interpret obj.2.val.1))
      (fun obj=>IsBellmanGODSelector (model (0 : Fin 1) noise low (1/4) (1/2) half_ok (3/4) (by norm_num)) (interpret obj.2)) :=
  actual_all_price_preserves_god 2 noise low (1/4) (1/2) half_ok (3/4) (by norm_num)

example (noise : PMF Bool) (pi : CausalPolicy (State 3) (fun _=>Action)) {t : ℕ} (h : pi.Memory t) :
    pi.infiniteValue (model (2 : Fin 3) noise low (1/4) (1/2) half_ok (3/4) (by norm_num)) h≤
      (model (2 : Fin 3) noise low (1/4) (1/2) half_ok (3/4) (by norm_num)).optimalValue (pi.current h) :=
  (dynamic_program_all_causal 2 noise low (1/4) (1/2) half_ok (3/4) (by norm_num)).2 pi h

example : dynamicProgram (2 : Fin 3) high (1/4) (1/2) (3/4)=.emit none :=by
  norm_num [dynamicProgram,RepairRegion,high,repairChance]
example (noise : PMF Bool) :
    (model (2 : Fin 3) noise high (1/4) (1/2) half_ok (3/4) (by norm_num)).optimalValue bad.physical=0 ∧
    (model (2 : Fin 3) noise high (1/4) (1/2) half_ok (3/4) (by norm_num)).optimalValue good.physical=4/5 :=by
  rw [←idle_value_eq_optimal 2 noise high (1/4) (1/2) half_ok (3/4) (by norm_num) (by norm_num [high,repairChance])]
  norm_num [idleValue,idleGoodValue,high,bad,good,repairChance]
example (noise : PMF Bool) :
    ¬IsBellmanGODSelector (model (2 : Fin 3) noise high (1/4) (1/2) half_ok (3/4) (by norm_num)) ((substrate 2).execute false) :=by
  intro hg
  have hh:=(compiled_god_iff 2 noise high (1/4) (1/2) half_ok (3/4) (by norm_num) (by norm_num [repairChance])).mp hg
  norm_num [RepairRegion,high,repairChance] at hh
example (noise : PMF Bool) :
    IsBellmanGODSelector (model (2 : Fin 3) noise edge (1/4) (1/2) half_ok (3/4) (by norm_num)) ((substrate 2).execute false) ∧
    IsBellmanGODSelector (model (2 : Fin 3) noise edge (1/4) (1/2) half_ok (3/4) (by norm_num)) (fun _=>none) :=
  threshold_tie 2 noise edge (1/4) (1/2) half_ok (3/4) (by norm_num) (by norm_num [edge,repairChance])

-- Keep the original expensive one-step-negative/dynamic-positive distinction.
example (noise : PMF Bool) :
    let m : Mechanism:=⟨true,3⟩
    let M:=model (0 : Fin 1) noise m (1/2) (1/4) quarter_ok (1/2) (by norm_num)
    let x : State 1:=fun _=>false
    (selectorPolicy ((substrate 0).execute true)).truncatedValue M 1 (t:=0) x-
      (selectorPolicy (fun _ : State 1=>none)).truncatedValue M 1 (t:=0) x= -(3/8) ∧
    (selectorPolicy ((substrate 0).execute true)).infiniteValue M (t:=0) x=3/32 ∧
    (selectorPolicy (fun _ : State 1=>none)).infiniteValue M (t:=0) x=0 :=
  RegisterFaultFinitePurposeProbe.one_step_negative_not_infinite_idle_optimal noise

example (noise : PMF Bool) :
    (model (2 : Fin 3) noise ⟨false,4⟩ (1/2) (1/4) quarter_ok (1/2) (by norm_num)).optimalValue bad.physical=0 ∧
    (model (2 : Fin 3) noise ⟨false,4⟩ (1/2) (1/4) quarter_ok (1/2) (by norm_num)).optimalValue good.physical=6/5 :=by
  rw [←idle_value_eq_optimal 2 noise ⟨false,4⟩ (1/2) (1/4) quarter_ok (1/2) (by norm_num) (by norm_num [repairChance])]
  norm_num [idleValue,idleGoodValue,bad,good,repairChance]
example (noise : PMF Bool) :
    IsBellmanGODSelector (model (2 : Fin 3) noise ⟨false,16/5⟩ (1/2) (1/4) quarter_ok (1/2) (by norm_num)) ((substrate 2).execute false) ∧
    IsBellmanGODSelector (model (2 : Fin 3) noise ⟨false,16/5⟩ (1/2) (1/4) quarter_ok (1/2) (by norm_num)) (fun _=>none) :=
  threshold_tie 2 noise ⟨false,16/5⟩ (1/2) (1/4) quarter_ok (1/2) (by norm_num) (by norm_num [repairChance])

example (noise : PMF Bool) :
    IsBellmanGODSelector (model (2 : Fin 3) noise low 0 (1/2) half_ok (3/4) (by norm_num)) (fun _=>some false) :=
  free_target_write_god 2 noise low 0 (1/2) half_ok (3/4) (by norm_num) (by simp)
example : (RegisterFaultJointRecord.modeRecordStep (2 : Fin 3) low good (some false) true true).transaction.expenditure=5 :=rfl
example (noise : PMF Bool) (a : Action) :
    a∈BellmanGODCorrespondence (model (2 : Fin 3) noise high 100 1 (by norm_num) (3/4) (by norm_num)) bad.physical :=
  total_fault_all_actions_god 2 noise high 100 (3/4) (by norm_num) bad.physical a

#print axioms common_actual_consumers
#print axioms dynamic_value_eq_optimal
#print axioms idle_god_iff
#print axioms actual_all_price_god_selector
end
end IndependentDynamicPrice
