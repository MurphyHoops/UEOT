import UEOT
namespace IndependentInstructionC4Consumer
open MeasureTheory ProbabilityTheory Filter Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open RegisterInstructionRecoveryScale RegisterInstructionHomeostasis RegisterInstructionPurposeScale RegisterInstructionGODScale
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩

def p : Instruction 4 := .test 0 true (compile 2 false) (.test 1 true (compile 2 false) (compile 2 false))
def q : Instruction 1 := returnedProgram 2 p
def o : Organism 4 := ⟨[false,true,false],![true,true,true,false],false⟩
def eps : NNReal := 2/5
theorem he : eps≤1 := by exact_mod_cast (by norm_num [eps,NNReal.coe_div] : (eps : ℝ)≤1)
theorem hepos : 0<eps := by exact_mod_cast (by norm_num [eps,NNReal.coe_div] : (0 : ℝ)<eps)
theorem helt : eps<1 := by exact_mod_cast (by norm_num [eps,NNReal.coe_div] : (eps : ℝ)<1)
theorem hs : synthesize (2 : Fin 4) p=some q := by
  have hf : finiteCheck (2 : Fin 4) p=true := by decide
  simp [synthesize,q,hf]
theorem hc : restorationCheck (2 : Fin 4) false p=true := by decide
theorem p_action (x : State 4) : interpret p x=interpret (compile 2 false) x := by simp [p,interpret]
def pq : RecoveringPair (2 : Fin 4) false := ⟨⟨(p,q),hs⟩,hc⟩

example : (projectOrganism 2 o).history=[false,true,false] ∧ (projectOrganism 2 o).program=false := ⟨rfl,rfl⟩
example (noise : PMF Bool) (t : ℕ) : iidSource noise eps he
    {w | Legitimate 2 (RegisterSemanticInstructionInfinite.parentAt 2 ⟨false,3⟩ p o w (t+1))}=
      ENNReal.ofReal (3/5 : ℝ) := by
  convert actual_maintained_probability 2 false 3 p hc o rfl noise eps he t using 1
  norm_num [eps,NNReal.coe_div]
example (noise : PMF Bool) : ∀ᵐ w ∂iidSource noise eps he,Tendsto
    (fun N : ℕ=>(∑ t∈Finset.range N,postLegitimate 2 false 3 p o t w)/(N : ℝ)) atTop (𝓝 (3/5 : ℝ)) := by
  convert actual_maintenance_frequency 2 false 3 p hc o rfl noise eps he using 1
  norm_num [eps,NNReal.coe_div]
example (noise : PMF Bool) : QuantitativeHomeostasis 0 false 3 (projectOrganism 2 o) noise eps he q :=
  p9_actual_returned_homeostasis 2 false 3 pq o rfl noise eps he
example (noise : PMF Bool) : ∀ᵐ w ∂iidSource noise eps he,
    ¬∃ N : ℕ,∀ t≥N,Legitimate 2 (RegisterSemanticInstructionInfinite.parentAt 2 ⟨false,3⟩ p o w t) :=
  actual_no_eventual_permanence 2 false 3 p hc o rfl noise eps he hepos
example (noise : PMF Bool) : ∀ᵐ w ∂iidSource noise eps helt.le,
    ∀ N : ℕ,∃ t≥N,Legitimate 2 (RegisterSemanticInstructionInfinite.parentAt 2 ⟨false,3⟩ p o w t) :=
  actual_returns_forever 2 false 3 p hc o rfl noise eps helt
example (noise : PMF Bool) : iidSource noise 1 (by norm_num)
    {w | Legitimate 2 (RegisterSemanticInstructionInfinite.parentAt 2 ⟨false,3⟩ p o w 1)}=0 := by
  simpa using actual_maintained_probability 2 false 3 p hc o rfl noise 1 (by norm_num) 0
example (noise : PMF Bool) : iidSource noise 0 (by norm_num)
    {w | Legitimate 2 (RegisterSemanticInstructionInfinite.parentAt 2 ⟨false,3⟩ p o w 1)}=1 := by
  simpa using actual_maintained_probability 2 false 3 p hc o rfl noise 0 (by norm_num) 0
-- Whole correlated primitive-path transport is a separate exact source result;
-- ONLY the explicit iidSource above receives the SLLN conclusion.
example (μ : Measure RegisterSemanticInstructionInfinite.Stream) :
    (RegisterSemanticInstructionInfinite.recordPathLaw 2 ⟨false,3⟩ p o μ).map
      (RegisterSemanticInstructionInfinite.projectPath 2)=
      RegisterSemanticInstructionInfinite.recordPathLaw 0 ⟨false,3⟩ q (projectOrganism 2 o) μ :=
  RegisterSemanticInstructionInfinite.actual_countable_path_law 2 ⟨false,3⟩ p q hs o μ

-- The native old Config/run retains the actual parent, including history/code.
def events : List RegisterFaultInfiniteRecord.Event :=
  [(some false,true,true),(none,false,false),(some false,true,false)]
example : projectOrganism 2
    (RegisterFaultInfiniteRecord.run 2 ⟨false,3⟩ (astPolicy p) ⟨0,o.physical,o⟩ events).2.2=
    (RegisterFaultInfiniteRecord.run 0 ⟨false,3⟩ (astPolicy q)
      (projectASTConfig 2 p q ⟨0,o.physical,o⟩) events).2.2 :=
  actual_run_parent 2 ⟨false,3⟩ p q ⟨0,o.physical,o⟩ events
example (noise : PMF Bool) :
    (RegisterFaultInfiniteRecord.recordPathLaw 2 noise ⟨false,3⟩ eps he (astPolicy p) ⟨0,o.physical,o⟩).map
      (fun rs k=>projectModeRecord 2 (rs k))=
      RegisterFaultInfiniteRecord.recordPathLaw 0 noise ⟨false,3⟩ eps he (astPolicy q)
        (projectASTConfig 2 p q ⟨0,o.physical,o⟩) :=
  actual_recordPathLaw 2 noise ⟨false,3⟩ eps he p q hs _
example (noise : PMF Bool) : actualValue 2 noise ⟨false,3⟩ eps he (1/6) (2/3) o p=
    actualValue 0 noise ⟨false,3⟩ eps he (1/6) (2/3) (projectOrganism 2 o) q :=
  actual_value_transport 2 noise ⟨false,3⟩ eps he (1/6) (2/3) o p q hs
example (noise : PMF Bool) : Integrable (RegisterFaultInfiniteRecord.streamPayoff (1/6) (2/3))
    (RegisterFaultInfiniteRecord.recordPathLaw 2 noise ⟨false,3⟩ eps he (astPolicy p) ⟨0,o.physical,o⟩) :=
  actual_value_integrable 2 noise ⟨false,3⟩ eps he (1/6) (2/3) (by norm_num) o p
example (noise : PMF Bool) (π : CausalPolicy.{0,0,0} (State 4) (fun _=>Action)) {t : ℕ} (h : π.Memory t)
    (hx : o.physical=π.current h) :
    (∫ rs,RegisterFaultInfiniteRecord.streamPayoff (1/6) (2/3) rs
      ∂(RegisterFaultInfiniteRecord.recordPathLaw 2 noise ⟨false,3⟩ eps he π ⟨t,h,o⟩))≤
      actualValue 2 noise ⟨false,3⟩ eps he (1/6) (2/3) o (compile 2 false) :=
  actual_compiled_dominates_all_causal 2 noise ⟨false,3⟩ eps he (1/6) (2/3) (by norm_num) (by norm_num) o rfl π h hx
example (noise : PMF Bool) : actualValue 0 noise ⟨false,3⟩ eps he (1/6) (2/3) (projectOrganism 2 o) q≤
    actualValue 0 noise ⟨false,3⟩ eps he (1/6) (2/3) (projectOrganism 2 o)
      (returnedProgram (2 : Fin 4) (compile 2 false)) :=
  compiled_actual_p9_purpose 2 noise ⟨false,3⟩ eps he (1/6) (2/3) (by norm_num) (by norm_num) o rfl pq.val
example (noise : PMF Bool) : IsBellmanGODSelector
    (RegisterFaultControlModel.model 0 noise ⟨false,3⟩ (1/6) eps he (2/3) (by norm_num)) (interpret q) := by
  apply (actual_god_selector_iff 2 noise ⟨false,3⟩ (1/6) eps he (2/3) (by norm_num) (by norm_num) p q hs).mp
  intro x
  rw [p_action]
  exact actual_compiled_god 2 noise ⟨false,3⟩ (1/6) eps he (2/3) (by norm_num) (by norm_num) x
-- Same physical parent path under arbitrary raw words does not identify fees.
example (w : RegisterSemanticInstructionInfinite.Stream) (t : ℕ) :
    RegisterSemanticInstructionInfinite.parentAt 2 ⟨false,3⟩ (compile 2 false) o w t=
      RegisterSemanticInstructionInfinite.parentAt 2 ⟨false,3⟩ (.emit (some false)) o w t :=
  same_actual_parent_path 2 false 3 o w t
example (noise : PMF Bool) : let e : (1/4 : NNReal)≤1:=by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
    let z : Organism 1:=⟨[false,true,false],fun _=>true,true⟩
    actualValue 0 noise ⟨true,1⟩ (1/4) e 1 (1/2) z (compile 0 true)=21/16 ∧
    actualValue 0 noise ⟨true,1⟩ (1/4) e 1 (1/2) z (.emit (some true))=0 ∧
    actualValue 0 noise ⟨true,1⟩ (1/4) e 1 (1/2) z (.emit (some true))<
      actualValue 0 noise ⟨true,1⟩ (1/4) e 1 (1/2) z (compile 0 true) := strict_paid_write_boundary noise _
-- This is a DIFFERENT, explicitly zero-price evaluation contract.
example (noise : PMF Bool) : let e : (1/4 : NNReal)≤1:=by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
    actualValue (0 : Fin 2) noise ⟨true,1⟩ (1/4) e 0 (1/2)
      ⟨[false,true,false],![false,true],true⟩ hiddenOptimal=3/2 ∧
    ¬∃ f : State 1→Action,∀ x,f (projectState (0 : Fin 2) x)=interpret hiddenOptimal x :=
  ⟨positive_fault_hidden_actual_value noise _ rfl,hiddenOptimal_no_factor.2⟩
-- Native GOD is a true set, not a particular greedy tie-break output.
def M0 (noise : PMF Bool) : Model (State 1) (fun _=>Action) :=
  RegisterFaultControlModel.model 0 noise ⟨true,1⟩ 0 (1/4)
    (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) (1/2) (by norm_num)
theorem two_god_actions (noise : PMF Bool) :
    none∈BellmanGODCorrespondence (M0 noise) (fun _=>true) ∧
    some true∈BellmanGODCorrespondence (M0 noise) (fun _=>true) := by
  have hg:=(positive_fault_hidden_god noise).1
  constructor
  · have hh:=(actual_god_action_iff (0 : Fin 2) noise ⟨true,1⟩ 0 (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) (1/2) (by norm_num) (by simp)
      ![true,true] (interpret hiddenOptimal ![true,true])).mp (hg ![true,true])
    exact hh
  · have hh:=(actual_god_action_iff (0 : Fin 2) noise ⟨true,1⟩ 0 (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) (1/2) (by norm_num) (by simp)
      ![true,false] (interpret hiddenOptimal ![true,false])).mp (hg ![true,false])
    exact hh
example (noise : PMF Bool) : ∃ a : Action,a∈BellmanGODCorrespondence (M0 noise) (fun _=>true) ∧
    a≠(M0 noise).greedyAction (fun _=>true) := by
  by_cases h : (none : Action)=(M0 noise).greedyAction (fun _=>true)
  · refine ⟨some true,(two_god_actions noise).2,?_⟩
    rw [←h]
    decide
  · exact ⟨none,(two_god_actions noise).1,h⟩
-- All-fault epsilon1 makes idle optimal but does not make it restoring.
example (noise : PMF Bool) : IsBellmanGODSelector
    (RegisterFaultControlModel.model (2 : Fin 4) noise ⟨false,3⟩ (1/6) 1 (by norm_num) (2/3) (by norm_num))
    (interpret (.emit none)) ∧ restorationCheck (2 : Fin 4) false (.emit none)=false := by
  refine ⟨?_,(idle_valid_not_restoring (2 : Fin 4) false).2⟩
  intro x
  rw [mem_bellmanGODCorrespondence_iff,
    ←RegisterFaultControlModel.value_eq_optimal 2 noise ⟨false,3⟩ (1/6) 1 (by norm_num) (2/3) (by norm_num) (by norm_num),
    RegisterFaultControlModel.qValue_source]
  simp [RegisterFaultControlModel.value,RegisterFaultControlModel.goodValue,RegisterFaultControlModel.badValue,
    RegisterFaultControlModel.repairChance]

end
end IndependentInstructionC4Consumer
