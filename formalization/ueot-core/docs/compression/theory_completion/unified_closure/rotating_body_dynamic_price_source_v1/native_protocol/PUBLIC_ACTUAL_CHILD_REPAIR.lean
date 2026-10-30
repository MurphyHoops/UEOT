import UEOT
namespace IndependentRotatingChild
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel UEOT.V3.FiniteDiscountedControl
open UEOT.V3.RecoveryProbability
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterFaultSource RegisterRotatingBodySource RegisterRotatingBodyReturns RegisterRotatingBodyP10 RegisterRotatingChildRepair
open scoped ENNReal
noncomputable section

def initial : Organism 4:=⟨[false,true,false],fun _=>false,true⟩
def birthRaw : RoundRaw 4:=fun i=>(i=2,i=2)
def future : RoundRaw 4:=fun i=>(true,i=0)
def firstFault : ModeRecord 4:=transaction 0 true 5 initial (false,false)
def secondFault : ModeRecord 4:=transaction 1 true 5 firstFault.transaction.parentAfter (false,false)
def actualBirth : ModeRecord 4:=transaction 2 true 5 secondFault.transaction.parentAfter (true,true)
def lastFault : ModeRecord 4:=transaction 3 true 5 actualBirth.transaction.parentAfter (false,false)
def child : Organism 4:=birthEvent 2 true actualBirth.transaction.parentAfter
def repaired : Organism 4:=roundParent true 5 future child

theorem child_actual : actualBirth.transaction.child=some child :=rfl
theorem member_actual : actualBirth∈tracePorts true 5 birthRaw initial (List.finRange 4) :=by
  change actualBirth∈[firstFault,secondFault,actualBirth,lastFault]
  simp

theorem all_repair : ∀i,(future i).1=true :=fun _=>rfl

example : (roundTrace true 5 birthRaw initial).map (fun r=>r.transaction.expenditure)=[0,0,5,0] :=rfl
example : (roundTrace true 5 birthRaw initial).map (fun r=>r.transaction.child.isSome)=[false,false,true,false] :=rfl
example : child.program=true ∧ child.history=[false,true,false,true] :=⟨rfl,rfl⟩
example : ¬BodyGoal true child.physical :=by
  intro h
  have hh:=h 0
  change false=true at hh
  cases hh
example : (roundTrace true 5 future child).map (fun r=>r.transaction.expenditure)=[5,5,0,5] :=rfl
example : (roundTrace true 5 future child).length=4 :=rfl
example : BodyGoal true repaired.physical :=(actual_cycle_repairs true 5 future child all_repair).1
example : repaired.program=child.program ∧ repaired.history=child.history :=⟨rfl,rfl⟩
example : repaired.history.dropLast=initial.history :=
  (repaired_child_parent_history true 5 birthRaw future initial rfl (List.finRange 4)
    actualBirth member_actual child child_actual).2
example (i : Fin 4) : (lineage i).SameObject child repaired ∧ ¬(lineage i).OffspringOf child repaired :=
  actual_cycle_same_child i true 5 future child
example : (lineage (2 : Fin 4)).OffspringOf actualBirth.transaction.parentAfter child :=
  birth_is_distinct_offspring 2 true _
example (a : Action) : ¬BodyGoal true (update 2 child.physical a) :=
  fixed_port_passive_damage 2 0 (by decide) true child.physical (by decide) a

example (i : Fin 4) : RepairProgramValid (substrate i) (physical i) {x | BodyGoal true x} true :=
  actual_body_valid i true

example (i : Fin 4) (noise : PMF Bool) :
    let M:=model i noise (3/7) (2/3) (by norm_num) ⟨true,5⟩
    let K : Set (State 4):={x | BodyGoal true x}
    let hv:=actual_body_model_valid i true noise (3/7) (2/3) (by norm_num) ⟨true,5⟩
    StaysIn (M.transitionPMF repaired.physical
      (recoveredProgramSourceSafeAction M K (substrate i) true hv repaired.physical).1) K ∧
      StaysIn (jointRepairKernel (substrate i) (fun x a=>M.transitionPMF x a)
        (restoredJointState (substrate i) true repaired.physical)) (RecoveredJointTarget (substrate i) K true) :=
  actual_cycle_source_and_joint_safety i true 5 future child all_repair noise (3/7) (2/3) (by norm_num)

theorem eps_ok : (1/2 : NNReal)≤1 :=by exact_mod_cast (by norm_num : (1/2 : ℝ)≤1)
theorem eps_lt : (1/2 : NNReal)<1 :=by exact_mod_cast (by norm_num : (1/2 : ℝ)<1)

example (i : Fin 4) :
    let seed : OntogeneticSeed (State 4) Bool:=⟨repaired.physical,repaired.program⟩
    let S:=finiteJointRecurrentHomeostasisSystem
      (physical i) (target i true) (target_fixed i true) (certificate i true)
      (substrate i) codec true (compiled_dynamics_implements i true)
      (fault i) (1/2) eps_ok (actual_fault_envelope i true)
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier :=
  repaired_actual_child_enters_p5 true 5 birthRaw future initial rfl (List.finRange 4)
    actualBirth member_actual child child_actual all_repair i (1/2) eps_ok

example (noise : PMF Bool) : roundLaw 4 noise (1/2) eps_ok
    {z | BodyGoal true (roundParent true 5 z child).physical}=(1/16 : ℝ≥0∞) :=by
  have hs : 1-(1/2 : NNReal)=(1/2 : NNReal) :=by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub eps_ok]
    norm_num
  rw [actual_child_cycle_probability,hs]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div,ENNReal.toReal_pow]

example (noise : PMF Bool) :
    ∀ᵐ w ∂infiniteLaw 4 noise (1/2) eps_ok,∀N : ℕ,∃k≥N,
      BodyGoal true (parentAt true 5 child w (k+1)).physical ∧
      (parentAt true 5 child w (k+1)).program=true ∧
      (parentAt true 5 child w (k+1)).history=child.history ∧
      (parentAt true 5 child w (k+1)).history.dropLast=initial.history :=
  actual_child_returns_same_identity true 5 birthRaw initial rfl (List.finRange 4)
    actualBirth member_actual child child_actual noise (1/2) eps_lt

-- Original P10 and literal child identity use the SAME child and future law.
theorem same_child_p10_and_identity (noise : PMF Bool) :
    (∀k : ℕ,realMean (infiniteLaw 4 noise (1/2) eps_ok) (defect true 5 child) (k+1)≤(failureRate 4 (1/2) : ℝ)) ∧
    (∀ᵐ w ∂infiniteLaw 4 noise (1/2) eps_ok,∀N : ℕ,∃k≥N,
      BodyGoal true (parentAt true 5 child w (k+1)).physical ∧
      (parentAt true 5 child w (k+1)).program=true ∧
      (parentAt true 5 child w (k+1)).history=child.history ∧
      (parentAt true 5 child w (k+1)).history.dropLast=initial.history) :=
  ⟨original_p10_body_mean true 5 noise (1/2) eps_ok child,
    actual_child_returns_same_identity true 5 birthRaw initial rfl (List.finRange 4)
      actualBirth member_actual child child_actual noise (1/2) eps_lt⟩

example (noise : PMF Bool) : ennMean (infiniteLaw 4 noise (1/2) eps_ok) (defect true 5 child) 0=1 :=by
  have hb : ¬BodyGoal true child.physical :=by
    intro h
    have hh:=h 0
    change false=true at hh
    cases hh
  simp [ennMean,defect,parentAt,hb]

example (noise : PMF Bool) (k : ℕ) :
    realMean (infiniteLaw 4 noise (1/2) eps_ok) (defect true 5 child) (k+1)≤(15/16 : ℝ) :=by
  have hs : 1-(1/2 : NNReal)=(1/2 : NNReal) :=by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub eps_ok]
    norm_num
  have hf : failureRate 4 (1/2)=(15/16 : NNReal) :=by
    unfold failureRate
    rw [hs]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by exact_mod_cast (by norm_num : (1/2 : ℝ)^4≤1))]
    norm_num
  simpa only [hf,NNReal.coe_div,NNReal.coe_ofNat] using original_p10_body_mean true 5 noise (1/2) eps_ok child k

example (noise : PMF Bool) : roundLaw 4 noise 1 (by norm_num)
    {z | BodyGoal true (roundParent true 5 z child).physical}=0 :=by
  rw [actual_child_cycle_probability];norm_num
example (noise : PMF Bool) : roundLaw 4 noise 0 (by norm_num)
    {z | BodyGoal true (roundParent true 5 z child).physical}=1 :=by
  rw [actual_child_cycle_probability];norm_num
example (o : Organism 0) (raw : RoundRaw 0) (r : ModeRecord 0) :
    r∉roundTrace true 5 raw o :=by simp [roundTrace,tracePorts,List.finRange_zero]

#print axioms same_child_p10_and_identity
#print axioms repaired_actual_child_enters_p5
#print axioms actual_cycle_source_and_joint_safety
end
end IndependentRotatingChild
