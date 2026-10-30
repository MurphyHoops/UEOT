import UEOT
namespace NonAuthorActualInstructionGOA
open MeasureTheory ProbabilityTheory
open UEOT.V3 UEOT.V3.FiniteDobrushin UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open RegisterInstructionPurposeScale RegisterInstructionRecoveryScale RegisterInstructionGODScale
open RegisterSemanticInstructionInfinite RegisterInstructionHomeostasis RegisterInstructionGOASource
open scoped ENNReal
noncomputable section
noncomputable local instance {n : ℕ} : DecidableEq (State n):=Classical.decEq _
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩
-- Different n/port/target/history/seed/noise/discount from author's n4/port2/false fixture.
def m : Mechanism:=⟨true,1⟩
def seed (b : Bool) : State 3:=fun j=>if j=1 then true else if j=2 then b else false
def o : Organism 3:=⟨[false,true,true],seed true,true⟩
def eps : NNReal:=1/3
theorem he : eps≤1 := by exact_mod_cast (by norm_num[eps] : (eps : ℝ)≤1)
def p : Instruction 3:=.test 0 false (compile 1 true) (compile 1 true)
def q : Instruction 1:=returnedProgram 1 p

theorem hs : synthesize (1 : Fin 3) p=some q := by
  simp[p,q,synthesize,finiteCheck,returnedProgram,compile,interpret,representative,projectState]
theorem hp_action (x : State 3) : interpret p x=interpret (compile (1 : Fin 3) true) x := by simp[p,interpret]
theorem hr : restorationCheck (1 : Fin 3) m.goal p=true := by
  rw[restorationCheck_iff]
  intro x
  rw[hp_action,same_repair_different_value_physical]
  simp[interpret,RegisterRepairSource.update,m]
theorem hq : restorationCheck (0 : Fin 1) m.goal q=true := (returned_restoration_iff 1 m.goal p q hs).mp hr

example (w : Stream) (t : ℕ) : (parentAt 1 m p o w (t+1)).physical=resetState 1 m o.physical (w t).1 := actual_parent_reset 1 m p hr o w t
example (w : Stream) (t : ℕ) : (parentAt 1 m p o w (t+1)).physical (2 : Fin 3)=true := by
  rw[actual_parent_reset 1 m p hr o]
  simp[resetState,o,seed]
example (noise : PMF Bool) (t : ℕ) : IsProbabilityMeasure ((iidSource noise eps he).map (fun w=>(parentAt 1 m p o w (t+1)).physical)) := actual_positive_time_probability 1 noise m eps he p hr o t
example (noise : PMF Bool) (t : ℕ) : (iidSource noise eps he).map (fun w=>(parentAt 1 m p o w (t+1)).physical)=
    (sourceLaw (1 : Fin 3) m eps he o.physical).toMeasure := actual_positive_time_law 1 noise m eps he p hr o t
example (noise : PMF Bool) : rowPMF (actualMatrix 1 noise m 1 eps he (2/3) (by norm_num) p)
    (actualMatrix_stochastic 1 noise m 1 eps he (2/3) (by norm_num) p) o.physical=sourceLaw (1 : Fin 3) m eps he o.physical := actualMatrix_row 1 noise m 1 eps he (2/3) (by norm_num) p hr o.physical
example : (sourceLaw (1 : Fin 3) m eps he o.physical).map (projectState 1)=sourceLaw (0 : Fin 1) m eps he (projectState 1 o.physical) := actual_sourceLaw_projection 1 m eps he o.physical

-- Same submitted p/actual synthesized q jointly consumes native GOD/value and ORIGINAL P9 GOA.
theorem same_q_joint (noise : PMF Bool) :
    IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 1) noise m 1 eps he (2/3) (by norm_num)) (interpret q) ∧
    actualValue (0 : Fin 1) noise m eps he 1 (2/3) (projectOrganism (1 : Fin 3) o) q=
      (RegisterFaultControlModel.model 1 noise m 1 eps he (2/3) (by norm_num)).optimalValue o.physical ∧
    ActualGOA (0 : Fin 1) noise m 1 eps he (2/3) (by norm_num) (projectOrganism (1 : Fin 3) o,q) := by
  have hg : IsBellmanGODSelector (RegisterFaultControlModel.model (1 : Fin 3) noise m 1 eps he (2/3) (by norm_num)) (interpret p) := by
    intro x
    rw[hp_action]
    exact actual_compiled_god 1 noise m 1 eps he (2/3) (by norm_num) (by norm_num[m]) x
  have hqg := (actual_god_selector_iff 1 noise m 1 eps he (2/3) (by norm_num) (by norm_num[m]) p q hs).mp hg
  refine ⟨hqg,?_,?_⟩
  · have hv:=actual_god_value 0 noise m 1 eps he (2/3) (by norm_num) (projectOrganism (1 : Fin 3) o) rfl q hqg
    exact hv.trans (optimal_value_projection 1 noise m 1 eps he (2/3) (by norm_num) (by norm_num[m]) o.physical).symm
  · let accepted : Accepted (1 : Fin 3):=⟨(p,q),hs⟩
    let restoring : RecoveringPair (1 : Fin 3) m.goal:=⟨accepted,hr⟩
    exact p9_actual_returned_goa 1 noise m 1 eps he (2/3) (by norm_num) (o,restoring)

theorem returned_value (noise : PMF Bool) : actualValue (0 : Fin 1) noise m eps he 1 (2/3) (projectOrganism (1 : Fin 3) o) q=14/9 := by
  rw[(same_q_joint noise).2.1,←RegisterFaultControlModel.value_eq_optimal 1 noise m 1 eps he (2/3) (by norm_num) (by norm_num[m])]
  norm_num[RegisterFaultControlModel.value,RegisterFaultControlModel.goodValue,RegisterFaultControlModel.repairChance,m,o,seed,eps]
def accepted : Accepted (1 : Fin 3):=⟨(p,q),hs⟩
def restoring : RecoveringPair (1 : Fin 3) true:=⟨accepted,hr⟩
def paid : Instruction 3:=.emit (some true)
def paidQ : Instruction 1:=returnedProgram 1 paid
theorem paid_synthesis : synthesize (1 : Fin 3) paid=some paidQ := by
  simp[paid,paidQ,synthesize,finiteCheck,returnedProgram,interpret]
def paidAccepted : Accepted (1 : Fin 3):=⟨(paid,paidQ),paid_synthesis⟩

theorem same_object_purpose (noise : PMF Bool) :
    PurposeOrder (0 : Fin 1) noise m eps he 1 (2/3) (projectOrganism (1 : Fin 3) o,q,paidQ) := by
  have hvalue : actualValue (1 : Fin 3) noise m eps he 1 (2/3) o p=14/9 :=
    (actual_value_transport 1 noise m eps he 1 (2/3) o p q hs).trans (returned_value noise)
  have hpaid : actualValue (1 : Fin 3) noise m eps he 1 (2/3) o paid=0 :=
    always_paid_actual_zero 1 noise true eps he (2/3) (by norm_num) o rfl
  have horder : PurposeOrder (1 : Fin 3) noise m eps he 1 (2/3) (o,p,paid) := by
    refine ⟨by norm_num,?_⟩
    rw[hpaid,hvalue]
    norm_num
  exact p9_actual_returned_purpose 1 noise m eps he 1 (2/3) (o,accepted,paidAccepted) horder

-- All common constants/actual parents/submitted p/returned q remain identical.
-- Homeostasis uses its stated original IID source; value uses its original native record law.
-- Their conjunction asserts no unproved whole-adapter-path identity between these law interfaces.
theorem common_actual_consumers (noise : PMF Bool) :
    QuantitativeHomeostasis (0 : Fin 1) true 1 (projectOrganism (1 : Fin 3) o) noise eps he q ∧
    PurposeOrder (0 : Fin 1) noise m eps he 1 (2/3) (projectOrganism (1 : Fin 3) o,q,paidQ) ∧
    IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 1) noise m 1 eps he (2/3) (by norm_num)) (interpret q) ∧
    (∫rs,RegisterFaultInfiniteRecord.streamPayoff 1 (2/3) rs ∂
      RegisterFaultInfiniteRecord.recordPathLaw (0 : Fin 1) noise m eps he (astPolicy q)
        ⟨0,(projectOrganism (1 : Fin 3) o).physical,projectOrganism (1 : Fin 3) o⟩)=14/9 ∧
    ActualGOA (0 : Fin 1) noise m 1 eps he (2/3) (by norm_num) (projectOrganism (1 : Fin 3) o,q) := by
  refine ⟨p9_actual_returned_homeostasis 1 true 1 restoring o rfl noise eps he,same_object_purpose noise,
    (same_q_joint noise).1,?_,(same_q_joint noise).2.2⟩
  exact returned_value noise

example (noise : PMF Bool) : PreservesPurpose (purposeScale (1 : Fin 3))
    (fun obj=>PurposeOrder 1 noise m eps he 1 (2/3) (obj.1,obj.2.1.val.1,obj.2.2.val.1))
    (PurposeOrder (0 : Fin 1) noise m eps he 1 (2/3)) := actual_preserves_purpose 1 noise m eps he 1 (2/3)
-- Real coarse one-bit uniqueness; no fine global uniqueness is inferred.
example (noise : PMF Bool) (mu : stdSimplex ℝ (State 1))
    (hi : InvariantLawGOA (actualMatrix 0 noise m 1 eps he (2/3) (by norm_num) q)
      (actualMatrix_stochastic 0 noise m 1 eps he (2/3) (by norm_num) q) mu) : mu=sourceSimplex 0 m eps he (projectState (1 : Fin 3) o.physical) :=
  coarse_invariant_unique noise m 1 eps he (2/3) (by norm_num) q hq _ mu hi

-- NEW n3 actual submitted-p witnesses: passive coordinate2 produces two distinct invariant laws.
example (_noise : PMF Bool) : sourceSimplex (1 : Fin 3) m eps he (seed false)≠sourceSimplex (1 : Fin 3) m eps he (seed true) := by
  intro h
  have hh:=congrArg (fun law : stdSimplex ℝ (State 3)=>(simplexPMF law).map (fun x=>x (2 : Fin 3))) h
  rw[sourceSimplex_pmf,sourceSimplex_pmf,actual_passive_marginal 1 2 (by decide),actual_passive_marginal 1 2 (by decide)] at hh
  have hz:=congrArg (fun law : PMF Bool=>law false) hh
  norm_num[seed] at hz
example (noise : PMF Bool) (b : Bool) : InvariantLawGOA (actualMatrix 1 noise m 1 eps he (2/3) (by norm_num) p)
    (actualMatrix_stochastic 1 noise m 1 eps he (2/3) (by norm_num) p) (sourceSimplex 1 m eps he (seed b)) := actual_invariant_goa 1 noise m 1 eps he (2/3) (by norm_num) p hr _
-- Same physical GOA law for always-paid AST, but actual complete-record value0 remains.
example (noise : PMF Bool) : ActualGOA (1 : Fin 3) noise m 1 eps he (2/3) (by norm_num) (o,.emit (some true)) := by
  apply actual_invariant_goa
  rw[restorationCheck_iff]
  intro x
  simp[m,interpret,RegisterRepairSource.update]
example (noise : PMF Bool) : actualValue (1 : Fin 3) noise m eps he 1 (2/3) o (.emit (some true))=0 := always_paid_actual_zero 1 noise true eps he (2/3) (by norm_num) o rfl
-- Epsilon1 genuine invariant law while every actual positive-time legitimacy probability is0.
example (noise : PMF Bool) : ActualGOA (1 : Fin 3) noise m 1 1 (by norm_num) (2/3) (by norm_num) (o,p) := actual_invariant_goa 1 noise m 1 1 (by norm_num) (2/3) (by norm_num) p hr _
example (noise : PMF Bool) (t : ℕ) : iidSource noise 1 (by norm_num) {w|Legitimate 1 (parentAt 1 m p o w (t+1))}=0 := by
  have h:=actual_maintained_probability 1 true 1 p hr o rfl noise 1 (by norm_num) t
  simpa[m] using h
#print axioms common_actual_consumers
#print axioms same_object_purpose
#print axioms same_q_joint
#print axioms actual_positive_time_law
#print axioms actual_invariant_goa
#print axioms p9_actual_returned_goa
#print axioms fine_invariant_nonunique
#print axioms coarse_invariant_unique
end
end NonAuthorActualInstructionGOA
