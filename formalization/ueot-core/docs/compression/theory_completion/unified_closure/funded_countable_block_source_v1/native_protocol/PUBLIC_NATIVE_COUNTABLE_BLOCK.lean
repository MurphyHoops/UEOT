import UEOT
namespace IndependentBlockInfinite
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterRotatingBodySource RegisterBlockFormationTransport RegisterBlockInfiniteTransport RegisterBlockReturnTransport
open RegisterRotatingBodyReturns (RoundStream infiniteLaw successMass)
open scoped NNReal ENNReal Topology
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩
def block : Fin 3 ↪ Fin 5:=⟨fun j=>if j=0 then 4 else if j=1 then 1 else 3,by
  intro j l h
  have hv:=congrArg Fin.val h
  fin_cases j <;> fin_cases l <;> first | rfl | (norm_num at hv)⟩
@[simp] theorem block_apply (j : Fin 3) : block j=(if j=0 then 4 else if j=1 then 1 else 3) :=rfl
@[simp] theorem block_zero : block 0=4 :=rfl
@[simp] theorem block_one : block 1=1 :=rfl
@[simp] theorem block_two : block 2=3 :=rfl
def seed : Organism 5:=⟨[false,true,false,false],fun _=>true,false⟩
def raw : RoundStream 5:=fun r j=>(decide (r=0 ∨ j.val≠4),true)
def noise : PMF Bool:=PMF.pure true
def eps : NNReal:=2/5
theorem he : eps≤1 :=by change (2/5 : ℝ)≤1;norm_num
theorem consumer_01 : (recordsThrough block false (7/3) seed raw 2).length=6 :=actual_prefix_length _ _ _ _ _ _
theorem consumer_02 : (parentAt block false (7/3) seed raw 2).physical 4=true ∧
    (parentAt block false (7/3) seed raw 2).physical 1=false ∧
    (parentAt block false (7/3) seed raw 2).physical 3=false ∧
    (parentAt block false (7/3) seed raw 2).physical 0=true :=by
  norm_num [parentAt,runPorts,transaction,raw,seed,List.finRange,block_apply,Function.update_apply,Fin.ext_iff,modeRecordStep,RegisterJointRecord.recordStep,execute_compiled,update]
theorem consumer_03 : ((recordsThrough block false (7/3) seed raw 2).map (fun r=>r.transaction.expenditure)).sum=7 :=by
  norm_num [recordsThrough,parentAt,tracePorts,runPorts,transaction,raw,seed,List.finRange,block_apply,Function.update_apply,Fin.ext_iff,modeRecordStep,RegisterJointRecord.recordStep,execute_compiled,update,cost]
theorem consumer_04 (r : ℕ) : (recordsThrough block false (7/3) seed raw r).map (modeRecord block)=
    RegisterRotatingBodyReturns.recordsThrough false (7/3) (organism block seed) (stream block raw) r :=
  prefix_transport _ _ _ _ _ _
theorem consumer_05 (r : ℕ) : ¬BodyGoal false (parentAt block false (7/3) seed raw r).physical :=by
  apply not_passive_never_full
  intro h
  have hh:=h 0 (by rintro ⟨j,hj⟩;have hv:=congrArg Fin.val hj; fin_cases j <;> norm_num [block_apply] at hv)
  norm_num [seed] at hh
theorem consumer_06 : (recordPathLaw block false (7/3) noise eps he seed).map (projectedRecords block)=
    RegisterRotatingBodyReturns.recordPathLaw false (7/3) noise eps he (organism block seed) :=
  countable_record_transport _ _ _ _ _ _ _

-- A genuinely countable tail event: zero-fee first transactions arbitrarily far out.
def tailZero : Set (ℕ→Fin 3→ModeRecord 3):={rs | ∀N : ℕ, ∃r : ℕ, N≤r ∧ (rs r 0).transaction.expenditure=0}
theorem tailZero_measurable : MeasurableSet tailZero :=by
  have hE : tailZero=⋂N : ℕ,⋃r : ℕ,⋃(_ : N≤r),{rs | (rs r 0).transaction.expenditure=0} :=by
    ext rs
    simp [tailZero]
  rw [hE]
  exact MeasurableSet.iInter (fun N=>MeasurableSet.iUnion (fun r=>MeasurableSet.iUnion (fun _=>
    (show MeasurableSet {q : ModeRecord 3 | q.transaction.expenditure=0} from trivial).preimage
      ((measurable_pi_apply 0).comp (measurable_pi_apply r)))))
theorem consumer_07 : recordPathLaw block false (7/3) noise eps he seed (projectedRecords block ⁻¹' tailZero)=
    RegisterRotatingBodyReturns.recordPathLaw false (7/3) noise eps he (organism block seed) tailZero :=
  record_event_transport _ _ _ _ _ _ _ _ tailZero_measurable

theorem rate : RegisterRotatingBodyP10.failureRate 3 eps=(98/125 : NNReal) :=by
  apply Subtype.ext
  norm_num [RegisterRotatingBodyP10.failureRate,NNReal.coe_sub_def,eps]
theorem consumer_08 : infiniteLaw 5 noise eps he {v | ∀r∈Finset.range 7,¬blockGoal block false (7/3) seed v (23+r+1)}=((98/125 : NNReal) : ℝ≥0∞)^7 :=by
  have h:=actual_block_no_return_tail block false (7/3) noise eps he seed 23 7
  rw [←RegisterRotatingBodyP10.failureRate_coe,rate] at h
  exact h
theorem consumer_09 (r : ℕ) : (infiniteLaw 5 noise eps he).real {v | ¬blockGoal block false (7/3) seed v (r+1)}≤98/125 :=by
  have h:=original_p10_block_tail block false (7/3) noise eps he seed r
  rw [rate] at h
  norm_num at h
  exact h
theorem consumer_10 : ∀ᵐ v ∂infiniteLaw 5 noise eps he,∀N : ℕ,∃r≥N,blockGoal block false (7/3) seed v (r+1) :=
  actual_block_returns_forever _ _ _ _ _ (by change (2/5 : ℝ)<1;norm_num) _
theorem consumer_11 : ¬∃ D : (ℕ→Fin 3→ModeRecord 3)→Prop,
    (∀ᵐ v ∂infiniteLaw 5 noise eps he,
      BodyGoal false (parentAt block false (7/3) (readySeed 5 false) v 1).physical ↔D (projectedRecords block (infiniteRecords block false (7/3) (readySeed 5 false) v))) ∧
    (∀ᵐ v ∂infiniteLaw 5 noise eps he,
      BodyGoal false (parentAt block false (7/3) (hiddenSeed false (0 : Fin 5)) v 1).physical ↔D (projectedRecords block (infiniteRecords block false (7/3) (hiddenSeed false 0) v))) :=
  hidden_body_not_ae_decodable _ _ _ _ _ (by change (2/5 : ℝ)<1;norm_num) 0
    (by rintro ⟨j,hj⟩;have hv:=congrArg Fin.val hj; fin_cases j <;> norm_num [block_apply] at hv)
theorem consumer_12 (v : RoundStream 5) (r : ℕ) : BodyGoal false (parentAt block false (7/3) (readySeed 5 false) v r).physical ↔
    blockGoal block false (7/3) (readySeed 5 false) v r :=by
  rw [full_goal_iff]
  simp [PassiveReady,readySeed]
#print axioms rate
#print axioms tailZero_measurable
#print axioms consumer_01
#print axioms consumer_02
#print axioms consumer_03
#print axioms consumer_04
#print axioms consumer_05
#print axioms consumer_06
#print axioms consumer_07
#print axioms consumer_08
#print axioms consumer_09
#print axioms consumer_10
#print axioms consumer_11
#print axioms consumer_12
end
end IndependentBlockInfinite
