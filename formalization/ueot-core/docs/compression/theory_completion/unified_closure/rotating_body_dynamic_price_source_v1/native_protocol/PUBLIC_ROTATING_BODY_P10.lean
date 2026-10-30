import UEOT
namespace IndependentRotatingBody
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterFaultJointRecord
open RegisterRotatingBodySource RegisterRotatingBodyReturns RegisterRotatingBodyP10
open UEOT.V3.RecoveryProbability
open scoped ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩

theorem eps_ok : (1/3 : NNReal)≤1 := by exact_mod_cast (by norm_num : (1/3 : ℝ)≤1)
theorem eps_lt : (1/3 : NNReal)<1 := by exact_mod_cast (by norm_num : (1/3 : ℝ)<1)
theorem one_sub_eps : 1-(1/3 : NNReal)=(2/3 : NNReal) := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub eps_ok]
  norm_num
theorem failure_exact : failureRate 3 (1/3)=(19/27 : NNReal) := by
  unfold failureRate
  rw [one_sub_eps]
  apply NNReal.coe_injective
  rw [NNReal.coe_sub (by exact_mod_cast (by norm_num : (2/3 : ℝ)^3≤1))]
  norm_num
theorem success_exact : successMass 3 (1/3)=(8/27 : ℝ≥0∞) := by
  unfold successMass
  rw [one_sub_eps]
  have hh : (2/3 : NNReal)^3=(8/27 : NNReal) := by
    apply NNReal.coe_injective
    norm_num
  rw [←ENNReal.coe_pow,hh]
  norm_num only [ENNReal.coe_div,ENNReal.coe_ofNat]


def seed : Organism 3 := ⟨[true,false],fun j=>if j=1 then false else true,false⟩
def labels : PMF Bool := PMF.pure true
def raw0 : RoundRaw 3 := fun j=>(if j=1 then false else true,j=2)
def raw1 : RoundRaw 3 := fun _=>(true,false)
def stream : RoundStream 3 := fun k=>if k=0 then raw0 else raw1
abbrev mu := infiniteLaw 3 labels (1/3) eps_ok

example : ¬BodyGoal false seed.physical := by
  intro h
  have hh:=h 0
  change true=false at hh
  cases hh

example : (recordsThrough false 2 seed stream 2).length=6 := by
  simpa using actual_prefix_length false 2 seed stream 2

example : (parentAt false 2 seed stream 1).physical 0=false ∧
    (parentAt false 2 seed stream 1).physical 1=true ∧
    (parentAt false 2 seed stream 1).physical 2=false := by
  rw [actual_parent_closed]
  decide

example : BodyGoal false (parentAt false 2 seed stream 2).physical := by
  apply (actual_macro_goal_iff false 2 seed stream 1).mpr
  intro j
  rfl

example : (recordAt false 2 seed 0 0 stream).transaction.action=some false ∧
    (recordAt false 2 seed 0 0 stream).transaction.expenditure=2 ∧
    (recordAt false 2 seed 0 1 stream).repairMode=false ∧
    (recordAt false 2 seed 0 1 stream).transaction.child=none ∧
    (recordAt false 2 seed 0 1 stream).transaction.expenditure=0 ∧
    (recordAt false 2 seed 0 2 stream).transaction.expenditure=2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

-- Actual first serviced-port child is born while another body coordinate is bad.
example : ∃ child : Organism 3,
    (transaction (0 : Fin 3) false 2 seed (true,false)).transaction.child=some child ∧
    ¬BodyGoal false child.physical := by
  refine ⟨birthEvent 0 false (transaction (0 : Fin 3) false 2 seed (true,false)).transaction.parentAfter, rfl, ?_⟩
  intro h
  have hh:=h 2
  change true=false at hh
  cases hh

example : IsProbabilityMeasure (recordPathLaw false 2 labels (1/3) eps_ok seed) := inferInstance

example (k : ℕ) :
    mu {w | BodyGoal false (parentAt false 2 seed w (k+1)).physical}=(8/27 : ℝ≥0∞) := by
  rw [actual_body_mass,success_exact]

example (N R : ℕ) :
    mu {w | ∀k∈Finset.range R,¬BodyGoal false (parentAt false 2 seed w (N+k+1)).physical}=
      (19/27 : ℝ≥0∞)^R := by
  rw [actual_no_return_tail]
  have hh:=failureRate_coe 3 (1/3)
  rw [failure_exact] at hh
  rw [←hh]
  norm_num only [ENNReal.coe_div,ENNReal.coe_ofNat]

example : ∀ᵐ w ∂mu,∀N : ℕ,∃k≥N,BodyGoal false (parentAt false 2 seed w (k+1)).physical :=
  actual_returns_forever false 2 labels (1/3) eps_lt seed

example : ennMean mu (defect false 2 seed) 0=1 := by
  have hh : ¬BodyGoal false seed.physical := by
    intro h
    have hx:=h 0
    change true=false at hx
    cases hx
  simp [ennMean,defect,parentAt,hh]

example (k : ℕ) :
    realMean mu (defect false 2 seed) (k+1)≤19/27 ∧
    mu.real {w | ¬BodyGoal false (parentAt false 2 seed w (k+1)).physical}≤19/27 := by
  constructor
  · simpa only [failure_exact,NNReal.coe_div,NNReal.coe_ofNat] using original_p10_body_mean false 2 labels (1/3) eps_ok seed k
  · simpa only [failure_exact,NNReal.coe_div,NNReal.coe_ofNat] using original_p10_body_tail false 2 labels (1/3) eps_ok seed k

example : Measurable[fullPast 3 5] (recordAt false 2 seed 2 1) :=
  previous_record_measurable false 2 seed (by norm_num) 1

example (k : ℕ) : mu⁻[defect false 2 seed (k+1)|fullPast 3 k] ≤ᵐ[mu]
    fun w=>(0 : NNReal)*defect false 2 seed k w+(failureRate 3 (1/3) : ℝ≥0∞) :=
  actual_p10_conditional_drift false 2 labels (1/3) eps_ok seed k

example (w : RoundStream 3) (k : ℕ) :
    List.ofFn (fun j : Fin 3=>recordAt false 2 seed k j w)=roundTrace false 2 (w k) (parentAt false 2 seed w k) :=
  actual_round_records false 2 seed w k

example : ∀ᵐ w ∂infiniteLaw 3 labels 1 (by norm_num),∀k : ℕ,
    ¬BodyGoal false (parentAt false 2 seed w (k+1)).physical :=
  total_fault_no_body_round (by norm_num) false 2 labels seed

example (k : ℕ) : realMean (infiniteLaw 3 labels 0 (by norm_num))
    (defect false 2 seed) (k+1)≤0 := by
  simpa [failureRate] using original_p10_body_mean false 2 labels 0 (by norm_num) seed k

example (w : RoundStream 0) (o : Organism 0) (k : ℕ) :
    (recordsThrough false 2 o w k).length=0 ∧ BodyGoal false (parentAt false 2 o w k).physical := by
  constructor
  · simpa using actual_prefix_length false 2 o w k
  · intro j
    exact Fin.elim0 j

example : ¬∃ next : State 1→State 1,∀ o : Organism 2,
    RegisterActuatorScaleSource.projectState 1 (transaction 0 true 1 o (true,false)).transaction.parentAfter.physical=
      next (RegisterActuatorScaleSource.projectState 0 o.physical) := next_port_information_obstruction

-- Common source/parent/parameters: actual complete law, original P10,
-- exact return tail and infinitely many complete-body returns coexist.
theorem common_actual_consumers :
    IsProbabilityMeasure (recordPathLaw false 2 labels (1/3) eps_ok seed) ∧
    (∀k : ℕ,realMean mu (defect false 2 seed) (k+1)≤(failureRate 3 (1/3) : ℝ)) ∧
    (∀N R : ℕ,mu {w | ∀k∈Finset.range R,¬BodyGoal false (parentAt false 2 seed w (N+k+1)).physical}=
      (1-successMass 3 (1/3))^R) ∧
    (∀ᵐ w ∂mu,∀N : ℕ,∃k≥N,BodyGoal false (parentAt false 2 seed w (k+1)).physical) :=
  ⟨inferInstance,original_p10_body_mean false 2 labels (1/3) eps_ok seed,
    actual_no_return_tail false 2 labels (1/3) eps_ok seed,
    actual_returns_forever false 2 labels (1/3) eps_lt seed⟩
#print axioms common_actual_consumers

#print axioms original_p10_body_mean
#print axioms actual_returns_forever
#print axioms actual_round_records
end
end IndependentRotatingBody
