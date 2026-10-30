import UEOT
namespace IndependentFiniteResource
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.Objecthood.ResourceClosure
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord RegisterFaultInfiniteRecord
open RegisterFaultControlModel
open RegisterActuatorScaleSource RegisterFaultFiniteResourceMaintenance RegisterFaultFiniteResourceWitness RegisterFaultFiniteResourceBoundary
open scoped NNReal ENNReal Topology
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩

def mech : Mechanism:=⟨true,7/3⟩
def initial : Organism 4:=⟨[false,true,false,true],fun _=>false,true⟩
abbrev pi:=oneAttempt 4 true
theorem eps_ok : (3/5 : NNReal)≤1 :=by exact_mod_cast (by norm_num : (3/5 : ℝ)≤1)
theorem eps_pos : (0 : NNReal)<3/5 :=by exact_mod_cast (by norm_num : (0 : ℝ)<3/5)
theorem eps_lt : (3/5 : NNReal)<1 :=by exact_mod_cast (by norm_num : (3/5 : ℝ)<1)
theorem fee_pos : 0 < mech.writeCost :=by exact_mod_cast (by norm_num : (0 : ℝ)<7/3)
abbrev mu (noise : PMF Bool):=recordPathLaw (3 : Fin 4) noise mech (3/5) eps_ok pi ⟨0,initial.physical,initial⟩

theorem actual_funding (noise : PMF Bool) :
    ∀ᵐ rs ∂mu noise,ResourceViable mech.writeCost (fun _=>0) (fun k=>(rs k).transaction.expenditure) :=
  oneAttempt_actual_funded 3 noise mech (3/5) eps_ok initial

theorem common_actual_consumer (noise : PMF Bool) :
    IsProbabilityMeasure (mu noise) ∧
    (∀ᵐ rs ∂mu noise,ResourceViable mech.writeCost (fun _=>0) (fun k=>(rs k).transaction.expenditure)) ∧
    Summable (fun k=>∫ rs,recordHealth (3 : Fin 4) (rs k) ∂mu noise) ∧
    Integrable (fun rs=>∑' k,recordHealth (3 : Fin 4) (rs k)) (mu noise) ∧
    (∀ᵐ rs ∂mu noise,Summable (fun k=>recordHealth (3 : Fin 4) (rs k))) ∧
    (∀ᵐ rs ∂mu noise,∃ N,∀ k≥N,¬Legitimate (3 : Fin 4) (rs k).transaction.parentAfter) :=by
  have hf:=actual_funding noise
  have hs:=actual_expected_health_summable 3 noise mech (3/5) eps_ok eps_pos fee_pos pi initial.physical initial rfl rfl mech.writeCost hf
  have hi:=actual_health_time_integrable 3 noise mech (3/5) eps_ok eps_pos fee_pos pi initial.physical initial rfl rfl mech.writeCost hf
  have he:=actual_eventually_never_legitimate 3 noise mech (3/5) eps_ok eps_pos fee_pos pi initial.physical initial rfl rfl mech.writeCost hf
  exact ⟨inferInstance,hf,hs,hi.1,hi.2,he⟩

example (noise : PMF Bool) :
    (∫ rs,(∑' k,recordHealth (3 : Fin 4) (rs k)) ∂mu noise)≤5/3 :=by
  have hh:=(actual_total_health_time_bound 3 noise mech (3/5) eps_ok eps_pos fee_pos pi
    initial.physical initial rfl rfl mech.writeCost (actual_funding noise)).1
  norm_num [health,mech,initial] at hh
  dsimp only [mu,mech,initial]
  linarith

example (noise : PMF Bool) (N : ℕ) :
    (∑ k∈Finset.range N,∫ rs,recordHealth (3 : Fin 4) (rs k) ∂mu noise)≤5/3 :=by
  have hh:=actual_finite_health_time_bound 3 noise mech (3/5) eps_ok eps_pos fee_pos pi
    initial.physical initial rfl rfl mech.writeCost (actual_funding noise) N
  norm_num [health,mech,initial] at hh
  dsimp only [mu,mech,initial]
  linarith

example (noise : PMF Bool) (k : ℕ) :
    (mu noise).map (fun (rs : ℕ→ModeRecord 4) (j : Fin k)=>rs j)=
      ((recordLaw (3 : Fin 4) noise mech (3/5) eps_ok pi k (t:=0) initial.physical initial).map
        (listPrefix 3 mech pi ⟨0,initial.physical,initial⟩ k)).toMeasure :=
  actual_recordPath_prefix_law 3 noise mech (3/5) eps_ok pi initial.physical initial k

-- Literal supported one-write / idle / fault prefix retains true expenditure,
-- child success/failure, paid attempt and source health without success filtering.
def word : Tape 3:=(some true,true,true,none,true,true,none,false,true,())
example : (records (3 : Fin 4) mech pi 3 (t:=0) initial.physical initial word).map
    (fun r=>r.transaction.expenditure)=[7/3,0,0] :=rfl
example : (records (3 : Fin 4) mech pi 3 (t:=0) initial.physical initial word).map
    (fun r=>r.repairMode)=[true,true,false] :=rfl
example : (records (3 : Fin 4) mech pi 3 (t:=0) initial.physical initial word).map
    (fun r=>r.transaction.child.isSome)=[true,true,false] :=rfl
example : (records (3 : Fin 4) mech pi 3 (t:=0) initial.physical initial word).map
    (fun r=>recordHealth 3 r)=[1,1,0] :=rfl

example : weight (3 : Fin 4) (PMF.pure true) mech (3/5) eps_ok pi 3 (t:=0) initial.physical initial word=12/125 :=by
  norm_num [weight,word,pi,oneAttempt,RegisterFaultControlModel.modeLaw,
    RegisterFaultControlModel.modeProbability,repairChance,FiniteProbabilityRow.ofRealRow_apply_toReal]
  change (1 : ℝ)*(2/5)*(1*(2/5)*(1*(3/5)))=12/125
  norm_num

example (noise : PMF Bool) :
    ∀ᵐ rs ∂recordPathLaw (3 : Fin 4) noise mech 1 (by norm_num) pi ⟨0,initial.physical,initial⟩,
      ∃N,∀k≥N,¬Legitimate (3 : Fin 4) (rs k).transaction.parentAfter :=
  oneAttempt_eventual_loss 3 noise mech 1 (by norm_num) (by norm_num) fee_pos initial rfl

example (noise : PMF Bool) :
    (∀ᵐ rs ∂recordPathLaw (3 : Fin 4) noise mech 0 (by norm_num) pi ⟨0,initial.physical,initial⟩,
      ResourceViable mech.writeCost (fun _=>0) (fun k=>(rs k).transaction.expenditure)) ∧
    (∀k,(∫ rs,recordHealth (3 : Fin 4) (rs k) ∂recordPathLaw (3 : Fin 4) noise mech 0 (by norm_num) pi
      ⟨0,initial.physical,initial⟩)=1) ∧
    ¬Summable (fun k=>∫ rs,recordHealth (3 : Fin 4) (rs k) ∂recordPathLaw (3 : Fin 4) noise mech 0 (by norm_num) pi
      ⟨0,initial.physical,initial⟩) :=
  native_zero_fault_boundary 3 noise mech initial rfl

abbrev muZeroFee (noise : PMF Bool):=recordPathLaw (3 : Fin 4) noise ⟨true,0⟩ (3/5) eps_ok (paid 4 true)
  ⟨0,initial.physical,initial⟩
example (noise : PMF Bool) :
    (∀ᵐ rs ∂muZeroFee noise,ResourceViable 0 (fun _=>0) (fun k=>(rs k).transaction.expenditure)) ∧
    ¬Summable (fun k=>∫ rs,recordHealth (3 : Fin 4) (rs k) ∂muZeroFee noise) :=
  native_zero_fee_boundary 3 noise true (3/5) eps_lt (t:=0) initial.physical initial rfl
example (noise : PMF Bool) (k : ℕ) : (∫ rs,recordHealth (3 : Fin 4) (rs k) ∂muZeroFee noise)=2/5 :=by
  have hh:=paid_actual_health_mean (3 : Fin 4) noise ⟨true,0⟩ (3/5) eps_ok (t:=0) initial.physical initial rfl k
  norm_num [repairChance] at hh
  exact hh

-- Independent strengthening of the two strict source boundaries using only
-- their SAME-native positive marginal and dominated convergence, no law switch.
theorem not_eventual_if_positive_mean {n : ℕ} (i : Fin n) (mu : Measure (ℕ→ModeRecord n))
    [IsProbabilityMeasure mu] (a : ℝ) (ha : 0<a)
    (hm : ∀k,(∫ rs,recordHealth i (rs k) ∂mu)=a) :
    ¬(∀ᵐ rs ∂mu,∃N,∀k≥N,¬Legitimate i (rs k).transaction.parentAfter) :=by
  intro he
  have hl : ∀ᵐ rs ∂mu,Tendsto (fun k=>recordHealth i (rs k)) atTop (𝓝 0) :=by
    filter_upwards [he] with rs hr
    obtain ⟨N,hN⟩:=hr
    have heq : (fun k=>recordHealth i (rs k))=ᶠ[atTop](fun _=>0) :=by
      filter_upwards [eventually_ge_atTop N] with k hk
      simp [recordHealth,hN k hk]
    exact tendsto_const_nhds.congr' heq.symm
  have hi:=tendsto_integral_of_dominated_convergence (fun _ : ℕ→ModeRecord n=>(1 : ℝ))
    (fun k=>((recordHealth_measurable i).comp (measurable_pi_apply k)).aestronglyMeasurable)
    (integrable_const (1 : ℝ)) (fun _=>ae_of_all _ (fun _=>recordHealth_norm_le i _)) hl
  have ht : Tendsto (fun _ : ℕ=>a) atTop (𝓝 0) :=by simpa only [Function.comp_apply,hm,integral_zero] using hi
  have hz : a=0:=tendsto_nhds_unique tendsto_const_nhds ht
  linarith

example (noise : PMF Bool) :
    ¬(∀ᵐ rs ∂muZeroFee noise,∃N,∀k≥N,¬Legitimate (3 : Fin 4) (rs k).transaction.parentAfter) :=by
  apply not_eventual_if_positive_mean 3 (muZeroFee noise) (2/5) (by norm_num)
  intro k
  have hh:=paid_actual_health_mean (3 : Fin 4) noise ⟨true,0⟩ (3/5) eps_ok (t:=0) initial.physical initial rfl k
  norm_num [repairChance] at hh
  exact hh

example (noise : PMF Bool) :
    ¬(∀ᵐ rs ∂recordPathLaw (3 : Fin 4) noise mech 0 (by norm_num) pi ⟨0,initial.physical,initial⟩,
      ∃N,∀k≥N,¬Legitimate (3 : Fin 4) (rs k).transaction.parentAfter) :=by
  apply not_eventual_if_positive_mean 3 _ 1 (by norm_num)
  exact (native_zero_fault_boundary 3 noise mech initial rfl).2.1

#print axioms common_actual_consumer
#print axioms not_eventual_if_positive_mean
#print axioms actual_total_health_time_bound
end
end IndependentFiniteResource
