import UEOT
namespace IndependentBodyHitting
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.DynamicsKernel UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterRotatingBodySource RegisterRotatingBodyReturns RegisterBodyCanonicalPath RegisterBodyHittingSource
open scoped NNReal ENNReal Topology
noncomputable section
def seed : Organism 2:=⟨[true,true,false,true],fun j=>decide (j.val=1),true⟩
def goodSeed : Organism 2:=⟨[false,true],fun _=>true,true⟩
def noise : PMF Bool:=PMF.pure false
def eps : NNReal:=1/3
def fee : NNReal:=5/2
theorem he : eps≤1 :=by change (1/3 : ℝ)≤1;norm_num
theorem he_lt : eps<1 :=by change (1/3 : ℝ)<1;norm_num
theorem seed_bad : ¬BodyGoal true seed.physical :=by intro h;have hh:=h 0;norm_num [seed] at hh
theorem seed_good : BodyGoal true goodSeed.physical :=fun _=>rfl
theorem success_nn : (1-eps : NNReal)^2=4/9 :=by
  have hs : (1-eps : NNReal)=2/3 :=by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub he]
    norm_num [eps]
  rw [hs]
  apply NNReal.coe_injective
  norm_num
theorem success : successMass 2 eps=4/9 :=by
  unfold successMass
  rw [←ENNReal.coe_pow,success_nn]
  norm_num only [ENNReal.coe_div,ENNReal.coe_ofNat]
theorem inv_success : (4/9 : ℝ≥0∞)⁻¹=9/4 :=by
  have hrat : (((4/9 : NNReal) : ℝ≥0∞))=(4/9 : ℝ≥0∞) :=by norm_num only [ENNReal.coe_div,ENNReal.coe_ofNat]
  rw [←hrat,←ENNReal.coe_inv (by norm_num : (4/9 : NNReal)≠0)]
  have hi : (4/9 : NNReal)⁻¹=9/4 :=by apply NNReal.coe_injective;norm_num
  rw [hi]
  norm_num only [ENNReal.coe_div,ENNReal.coe_ofNat]
theorem failure : 1-successMass 2 eps=(5/9 : ℝ≥0∞) :=by
  unfold successMass
  rw [←ENNReal.coe_pow,success_nn,←ENNReal.coe_one,←ENNReal.coe_sub]
  have hh : (1-(4/9 : NNReal))=5/9 :=by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by exact_mod_cast (by norm_num : (4/9 : ℝ)≤1))]
    norm_num
  rw [hh]
  norm_num only [ENNReal.coe_div,ENNReal.coe_ofNat]
theorem actual_kernel : bodyKernel 2 true noise eps he seed.physical=
    (roundLaw 2 noise eps he).map (fun z=>(roundParent true fee z seed).physical) :=kernel_actual_round _ _ _ _ _ _
theorem actual_whole_path : (infiniteLaw 2 noise eps he).map (physicalPath true fee seed)=
    homTrajMeasure (Measure.dirac seed.physical) (bodyKernel 2 true noise eps he) :=actual_canonical_path_law _ _ _ _ _ _
theorem actual_mean : meanTau true fee noise eps he seed=9/4 :=by rw [actual_mean_exact,if_neg seed_bad,success,inv_success]
theorem original_consumer : meanTau true fee noise eps he seed≤9/4 :=by
  have h:=original_p_rec_04_actual true fee noise eps he_lt seed
  have hp : potential true seed.physical=1 :=by simp [potential,RegisterBodyHittingSource.target,seed_bad]
  rw [hp,success,one_div,inv_success] at h
  exact h
theorem actual_tail : infiniteLaw 2 noise eps he (survives true fee seed 6)=(5/9 : ℝ≥0∞)^6 :=by
  rw [actual_survival_mass true fee noise eps he seed seed_bad,failure]
theorem actual_stopping : IsStoppingTime (RegisterRotatingBodyP10.fullPast 2) (tau true fee seed) :=tau_stopping _ _ _
theorem actual_finite : ∀ᵐ w ∂infiniteLaw 2 noise eps he,tau true fee seed w<⊤ :=tau_finite_ae _ _ _ _ he_lt _
theorem actual_good_mean : meanTau true fee noise eps he goodSeed=0 :=mean_initial_goal _ _ _ _ _ _ seed_good
theorem actual_good_time (w : RoundStream 2) : tau true fee goodSeed w=0 :=tau_initial_goal _ _ _ seed_good _
theorem actual_total_fault_mean : meanTau true fee noise 1 (by norm_num) seed=∞ :=mean_total_fault (by decide) _ _ _ _ seed_bad
theorem actual_total_fault_time : ∀ᵐ w ∂infiniteLaw 2 noise 1 (by norm_num),tau true fee seed w=⊤ :=tau_total_fault (by decide) _ _ _ _ seed_bad
theorem actual_no_fault : meanTau true fee noise 0 (by norm_num) seed=1 :=by
  rw [actual_mean_exact,if_neg seed_bad]
  norm_num [successMass]
theorem actual_empty_body (o : Organism 0) : meanTau true fee noise 1 (by norm_num) o=0 :=mean_zero_body _ _ _ _ _ _

-- All labels lie in the actual purefalse source support. Round0/1 miss,
-- round2 succeeds. Inside round1, the body becomes good then faults again.
def word : RoundStream 2:=fun r j=>(decide (2≤r ∨ r%2≠j.val),false)
theorem actual_word_length : (recordsThrough true fee seed word 3).length=6 :=actual_prefix_length _ _ _ _ _
theorem actual_word_first_hit : tau true fee seed word=WithTop.some 3 :=by
  have hle : tau true fee seed word≤WithTop.some 3 :=by
    apply (tau_le_iff true fee seed word 3).mpr
    refine ⟨3,le_rfl,?_⟩
    change BodyGoal true (parentAt true fee seed word 3).physical
    rw [actual_macro_goal_iff]
    intro j
    norm_num [word]
  have hnot : ¬tau true fee seed word≤WithTop.some 2 :=by
    rw [tau_le_iff]
    rintro ⟨j,hj,hgoal⟩
    interval_cases j
    · exact seed_bad hgoal
    · change BodyGoal true (parentAt true fee seed word 1).physical at hgoal
      rw [actual_macro_goal_iff] at hgoal
      have hh:=hgoal 0
      norm_num [word] at hh
    · change BodyGoal true (parentAt true fee seed word 2).physical at hgoal
      rw [actual_macro_goal_iff] at hgoal
      have hh:=hgoal 1
      norm_num [word] at hh
  have ht : tau true fee seed word≠⊤ :=ne_of_lt (lt_of_le_of_lt hle (WithTop.coe_lt_top 3))
  obtain ⟨n,hn⟩:=WithTop.ne_top_iff_exists.mp ht
  rw [←hn] at hle hnot ⊢
  have hnle : n≤3:=WithTop.coe_le_coe.mp hle
  have hnn : ¬n≤2:=fun hh=>hnot (WithTop.coe_le_coe.mpr hh)
  have h3 : n=3:=by omega
  subst n
  rfl
theorem actual_word_value : tauValue true fee seed word=3 :=tauValue_of_finite _ _ _ _ _ actual_word_first_hit
theorem actual_word_cost : ((recordsThrough true fee seed word 3).map (fun r=>r.transaction.expenditure)).sum=5 :=by
  norm_num [recordsThrough,parentAt,roundParent,roundTrace,tracePorts,runPorts,transaction,word,seed,List.finRange,
    modeRecordStep,RegisterJointRecord.recordStep,execute_compiled,update,cost,fee,Function.update_apply,Fin.ext_iff]
theorem actual_intermediate_good : BodyGoal true
    (transaction (0 : Fin 2) true fee (parentAt true fee seed word 1) (word 1 0)).transaction.parentAfter.physical :=by
  intro j
  fin_cases j <;>
    norm_num [parentAt,roundParent,runPorts,transaction,word,seed,List.finRange,
      modeRecordStep,RegisterJointRecord.recordStep,execute_compiled,update,fee,Function.update_apply,Fin.ext_iff]
#print axioms actual_mean
#print axioms original_consumer
#print axioms actual_whole_path
#print axioms actual_word_first_hit
#print axioms actual_word_cost
#print axioms actual_intermediate_good
end
end IndependentBodyHitting
