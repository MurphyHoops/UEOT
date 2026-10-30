import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundedInfinite

/-!
Original commitment: resource prerequisites must have actual source-derived boundaries, not merely sufficient accounting assumptions.
Existing result: g>=c funds the SAME ongoing idle-before-compiled-work protocol from any nonnegative finite shared reserve.
Premise tested: for that fixed real-parent protocol, show g<c cannot give almost-everywhere funding from any finite reserve.
Model/counter: SAME own-program source, original allowed compiler, hazard1/4/uniform labels; a legal fault-idle/repair-work prefix has positive mass.
Consumer: actual ongoing recordPathLaw fails original ResourceViable with positive probability; no claim about other policies or a.s. ruin.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundingObstruction
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
open RegisterActuatorPopulationScale RegisterPopulationFundedProtocol RegisterPopulationFundedInfinite
noncomputable section

def badRound (j : ℕ) : Round := ⟨j,.compiled,false,true,true,true⟩
def fixedPlan (j : ℕ) (_ : ℕ) : ℕ × Command := (j,.compiled)
def badRaw (N : ℕ) : Raw N := fun j => (j.2,true)

/-- Actual idle fault damages this retained parent's OWN actuator, so its
actual next compiler requests the paid write. No write/reset is installed. -/
theorem bad_pair_actual_account {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (j : ℕ)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s j=some p) (g R : ℝ) :
    balance R g (completeTrace i c s [badRound j])=R+g-(c : ℝ) ∧
    ∃ p', RegisterPopulationHistorySource.lookup (roundNext i c s (badRound j)) j=some p' := by
  let r0 := RegisterTimestampedBirthSource.step i ⟨p.organism.program,c⟩ {p with clock:=s.length} none false true
  have hmid : RegisterPopulationHistorySource.lookup (middle i c s (badRound j)) j=some r0.parentAfter :=
    (RegisterOwnProgramPopulation.retained_parent_identity i c s (idleRequest (badRound j)) p hp).1
  have ha : (workRequest i c s (badRound j)).action=some p.organism.program := by
    change (RegisterOwnProgramPopulation.compiledRequest i (middle i c s (badRound j)) j true true).action=_
    simp only [RegisterOwnProgramPopulation.compiledRequest,hmid]
    change (substrate i).execute p.organism.program (Function.update p.organism.physical i (!p.organism.program))=_
    simp [execute_compiled]
  have ht : RegisterOwnProgramPopulation.transaction i c (middle i c s (badRound j)) (workRequest i c s (badRound j))=
      some (RegisterTimestampedBirthSource.step i ⟨p.organism.program,c⟩
        {r0.parentAfter with clock:=(middle i c s (badRound j)).length} (some p.organism.program) true true) := by
    unfold RegisterOwnProgramPopulation.transaction
    rw [RegisterOwnProgramPopulation.mechanism_eq c _ _ _ hmid]
    change Option.map (fun p0 => RegisterTimestampedBirthSource.step i ⟨r0.parentAfter.organism.program,c⟩
      {p0 with clock:=(middle i c s (badRound j)).length} (workRequest i c s (badRound j)).action true true)
      (RegisterPopulationHistorySource.lookup (middle i c s (badRound j)) j)=_
    rw [hmid,Option.map_some,ha]
    rfl
  have hf : fee (RegisterOwnProgramPopulation.transaction i c (middle i c s (badRound j)) (workRequest i c s (badRound j)))=(c : ℝ) := by
    rw [ht]
    simp [fee,RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,cost]
  have hc : credit g (RegisterOwnProgramPopulation.transaction i c (middle i c s (badRound j)) (workRequest i c s (badRound j)))=0 := by
    rw [ht]
    simp [credit,RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep]
  have hi := (idle_account i c s (badRound j) g).1
  have hic : credit g (RegisterOwnProgramPopulation.transaction i c s (idleRequest (badRound j)))=g := by
    have h := (idle_account i c s (badRound j) g).2
    change credit g (RegisterOwnProgramPopulation.transaction i c s (idleRequest (badRound j)))=
      if (RegisterPopulationHistorySource.lookup s j).isSome then g else 0 at h
    simpa only [hp,Option.isSome_some,if_true] using h
  constructor
  · change balance R g [RegisterOwnProgramPopulation.transaction i c s (idleRequest (badRound j)),
      RegisterOwnProgramPopulation.transaction i c (middle i c s (badRound j)) (workRequest i c s (badRound j))]=_
    simp only [balance_cons,balance_nil,hi,hic,hf,hc]
    ring
  · exact ⟨_,(RegisterOwnProgramPopulation.retained_parent_identity i c _ (workRequest i c s (badRound j)) r0.parentAfter hmid).1⟩

/-- Every repeated legal source pair really pays c and credits only g. The
same parent remains present; all new children and failed allocations remain. -/
theorem repeated_bad_balance {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (j : ℕ)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s j=some p) (g R : ℝ) (N : ℕ) :
    balance R g (completeTrace i c s (List.replicate N (badRound j)))=R+(N : ℝ)*(g-c) := by
  induction N generalizing s p R with
  | zero => simp [completeTrace,requests,transactionTrace]
  | succ N ih =>
    obtain ⟨hpair,p',hp'⟩ := bad_pair_actual_account i c s j p hp g R
    change balance R g (_ :: _ :: completeTrace i c (roundNext i c s (badRound j)) (List.replicate N (badRound j)))=_
    rw [balance_cons,balance_cons,ih _ p' hp']
    have hh : R+credit g (RegisterOwnProgramPopulation.transaction i c s (idleRequest (badRound j)))-
        fee (RegisterOwnProgramPopulation.transaction i c s (idleRequest (badRound j)))+
        credit g (RegisterOwnProgramPopulation.transaction i c (middle i c s (badRound j)) (workRequest i c s (badRound j)))-
        fee (RegisterOwnProgramPopulation.transaction i c (middle i c s (badRound j)) (workRequest i c s (badRound j)))=R+g-c := hpair
    calc
      _ = (R+g-c)+(N : ℝ)*(g-c) := congrArg (fun v => v+(N : ℝ)*(g-c)) hh
      _ = _ := by push_cast; ring

theorem registered_bad_rounds (j N : ℕ) :
    registeredRounds (prefixPlan N (fixedPlan j)) (badRaw N)=List.replicate N (badRound j) := by
  simp [registeredRounds,prefixPlan,fixedPlan,badRaw,badRound,List.ofFn_const]

/-- Exact legal complete raw prefix mass. Both draws and true labels of each
round remain in the original source: (1/4*1/2)*(3/4*1/2)=3/64. -/
theorem bad_finite_mass (N : ℕ) :
    (sourceLaw (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) N).real {badRaw N}=
      (3/64 : ℝ)^N := by
  rw [Measure.real,sourceLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fintype.prod_prod_type,Fintype.prod_bool,badRaw,
    RegisterFaultFinitePurposeProbe.primitiveLaw_apply,ENNReal.toReal_mul,RegisterFaultControlModel.modeLaw,
    FiniteProbabilityRow.ofRealRow_apply_toReal,RegisterFaultControlModel.modeProbability,
    RegisterFaultControlModel.repairChance,PMF.uniformOfFintype_apply]
  rw [div_pow]

theorem bad_infinite_cylinder_mass (N : ℕ) :
    (infiniteSource (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1))).real
      {w | prefixRaw N w=badRaw N}=(3/64 : ℝ)^N := by
  have h := congrArg (fun mu : Measure (Raw N) => mu {badRaw N})
    (infinite_raw_prefix_law (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) N)
  rw [Measure.map_apply (measurable_prefixRaw N) (measurableSet_singleton _)] at h
  exact (congrArg ENNReal.toReal h).trans (bad_finite_mass N)

/-- Minimal pure accounting bridge from literal complete record prefixes to
the original cumulative ResourceViable consumer. No funding assumption. -/
theorem prefix_cumulative_eq_balance {n : ℕ} (R g : ℝ) (ts : ℕ → Option (ClockedRecord n)) (k : ℕ) :
    cumulativeResourceBalance R (fun t => credit g (ts t)) (fun t => fee (ts t)) k=
      balance R g (List.ofFn (fun j : Fin k => ts j)) := by
  symm
  induction k with
  | zero => simp [cumulativeResourceBalance]
  | succ k ih =>
    rw [List.ofFn_succ',List.concat_eq_append]
    change (List.foldl (fun r t => r+credit g t-fee t) R (List.ofFn (fun j : Fin k => ts j)++[ts k]))=_
    rw [List.foldl_append]
    change balance R g (List.ofFn (fun j : Fin k => ts j))+credit g (ts k)-fee (ts k)=_
    rw [ih]
    simp only [cumulativeResourceBalance,Finset.sum_range_succ]
    ring

/-- The SAME actual infinite protocol has the computed bad prefix balance.
Nothing is conditioned away; this implication is used on its positive-mass
cylinder in the original complete source. -/
theorem bad_actual_prefix_balance {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (j : ℕ)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s j=some p)
    (w : InfiniteRaw) (N : ℕ) (hw : prefixRaw N w=badRaw N) (g R : ℝ) :
    cumulativeResourceBalance R
      (fun t => credit g (RegisterPopulationFundedInfinite.recordAt i c s (fixedPlan j) w t))
      (fun t => fee (RegisterPopulationFundedInfinite.recordAt i c s (fixedPlan j) w t)) (2*N)=R+(N : ℝ)*(g-c) := by
  rw [prefix_cumulative_eq_balance,actual_record_finite_prefix,hw,registered_bad_rounds]
  exact repeated_bad_balance i c s j p hp g R N

theorem bad_prefix_not_viable {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (j : ℕ)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s j=some p)
    (w : InfiniteRaw) (N : ℕ) (hw : prefixRaw N w=badRaw N) (g R : ℝ) (hneg : R+(N : ℝ)*(g-c)<0) :
    ¬ ResourceViable R
      (fun t => credit g (RegisterPopulationFundedInfinite.recordAt i c s (fixedPlan j) w t))
      (fun t => fee (RegisterPopulationFundedInfinite.recordAt i c s (fixedPlan j) w t)) := by
  intro h
  have hk := h (2*N)
  rw [bad_actual_prefix_balance i c s j p hp w N hw] at hk
  linarith

local instance {d : ℕ} : MeasurableSpace (Option (ClockedRecord d)) := ⊤

/-- Strict obstruction for the SAME fixed-parent ongoing compiler under its
original raw law. For ANY finite reserve, sub-cost valid-idle credit is not
almost-everywhere sufficient. This is NOT no-go for every other controller,
NOT an almost-sure-ruin theorem and NOT an expected-drift argument. -/
theorem subcost_fixed_protocol_not_ae_viable {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (j : ℕ)
    (p : ClockedOrganism n) (hp : RegisterPopulationHistorySource.lookup s j=some p)
    (g R : ℝ) (_hg0 : 0≤g) (hgc : g<(c : ℝ)) :
    ¬ ∀ᵐ ts ∂ RegisterPopulationFundedInfinite.recordPathLaw i c s (fixedPlan j)
        (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)),
      ResourceViable R (fun t => credit g (ts t)) (fun t => fee (ts t)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (R/((c : ℝ)-g))
  have hneg : R+(N : ℝ)*(g-c)<0 := by
    have hh := (div_lt_iff₀ (sub_pos.mpr hgc)).mp hN
    nlinarith
  intro h
  have ha := ae_of_ae_map (RegisterPopulationFundedInfinite.measurable_recordStream i c s (fixedPlan j)).aemeasurable h
  have hz : (infiniteSource (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)))
      {w | prefixRaw N w=badRaw N}=0 := by
    apply measure_mono_null _ (ae_iff.mp ha)
    intro w hw
    exact bad_prefix_not_viable i c s j p hp w N hw g R hneg
  have hm := bad_infinite_cylinder_mass N
  have hpos : 0<(3/64 : ℝ)^N := pow_pos (by norm_num) N
  rw [← hm,Measure.real,hz,ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundingObstruction
