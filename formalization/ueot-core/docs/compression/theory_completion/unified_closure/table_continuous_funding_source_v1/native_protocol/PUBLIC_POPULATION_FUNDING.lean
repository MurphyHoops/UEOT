import UEOT
namespace IndependentOngoingFunding
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterTimestampedBirthSource (ClockedRecord)
open RegisterActuatorScaleSource RegisterActuatorPopulationScale RegisterPopulationFundedProtocol
open RegisterPopulationFundedInfinite

example : prefixPlan 2 alternatingPlan=witnessPlan := by funext j; fin_cases j <;> rfl
-- SAME frozen finite formal word is the actual prefix of a genuine continuing process.
example (w : InfiniteRaw) (hw : prefixRaw 2 w=witnessRaw) :
    List.ofFn (fun j : Fin 4 => RegisterPopulationFundedInfinite.recordAt (0 : Fin 1) 1
      RegisterOwnProgramPopulation.witnessInitial alternatingPlan w j)=witnessTrace := by
  change List.ofFn (fun j : Fin (2*2) => RegisterPopulationFundedInfinite.recordAt (0 : Fin 1) 1
    RegisterOwnProgramPopulation.witnessInitial alternatingPlan w j)=_
  rw [actual_record_finite_prefix,hw]
  have hp : prefixPlan 2 alternatingPlan=witnessPlan := by funext j; fin_cases j <;> rfl
  rw [hp]
  rfl
-- Prefix cylinder has positive mass, NOT the singleton of an infinite word.
example : (infiniteSource (PMF.uniformOfFintype Bool) (1/4)
    (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1))).real {w | prefixRaw 2 w=witnessRaw}=9/4096 := by
  have h := congrArg (fun mu : Measure (Raw 2) => mu {witnessRaw})
    (infinite_raw_prefix_law (PMF.uniformOfFintype Bool) (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) 2)
  rw [Measure.map_apply (measurable_prefixRaw 2) (measurableSet_singleton _)] at h
  have hh := witness_mass
  exact (congrArg ENNReal.toReal h).trans hh
-- BOTH actual transactions exist at every ongoing stage, for EVERY raw realization.
example (w : InfiniteRaw) (k : ℕ) := alternating_actual_work_forever w k
-- Same unknown-parameter source, arbitrary budget, not replaced samples.
example {n : ℕ} (i : Fin n) (c : NNReal) (s : RegisterPopulationHistorySource.Store n)
    (plan : ℕ → ℕ × Command) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) :=
  recordPath_prefix_law i c s plan noise epsilon he N
example (w : InfiniteRaw) : ResourceViable 0
    (fun t => credit 1 (RegisterPopulationFundedInfinite.recordAt (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial alternatingPlan w t))
    (fun t => fee (RegisterPopulationFundedInfinite.recordAt (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial alternatingPlan w t)) :=
  every_actual_infinite_prefix_funded _ _ _ _ _ _ _ (by norm_num) (by norm_num)
-- TRUE infinite source law consumer at nonzero hazard; no stop/padding field.
example := actual_infinite_law_resource_viable (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial alternatingPlan
  (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) 1 0 (by norm_num) (by norm_num)
-- Fine port1 realization has SAME infinite complete journal law and funding.
example (hidden : Bool) := infinite_journal_law_transport (1 : Fin 3) 1 (witnessStore hidden) alternatingPlan
  (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1))
example (hidden : Bool) := actual_infinite_law_resource_viable (1 : Fin 3) 1 (witnessStore hidden) alternatingPlan
  (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) 1 0 (by norm_num) (by norm_num)
#print axioms infinite_raw_prefix_law
#print axioms actual_store_finite_prefix
#print axioms actual_record_finite_prefix
#print axioms source_actual_prefix_law
#print axioms recordPath_prefix_law
#print axioms actual_infinite_law_resource_viable
#print axioms retained_address_exists
#print axioms alternating_actual_work_forever
#print axioms infinite_journal_law_transport

end IndependentOngoingFunding

namespace IndependentFundingObstruction
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterTimestampedBirthSource (ClockedOrganism)
open RegisterActuatorScaleSource RegisterActuatorPopulationScale RegisterPopulationFundedProtocol RegisterPopulationFundedInfinite
open RegisterPopulationFundingObstruction

def p0 : ClockedOrganism 1 := ⟨⟨[],fun _ => false,false⟩,[(0,false)],0⟩
example : RegisterPopulationHistorySource.lookup RegisterOwnProgramPopulation.witnessInitial 0=some p0 := rfl
-- Actual source-derived six-record budget and exact strictly positive complete cylinder mass.
example (w : InfiniteRaw) (hw : prefixRaw 3 w=badRaw 3) :
    cumulativeResourceBalance 1
      (fun t => credit (1/2) (RegisterPopulationFundedInfinite.recordAt (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial (fixedPlan 0) w t))
      (fun t => fee (RegisterPopulationFundedInfinite.recordAt (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial (fixedPlan 0) w t)) 6= -(1/2) := by
  have h := bad_actual_prefix_balance (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial 0 p0 rfl w 3 hw (1/2) 1
  norm_num at h
  exact h
example : (infiniteSource (PMF.uniformOfFintype Bool) (1/4)
    (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1))).real {w | prefixRaw 3 w=badRaw 3}=27/262144 := by
  rw [bad_infinite_cylinder_mass]
  norm_num
example (R : ℝ) : ¬ ∀ᵐ ts ∂ (RegisterPopulationFundedInfinite.recordPathLaw (0 : Fin 1) 1
    RegisterOwnProgramPopulation.witnessInitial (fixedPlan 0) (PMF.uniformOfFintype Bool) (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1))),
    ResourceViable R (fun t => credit (3/4) (ts t)) (fun t => fee (ts t)) :=
  subcost_fixed_protocol_not_ae_viable _ _ _ _ p0 rfl (3/4) R (by norm_num) (by norm_num)
-- EXACT boundary g=c consumes original positive ongoing theorem, same fixed controller/source.
example := actual_infinite_law_resource_viable (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial (fixedPlan 0)
  (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) 1 0 (by norm_num) (by norm_num)
-- Strict boundary also holds on SAME n3/port1 actual parent, both passive hidden choices.
example (hidden : Bool) (R : ℝ) : ¬ ∀ᵐ ts ∂ (RegisterPopulationFundedInfinite.recordPathLaw (1 : Fin 3) 1
    (witnessStore hidden) (fixedPlan 0) (PMF.uniformOfFintype Bool) (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1))),
    ResourceViable R (fun t => credit (1/2) (ts t)) (fun t => fee (ts t)) := by
  apply subcost_fixed_protocol_not_ae_viable _ _ _ _ (embedClocked hidden p0) rfl (1/2) R <;> norm_num
-- Empty negative-prefix boundary: cylinder0=univ, not claimed to damage a nonnegative wallet.
example : (sourceLaw (PMF.uniformOfFintype Bool) (1/4)
    (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) 0).real {badRaw 0}=1 := by
  rw [bad_finite_mass]; norm_num
#print axioms bad_pair_actual_account
#print axioms repeated_bad_balance
#print axioms bad_finite_mass
#print axioms bad_infinite_cylinder_mass
#print axioms bad_actual_prefix_balance
#print axioms bad_prefix_not_viable
#print axioms subcost_fixed_protocol_not_ae_viable

end IndependentFundingObstruction

namespace IndependentAllInvalidScheduleBoundary
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory
open RegisterTimestampedBirthSource (ClockedRecord)
open RegisterPopulationHistorySource (Store)
open RegisterPopulationFundedProtocol RegisterPopulationFundedInfinite
noncomputable section
-- This fixed schedule always requests the current fresh (empty) allocator
-- address. It cannot pay fees or receive fictional supply; thus subcost is
-- NOT a theorem that every other controller is impossible.
def emptySlotPlan {n : ℕ} (s : Store n) (k : ℕ) : ℕ × Command :=
  (s.length+2*k,.compiled)
theorem actual_invalid_pairs {n : ℕ} (i : Fin n) (c : NNReal)
    (s : Store n) (w : InfiniteRaw) (k : ℕ) :
    RegisterPopulationFundedInfinite.recordAt i c s (emptySlotPlan s) w (2*k)=none ∧
    RegisterPopulationFundedInfinite.recordAt i c s (emptySlotPlan s) w (2*k+1)=none := by
  let u := stageStore i c s (emptySlotPlan s) w k
  let r := roundAt (emptySlotPlan s) w k
  have hp : RegisterPopulationHistorySource.lookup u r.parent=none := by
    change RegisterPopulationHistorySource.lookup
      (stageStore i c s (emptySlotPlan s) w k) (s.length+2*k)=none
    rw [← stage_length i c s (emptySlotPlan s) w k]
    simp [RegisterPopulationHistorySource.lookup]
  have hm := invalid_stays_invalid i c u r hp
  rw [actual_even,actual_odd]
  change RegisterOwnProgramPopulation.transaction i c u (idleRequest r)=none ∧
    RegisterOwnProgramPopulation.transaction i c (middle i c u r) (workRequest i c u r)=none
  constructor
  · simp [RegisterOwnProgramPopulation.transaction,RegisterPopulationHistorySource.transaction,idleRequest,hp]
  · simp [RegisterOwnProgramPopulation.transaction,RegisterPopulationHistorySource.transaction,workRequest,hm]
theorem actual_invalid_all_times {n : ℕ} (i : Fin n) (c : NNReal)
    (s : Store n) (w : InfiniteRaw) (t : ℕ) :
    RegisterPopulationFundedInfinite.recordAt i c s (emptySlotPlan s) w t=none := by
  have h := actual_invalid_pairs i c s w (t/2)
  by_cases ht : t%2=0
  · have he : 2*(t/2)=t := by omega
    simpa only [he] using h.1
  · have he : 2*(t/2)+1=t := by omega
    simpa only [he] using h.2
-- Same full source, cost1, ZERO supply and a genuine nonempty initial store.
-- Ledger is viable because this particular different schedule never has an
-- addressed transaction. All failed ticks/empty allocations still happen.
example (w : InfiniteRaw) : ResourceViable 0
    (fun t => credit 0 (RegisterPopulationFundedInfinite.recordAt (0 : Fin 1) 1
      RegisterOwnProgramPopulation.witnessInitial (emptySlotPlan RegisterOwnProgramPopulation.witnessInitial) w t))
    (fun t => fee (RegisterPopulationFundedInfinite.recordAt (0 : Fin 1) 1
      RegisterOwnProgramPopulation.witnessInitial (emptySlotPlan RegisterOwnProgramPopulation.witnessInitial) w t)) := by
  intro k
  simp only [actual_invalid_all_times,credit,fee,cumulativeResourceBalance]
  simp
#print axioms actual_invalid_pairs
#print axioms actual_invalid_all_times
end
end IndependentAllInvalidScheduleBoundary
