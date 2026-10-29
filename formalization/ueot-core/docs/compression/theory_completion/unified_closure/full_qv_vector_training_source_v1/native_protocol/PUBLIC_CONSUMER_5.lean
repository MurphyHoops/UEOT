import UEOT
open MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterPopulationJournalLearning
noncomputable section
local instance : MeasurableSpace Observation := ⊤
local instance : MeasurableSingletonClass Observation := ⟨fun _ => trivial⟩
-- Distinct events with the same ID are intentionally NOT identified as events.
example {N : ℕ} (data : Data N) (hmaj : N < 2 * score data (witnessKey 0)) :
    witnessKey (select [0,0,1,2,3] witnessKey 3 data) = witnessKey 0 :=
  select_eq_class _ _ _ _ (by simp) _ hmaj
-- Correct probability is a lower bound; confuser may also hit the true class.
example (confuser : PMF WitnessEvent) :
    (3/4 : ℝ) ≤ (sensorLaw (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) confuser witnessKey 0).toMeasure.real {witnessKey 0} := by
  have h := actual_correct_read_probability_ge (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) confuser witnessKey 0
  norm_num [RegisterFaultControlModel.repairChance] at h
  linarith
-- Both parent names are the actual original journal, arbitrary deterministic
-- estimators cannot be jointly consistent under the two complete equal laws.
example (estimate : ∀ N, Data N → Observation) :
    ¬ (Tendsto (fun N => (observedLaw (1/2) (by norm_num) (PMF.pure (1 : WitnessEvent)) witnessKey 0 N).real
          {data | estimate N data ≠ witnessParent 0}) atTop (𝓝 0) ∧
        Tendsto (fun N => (observedLaw (1/2) (by norm_num) (PMF.pure (0 : WitnessEvent)) witnessKey 1 N).real
          {data | estimate N data ≠ witnessParent 1}) atTop (𝓝 0)) :=
  half_noise_no_joint_consistency witnessKey 0 1 _ _
    (two_founder_half_noise_obstruction 0 (fun _ => none)).2.1 estimate
example (N : ℕ) (confuser : PMF WitnessEvent) :
    (rawLaw (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) confuser N).real
      {omega | witnessParent (select (List.finRange 4) witnessKey 3 (readout witnessKey 0 omega)) ≠ witnessParent 0}
      ≤ Real.exp (-(N : ℝ)/8) := two_founder_parent_risk_le confuser 0 3 N
#print axioms actual_journal_discovery_consumes_p12
#print axioms actual_parent_risk_le
#print axioms half_noise_no_joint_consistency
#print axioms two_founder_half_noise_obstruction
end
