import UEOT
namespace IndependentFundedProbe
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterFaultFinitePurposeProbe RegisterFaultFeedbackResource RegisterFaultFundedProbe
open scoped ENNReal NNReal
noncomputable section
local instance (n : ℕ) : MeasurableSpace (ModeRecord n) := ⊤
local instance (n : ℕ) : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩
theorem actual_tail {n : ℕ} (pre : List (ModeRecord n)) (rs : ℕ → ModeRecord n) (k : ℕ) :
    prepend pre rs (pre.length+k) = rs k := by
  induction pre with
  | nil => simp [prepend]
  | cons r pre ih =>
    rw [List.length_cons,show pre.length+1+k = pre.length+k+1 by omega]
    exact ih
example {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (price width : ℚ) (o : Organism n) (w : Raw N) :
    (wholeKernel i noise m epsilon he price width o w).map
      (fun rs k => rs ((completeTrace i m w o).length+k)) =
        futureKernel i noise m epsilon he price width o w := by
  change ((futureKernel i noise m epsilon he price width o w).map
    (prepend (completeTrace i m w o))).map _ = _
  rw [Measure.map_map (by fun_prop) (measurable_prepend _)]
  have h : (fun rs k => (prepend (completeTrace i m w o) rs) ((completeTrace i m w o).length+k)) =
      (id : (ℕ → ModeRecord n) → (ℕ → ModeRecord n)) := by
    funext rs k
    exact actual_tail _ _ _
  change (futureKernel i noise m epsilon he price width o w).map _ = _
  simp only [Function.comp_def,h,Measure.map_id]
example : RegisterFaultFundedProbe.PrefixFunded 0 1
    (completeTrace (0 : Fin 1) witnessMechanism witnessRaw witnessParent) ∧
    (witnessMechanism.writeCost : ℝ) ≤ listBalance 0 1
      (completeTrace (0 : Fin 1) witnessMechanism witnessRaw witnessParent) :=
  complete_training_funded 0 witnessMechanism witnessRaw witnessParent 1 0 (by norm_num [witnessMechanism]) (by norm_num)
example : select (1/2) (1/4) (actualData (0 : Fin 1) witnessMechanism (1/4) witnessRaw witnessParent) = .repair false :=
  funded_training_witness_accepts
example : ∀ᵐ rs ∂wholeKernel (N := 1) (0 : Fin 1) (PMF.uniformOfFintype Bool)
    witnessMechanism (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) (1/2) (1/4) witnessParent witnessRaw,
    UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceViable 0
      (fun t => idleInflow 1 (rs t)) (fun t => (rs t).transaction.expenditure) := by
  exact accepted_whole_path_funded 0 (PMF.uniformOfFintype Bool) witnessMechanism (1/4)
    (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) (1/2) (1/4) (by norm_num) (by norm_num) (1/2)
    (by constructor <;> norm_num) witnessRaw false witnessParent rfl
    funded_training_witness_accepts 1 0 (by norm_num [witnessMechanism]) (by norm_num)
example : IsProbabilityMeasure (jointLaw (N := 1) (0 : Fin 1)
    (PMF.uniformOfFintype Bool) witnessMechanism (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) (1/2) (1/4) witnessParent) := by
  infer_instance
#check funded_training_witness_mass
#print axioms write_marginal
#print axioms actualData_law
#print axioms complete_idle_primitive_readout
#print axioms complete_training_funded
#print axioms accepted_training_and_deployment
#print axioms accepted_whole_path_funded
#print axioms joint_resource_viable_on_repair
#print axioms actual_tail
end
end IndependentFundedProbe
