import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SISCRowwiseProbeCalibration

/-!
# Nonempty SISC rowwise experiment and an actual model-mismatch boundary

Two probes use 128 and 256 separate units from the same declared point-mass
post-action source. The two registered candidate predictions are 0 and 1.
Both N3 resolution and N6 audited-source recovery consume this actual product
experiment. It is a formal finite example, not an empirical experiment.

The negative control changes the declared source kernel to the opposite
point mass while retaining the true data law. Exact concentration about the
data mean then fails to calibrate the declared kernel risk.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SISCRowwiseProbeWitness

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open RowwiseProbeSampling VariableRegisteredSamples
open scoped BigOperators Classical

noncomputable section

local instance : MeasurableSpace Bool := ⊤

def pointKernel (next : Bool) : FiniteControlledStochasticKernel Bool Unit where
  mass := fun _ _ y => if y = next then 1 else 0
  nonneg := by intro _ _ y; split <;> norm_num
  normalized := by intro _ _; cases next <;> simp

def read (y : Bool) (_j : Bool) : ℝ := if y then 1 else 0

def protocol (next : Bool) : RegisteredCausalCandidateProtocol Bool Unit Bool Bool where
  kernel := pointKernel next
  source := false
  action := ()
  read := read
  prediction := fun c _ => if c then 1 else 0
  registered := Finset.univ
  causal := fun _ => True
  tolerance := 1 / 2
  interval := fun _ => {
    estimate := 0
    statisticalRadius := 0
    driftRadius := 0
    statisticalRadius_nonneg := le_refl 0
    driftRadius_nonneg := le_refl 0 }
  observed_nonempty := ⟨false⟩

def allocation (j : Bool) : ℕ := if j then 256 else 128

theorem allocation_pos (j : Bool) : 0 < allocation j := by
  cases j <;> norm_num [allocation]

/-- Each group samples the same real action's next-state law and reads only
its own registered coordinate. No joint counterfactual unit is fabricated. -/
def row (_j : Bool) : PMF Bool := PMF.pure false

abbrev SampleSpace := SampleCoordinate allocation → Bool

def trainingLaw : Measure SampleSpace := productRowLaw row allocation

instance trainingLaw_isProbability : IsProbabilityMeasure trainingLaw := by
  unfold trainingLaw
  infer_instance

def sample (j : Bool) (k : Fin (allocation j)) (ω : SampleSpace) : Bool :=
  productRowSample j k ω

theorem sample_measurable (j : Bool) (k : Fin (allocation j)) :
    Measurable (sample j k) := productRowSample_measurable j k

theorem sample_independent (j : Bool) : iIndepFun (sample j) trainingLaw :=
  productRowSample_independent row allocation j

theorem sample_law (j : Bool) (k : Fin (allocation j)) :
    trainingLaw.map (sample j k) = (row j).toMeasure :=
  productRowSample_law row allocation j k

theorem actual_mean_zero (j : Bool) :
    trueRisk (row j).toMeasure (fun y => read y j) = 0 := by
  simp [row, trueRisk, PMF.toMeasure_pure, read]

theorem actual_model_match : RowwiseCoordinateLawMatchesKernel (protocol false) row := by
  intro j
  change trueRisk (row j).toMeasure (fun y => read y j) = _
  rw [actual_mean_zero]
  simp [protocol, pointKernel, read]

theorem actual_registered_risks :
    registeredCandidateRisk (protocol false) false = 0 ∧
      registeredCandidateRisk (protocol false) true = 2 := by
  norm_num [registeredCandidateRisk, protocol, pointKernel, read]

theorem nonempty_unequal_experiment :
    Fintype.card Bool = 2 ∧ allocation false = 128 ∧ allocation true = 256 ∧
      allocation false ≠ allocation true := by
  norm_num [allocation]

/-- The exact scalar budget has one contribution per probe. -/
theorem actual_scalar_budget :
    scalarBudget allocation (1 / 8) = 2 * exp (-4) + 2 * exp (-8) := by
  norm_num [scalarBudget, allocation]
  ring

/-- A conservative exact nonvacuity certificate, requiring no decimal
approximation of either exponential. -/
theorem actual_scalar_budget_nonvacuous :
    scalarBudget allocation (1 / 8) ≤ (28 / 45 : ℝ) := by
  have h4 : (5 : ℝ) ≤ exp 4 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  have h8 : (9 : ℝ) ≤ exp 8 := by
    have h := Real.add_one_le_exp (8 : ℝ)
    linarith
  have hi4 : exp (-4) ≤ (1 / 5 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h4
  have hi8 : exp (-8) ≤ (1 / 9 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h8
  rw [actual_scalar_budget]
  linarith

/-- Actual N3 decision power for a nonempty, unequal-allocation product law. -/
theorem actual_product_candidate_power :
    trainingLaw.real {ω | resolveRegisteredCandidates
      (rowwiseCoordinateProtocol (protocol false) sample ω (1 / 8) (by norm_num)) ≠
        .unique false} ≤ min 1 (scalarBudget allocation (1 / 8)) := by
  apply measure_rowwise_failure_to_identify_le allocation allocation_pos
    (protocol false) trainingLaw row sample
  · intro j
    exact measurable_of_finite _
  · intro j y
    cases y <;> norm_num [protocol, read]
  · exact sample_measurable
  · exact sample_independent
  · exact sample_law
  · exact actual_model_match
  · simp [protocol]
  · trivial
  · rw [actual_registered_risks.1]
    norm_num [protocol]
  · intro d _ _ hd
    cases d
    · exact False.elim (hd rfl)
    · rw [actual_registered_risks.2]
      norm_num [protocol]

def audit : FiniteInterventionTransferAudit Bool Unit Bool where
  registered := Finset.univ
  authenticatedTransfer := fun _ _ => True
  referenceResponse := fun c _ => if c then 1 else 0
  observedResponse := fun _ _ => 0
  tolerance := 1 / 8

/-- Authentication is explicit in this toy audit; fitting alone does not
construct authentication or a genealogical relation. -/
theorem actual_product_audit_power :
    trainingLaw.real {ω | auditedSourceCandidates
      (rowwiseInterventionAudit audit (fun j y => read y j) sample ω (1 / 8)) () ≠
        {false}} ≤ min 1 (scalarBudget allocation (1 / 8)) := by
  apply measure_rowwise_audited_source_failure_le allocation allocation_pos
    audit trainingLaw row (fun j y => read y j) sample
  · intro j
    exact measurable_of_finite _
  · intro j y
    cases y <;> norm_num [read]
  · exact sample_measurable
  · exact sample_independent
  · exact sample_law
  · norm_num
  · simp [audit]
  · trivial
  · intro j
    simpa [audit] using actual_mean_zero j
  · intro d hd
    cases d
    · exact False.elim (hd rfl)
    · exact ⟨false, by norm_num [audit]⟩

/-- Concentration cannot establish the missing equality with a different
source kernel: the data mean is 0 but the declared kernel mean is 1. -/
theorem actual_data_fail_wrong_model_match :
    ¬ RowwiseCoordinateLawMatchesKernel (protocol true) row := by
  intro h
  have hm := h false
  change trueRisk (row false).toMeasure (fun y => read y false) = _ at hm
  rw [actual_mean_zero] at hm
  norm_num [protocol, pointKernel, read] at hm

def zeroRecord : SampleSpace := fun _ => false

theorem zero_record_empirical_mean (j : Bool) :
    empiricalRisk (fun y => read y j) (sample j) zeroRecord = 0 := by
  simp [empiricalRisk, read, sample, productRowSample, zeroRecord]

theorem zero_record_is_actual_good :
    zeroRecord ∈ coordinateGood row (fun j y => read y j) sample 0 := by
  intro j
  rw [zero_record_empirical_mean, actual_mean_zero]
  norm_num

/-- Even exact data-mean accuracy does not calibrate the wrong kernel.
This is a concrete failed conclusion, not merely absence of hMean. -/
theorem exact_data_good_does_not_calibrate_wrong_kernel :
    ¬ (rowwiseCoordinateProtocol (protocol true) sample zeroRecord 0
      (by norm_num)).Calibrated := by
  intro hcal
  have h := hcal false (by simp [rowwiseCoordinateProtocol, protocol])
  change |rowwiseCoordinateRisk (protocol true) sample zeroRecord false -
    registeredCandidateRisk (protocol true) false| ≤
      (Fintype.card Bool : ℝ) * 0 + 0 at h
  have hemp : rowwiseCoordinateRisk (protocol true) sample zeroRecord false = 0 := by
    simp only [rowwiseCoordinateRisk]
    change (∑ j : Bool, |empiricalRisk (fun y => read y j) (sample j) zeroRecord - 0|) = 0
    simp [zero_record_empirical_mean]
  rw [hemp] at h
  norm_num [registeredCandidateRisk, protocol, pointKernel, read] at h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SISCRowwiseProbeWitness
