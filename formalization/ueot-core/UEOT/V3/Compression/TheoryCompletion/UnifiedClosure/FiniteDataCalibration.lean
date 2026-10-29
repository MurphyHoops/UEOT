import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataNumericalBounds

/-! Four actual source probes, one fixed product experiment, and a selector
that uses only raw empirical means. No true parameter enters `estimate`.
The finite bit parsing performed by the executable remains a declared boundary. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCalibration
open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.BoundedLossSampling
open FiniteDataSource FiniteDataNumericalBounds VariableRegisteredSamples RowwiseProbeSampling
open scoped BigOperators Classical
noncomputable section
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Bool := ⊤

/-- Used by the common target normalization and full-path budget consumer. -/
theorem safePMF_tv (v w : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    tvDist (safePMF v hv).toMeasure (safePMF w hw).toMeasure = |v-w| := by
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp [Fin.sum_univ_succ]
  rw [abs_sub_comm w v]
  ring

def allocation (_ : Fin 4) : ℕ := 262144
abbrev Record := SampleCoordinate allocation → Bool

def bitOutcome (b : Bool) : ℝ := if b then 1 else 0

def probeStart (j : Fin 4) : State := if j.val = 1 then 1 else 0
def probeAction (j : Fin 4) : Action := if j.val < 2 then 0 else if j.val = 2 then 1 else 2
/-- Risk records safety, and each selection action records failure. -/
def probeReadout (j : Fin 4) (x : State) : Bool :=
  if j.val < 2 then decide (x.val ≠ 2) else decide (x.val = 2)

/-- The Bernoulli law is the pushforward of the SAME controlled source row. -/
def probeRow (p : Param) (hp : Admissible p) (j : Fin 4) : PMF Bool :=
  ((model p hp).transitionPMF (probeStart j) (probeAction j)).map (probeReadout j)

def trainingMeasure (p : Param) (hp : Admissible p) : Measure Record :=
  productRowLaw (probeRow p hp) allocation

instance trainingMeasure_probability (p : Param) (hp : Admissible p) :
    IsProbabilityMeasure (trainingMeasure p hp) := by
  unfold trainingMeasure
  infer_instance

def trainingPMF (p : Param) (hp : Admissible p) : PMF Record :=
  (trainingMeasure p hp).toPMF

@[simp] theorem trainingPMF_measure (p : Param) (hp : Admissible p) :
    (trainingPMF p hp).toMeasure = trainingMeasure p hp := by
  exact Measure.toPMF_toMeasure _

def empiricalMean (j : Fin 4) (omega : Record) : ℝ :=
  empiricalRisk bitOutcome (productRowSample (N := allocation) j) omega

/-- A count-only structured source estimate. It does not know the true source. -/
def estimate (omega : Record) : Param :=
  ⟨empiricalMean 0 omega, empiricalMean 1 omega, empiricalMean 2 omega, empiricalMean 3 omega⟩

@[simp] theorem estimate_probe (omega : Record) (j : Fin 4) :
    probeParameter (estimate omega) j = empiricalMean j omega := by
  fin_cases j <;> rfl

/-- Exact means of the four actual model pushforwards. -/
theorem probe_expectation (p : Param) (hp : Admissible p) (j : Fin 4) :
    trueRisk (probeRow p hp j).toMeasure bitOutcome = probeParameter p j := by
  unfold trueRisk
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, probeRow]
  rw [coverage_expectation_map]
  have h02 : (0 : State) ≠ 2 := by decide
  have h12 : (1 : State) ≠ 2 := by decide
  have h20 : (2 : Action) ≠ 0 := by decide
  have h21 : (2 : Action) ≠ 1 := by decide
  fin_cases j <;>
    norm_num [h02, h12, h20, h21, probeStart, probeAction, probeReadout, bitOutcome,
      Fin.sum_univ_succ, model, transition, probeParameter, Fin.reduceFinMk]

/-- The saved Bernoulli format has the exact registered parameter as true mass. -/
theorem probeRow_true (p : Param) (hp : Admissible p) (j : Fin 4) :
    (probeRow p hp j true).toReal = probeParameter p j := by
  have h := probe_expectation p hp j
  simpa [trueRisk, PMF.integral_eq_sum, bitOutcome, smul_eq_mul] using h

theorem probeRow_false (p : Param) (hp : Admissible p) (j : Fin 4) :
    (probeRow p hp j false).toReal = 1-probeParameter p j := by
  have h := coverage_sum_toReal (probeRow p hp j)
  rw [Fintype.sum_bool, probeRow_true] at h
  linarith

/-- The raw empirical parameter remains a probability, including zero counts. -/
theorem empiricalMean_mem (j : Fin 4) (omega : Record) :
    empiricalMean j omega ∈ Set.Icc (0 : ℝ) 1 := by
  have hbit (b : Bool) : bitOutcome b ∈ Set.Icc (0 : ℝ) 1 := by
    cases b <;> norm_num [bitOutcome]
  have hlow : 0 ≤ ∑ k : Fin (allocation j),
      bitOutcome (productRowSample j k omega) :=
    Finset.sum_nonneg fun k _ => (hbit _).1
  have hupp : (∑ k : Fin (allocation j), bitOutcome (productRowSample j k omega)) ≤
      ∑ _k : Fin (allocation j), (1 : ℝ) :=
    Finset.sum_le_sum fun k _ => (hbit _).2
  change 0 ≤ _ / (262144 : ℝ) ∧ _ / (262144 : ℝ) ≤ 1
  constructor
  · exact div_nonneg hlow (by norm_num)
  · apply (div_le_one (by norm_num : (0 : ℝ) < 262144)).mpr
    have hc : (∑ _k : Fin (allocation j), (1 : ℝ)) = 262144 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num [allocation]
    rw [hc] at hupp
    exact hupp

/-- The common calibration event is exactly simultaneous error of the raw estimate. -/
theorem good_event_eq (p : Param) (hp : Admissible p) (d : ℝ) :
    coordinateGood (probeRow p hp) (fun _ => bitOutcome)
      (productRowSample (N := allocation)) d =
      {omega | Good p (estimate omega) d} := by
  ext omega
  simp only [coordinateGood, Set.mem_ofPred_eq, Good, estimate_probe, probe_expectation]
  simp only [empiricalMean, abs_sub_comm]

/-- The registered scalar confidence is spent once for all four parameters
and all downstream registered horizons, without a post-selection fit premise. -/
theorem calibration_bad_le (p : Param) (hp : Admissible p) :
    (trainingMeasure p hp).real {omega | Good p (estimate omega) (1/250)}ᶜ ≤ 1/300 := by
  have h := product_probe_calibration (probeRow p hp) allocation (by intro j; norm_num [allocation])
    (fun _ => bitOutcome) (by intro j; exact measurable_of_finite _)
    (by intro j b; cases b <;> norm_num [bitOutcome]) (1/250) (by norm_num)
  rw [good_event_eq] at h
  exact h.2.trans ((min_le_right _ _).trans registeredScalarBudget_lt.le)

/-- Outside Good the program may reject zero-risk-count records; on Good,
Box positivity and the empirical probability range construct admissibility. -/
theorem estimate_admissible_on_good (p : Param) (hb : Box p) (omega : Record)
    (hg : Good p (estimate omega) (1/250)) : Admissible (estimate omega) := by
  have h0 := hg (0 : Fin 4)
  have h1 := hg (1 : Fin 4)
  change |p.r0 - empiricalMean 0 omega| ≤ 1/250 at h0
  change |p.r1 - empiricalMean 1 omega| ≤ 1/250 at h1
  have hl0 := (abs_le.mp h0).2
  have hl1 := (abs_le.mp h1).2
  exact ⟨by dsimp [estimate]; linarith [hb.1], (empiricalMean_mem 0 omega).2,
    by dsimp [estimate]; linarith [hb.2.2.1], (empiricalMean_mem 1 omega).2,
    (empiricalMean_mem 2 omega).1, (empiricalMean_mem 2 omega).2,
    (empiricalMean_mem 3 omega).1, (empiricalMean_mem 3 omega).2⟩

/-- The ideal count-only selector accepts both registered short horizons on
Good throughout the nonzero low-noise interval. No observed Good flag is used. -/
theorem low_noise_good_accepts_raw (p : Param) (hb : Box p)
    (he0 : p.e0 ≤ 1/200) (he1 : p.e1 ≤ 1/200) (omega : Record)
    (hg : Good p (estimate omega) (1/250)) :
    Admissible (estimate omega) ∧
      prepBudget 2 (max (estimate omega).e0 (estimate omega).e1)
        ((estimate omega).r0 + (estimate omega).r1) < 1/5 ∧
      prepBudget 10 (max (estimate omega).e0 (estimate omega).e1)
        ((estimate omega).r0 + (estimate omega).r1) < 1/5 := by
  have hg0 := hg (0 : Fin 4)
  have hg1 := hg (1 : Fin 4)
  have hg2 := hg (2 : Fin 4)
  have hg3 := hg (3 : Fin 4)
  change |p.r0 - (estimate omega).r0| ≤ 1/250 at hg0
  change |p.r1 - (estimate omega).r1| ≤ 1/250 at hg1
  change |p.e0 - (estimate omega).e0| ≤ 1/250 at hg2
  change |p.e1 - (estimate omega).e1| ≤ 1/250 at hg3
  rw [abs_sub_comm] at hg0 hg1 hg2 hg3
  exact ⟨estimate_admissible_on_good p hb omega hg,
    low_noise_good_accepts hb.1 hb.2.2.1 he0 he1 hg0 hg1 hg2 hg3⟩

/-- The three registrations belong to one finite product experiment. -/
def batchMeasure (p : Fin 3 → Param) (hp : ∀ i, Admissible (p i)) :
    Measure (Fin 3 → Record) :=
  Measure.pi (fun i => trainingMeasure (p i) (hp i))

instance batchMeasure_probability (p : Fin 3 → Param) (hp : ∀ i, Admissible (p i)) :
    IsProbabilityMeasure (batchMeasure p hp) := by
  unfold batchMeasure
  infer_instance

/-- The sum is for the three calibration events, not three deployment failures. -/
theorem batch_calibration_bad_le (p : Fin 3 → Param) (hp : ∀ i, Admissible (p i)) :
    (batchMeasure p hp).real
      {omega | ∀ i, Good (p i) (estimate (omega i)) (1/250)}ᶜ ≤ 1/100 := by
  have heq : {omega : Fin 3 → Record | ∀ i, Good (p i) (estimate (omega i)) (1/250)}ᶜ =
      ⋃ i : Fin 3, {omega | ¬Good (p i) (estimate (omega i)) (1/250)} := by
    ext omega
    simp
  rw [heq]
  apply (measureReal_iUnion_fintype_le _).trans
  have hrow : ∀ i : Fin 3, (batchMeasure p hp).real
      {omega | ¬Good (p i) (estimate (omega i)) (1/250)} ≤ 1/300 := by
    intro i
    have hm := (measurePreserving_eval (fun j => trainingMeasure (p j) (hp j)) i).map_eq
    have hbad : MeasurableSet {omega : Record | Good (p i) (estimate omega) (1/250)}ᶜ :=
      (Set.toFinite _).measurableSet
    have hread : (batchMeasure p hp).real
        {omega | ¬Good (p i) (estimate (omega i)) (1/250)} =
        (trainingMeasure (p i) (hp i)).real
          {omega | Good (p i) (estimate omega) (1/250)}ᶜ := by
      rw [← hm]
      simp only [Measure.real]
      rw [Measure.map_apply (measurable_pi_apply i) hbad]
      rfl
    rw [hread]
    exact calibration_bad_le (p i) (hp i)
  calc
    _ ≤ ∑ _i : Fin 3, (1/300 : ℝ) := Finset.sum_le_sum fun i _ => hrow i
    _ = 1/100 := by norm_num

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCalibration
