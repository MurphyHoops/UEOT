import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCertificate
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentJoint

/-! The actual finite training-selection-deployment experiment. Rejected data
are masked out of the failure event; a mathematical fallback only totalizes the
PMF and does not instruct the executable to deploy rejected records. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataJoint
open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteDataSource FiniteDataCalibration FiniteDataNumericalBounds
open SameSourceFiniteWindowCheck SameSourceKilledPathCheck
open scoped BigOperators Classical
noncomputable section
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Bool := ⊤

abbrev Candidate := {p : Param // Admissible p}

def fallback : Candidate := ⟨⟨3/4,1/4,0,0⟩, by norm_num [Admissible]⟩

/-- The raw empirical estimate is used whenever valid. Good is never inspected. -/
def selectedEstimate (omega : Record) : Candidate :=
  if he : Admissible (estimate omega) then ⟨estimate omega,he⟩ else fallback

def Accept (omega : Record) (T : ℕ) : Prop :=
  Admissible (estimate omega) ∧ budget (estimate omega) T ≤ 1/5

def failureEvent (T : ℕ) : Set (CausalHistory State State T) :=
  {h | ¬stateSurvives FiniteDataConditioned.safe T h}

def acceptedFailure (omega : Record) (T : ℕ) : Set (CausalHistory State State T) :=
  if Accept omega T then failureEvent T else ∅

def jointLaw (p : Param) (hp : Admissible p) (T : ℕ) :
    PMF (Record × CausalHistory State State T) :=
  selectedTrainingDeployment (trainingPMF p hp) selectedEstimate
    (fun s => deployed p hp s.val s.property T)

/-- Safety of the comparison law comes from actual same-source conditioning. -/
theorem target_failure_zero (p : Param) (hp : Admissible p) (T : ℕ) :
    (target p hp T).toMeasure.real (failureEvent T) = 0 := by
  have hzero : (target p hp T).toMeasure (failureEvent T) = 0 := by
    apply ((target p hp T).toMeasure_apply_eq_zero_iff
      (Set.toFinite _).measurableSet).mpr
    apply Set.disjoint_left.mpr
    intro h hsupp hfail
    rw [FiniteDataConditioned.target_eq_actual] at hsupp
    have hs := actual_conditioned_prefix_support (model p hp) observe baseline initial
      FiniteDataConditioned.safe T 0 (FiniteDataConditioned.source_positive p hp T) hsupp
    exact hfail hs
  simp only [Measure.real, hzero, ENNReal.toReal_zero]

/-- The complete-path risk bound is for this selected estimator's actual
noisy-preparation experiment, not a separate fitted deployment PMF. -/
theorem deployment_failure_on_good (p : Param) (hp : Admissible p)
    (e : Param) (he : Admissible e) (T : ℕ) (hT : 0 < T)
    (hg : Good p e (1/250)) :
    (deployed p hp e he T).toMeasure.real (failureEvent T) ≤ budget e T := by
  have htv := statistical_approximation p hp e he T hT hg
  have hevent := tvEvent_le (deployed p hp e he T).toMeasure (target p hp T).toMeasure
    (failureEvent T) (Set.toFinite _).measurableSet
  rw [target_failure_zero, sub_zero, abs_of_nonneg measureReal_nonneg] at hevent
  exact hevent.trans htv

/-- Data selection is followed by actual deployment in the same source.
This bounds Accept∩Fail jointly; it is not a conditional-on-acceptance bound. -/
theorem registered_joint_failure_le (p : Param) (hp : Admissible p) (T : ℕ) (hT : 0 < T) :
    (jointLaw p hp T).toMeasure.real {z | z.2 ∈ acceptedFailure z.1 T} ≤ 76/375 := by
  have hbad : (trainingPMF p hp).toMeasure.real
      {omega | Good p (estimate omega) (1/250)}ᶜ ≤ 1/300 := by
    rw [trainingPMF_measure]
    exact calibration_bad_le p hp
  have hgood : ∀ omega ∈ {omega | Good p (estimate omega) (1/250)},
      (deployed p hp (selectedEstimate omega).val (selectedEstimate omega).property T).toMeasure.real
        (acceptedFailure omega T) ≤ 1/5 := by
    intro omega hg
    by_cases ha : Accept omega T
    · have hselect : selectedEstimate omega = ⟨estimate omega,ha.1⟩ := by
        simp [selectedEstimate, ha.1]
      rw [hselect]
      simp only [acceptedFailure, if_pos ha]
      exact (deployment_failure_on_good p hp (estimate omega) ha.1 T hT hg).trans ha.2
    · simp [acceptedFailure, ha]
  have h := selectedTrainingDeployment_failure_le (trainingPMF p hp) selectedEstimate
    (fun s => deployed p hp s.val s.property T)
    {omega | Good p (estimate omega) (1/250)} (fun omega => acceptedFailure omega T)
    (1/300) (1/5) (by norm_num) hbad hgood
  norm_num at h
  exact h

/-- On the registered low-noise interval the deterministic ideal gate accepts
both short horizons whenever the simultaneous calibration event holds. -/
theorem low_noise_good_gate (p : Param) (hb : Box p)
    (he0 : p.e0 ≤ 1/200) (he1 : p.e1 ≤ 1/200) (omega : Record)
    (hg : Good p (estimate omega) (1/250)) : Accept omega 2 ∧ Accept omega 10 := by
  have h := low_noise_good_accepts_raw p hb he0 he1 omega hg
  exact ⟨⟨h.1, (min_le_right _ _).trans h.2.1.le⟩,
    ⟨h.1, (min_le_right _ _).trans h.2.2.le⟩⟩

/-- Ideal algorithmic acceptance probability; machine failures remain outside
this probability model and must be retained by the executable. -/
theorem low_noise_acceptance_probability (p : Param) (hb : Box p)
    (he0 : p.e0 ≤ 1/200) (he1 : p.e1 ≤ 1/200) :
    (299/300 : ℝ) ≤ (trainingMeasure p (box_admissible hb)).real
      {omega | Accept omega 2 ∧ Accept omega 10} := by
  let A : Set Record := {omega | Accept omega 2 ∧ Accept omega 10}
  let G : Set Record := {omega | Good p (estimate omega) (1/250)}
  have hsub : G ⊆ A := fun omega hg => low_noise_good_gate p hb he0 he1 omega hg
  have hbad : (trainingMeasure p (box_admissible hb)).real Aᶜ ≤ 1/300 :=
    (measureReal_mono (Set.compl_subset_compl.mpr hsub)).trans (calibration_bad_le p (box_admissible hb))
  have hcompl : (trainingMeasure p (box_admissible hb)).real Aᶜ =
      1-(trainingMeasure p (box_admissible hb)).real A := by
    rw [measureReal_compl (Set.toFinite A).measurableSet]
    simp
  rw [hcompl] at hbad
  linarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataJoint
