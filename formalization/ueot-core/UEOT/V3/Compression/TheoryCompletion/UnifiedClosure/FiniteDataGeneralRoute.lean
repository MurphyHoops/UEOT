import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataCertificate
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteActionRealizabilityCheck SourcePolicyPathBridgeCheck
open SameSourceFiniteWindowCheck SameSourceConditionedTerminalCheck
open FiniteConditionalStability
open scoped BigOperators Classical
noncomputable section

theorem source_row_tv_le (p : Param) (hp : Admissible p) (estimate : Param)
    (he : Admissible estimate) (d : ℝ) (hg : Good p estimate d) (x : State) (a : Action) :
    tvDist ((model p hp).transitionPMF x a).toMeasure
      ((model estimate he).transitionPMF x a).toMeasure ≤ d := by
  have hd : 0 ≤ d := (abs_nonneg _).trans (hg 0)
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp only [Model.transitionPMF_apply_toReal]
  have hr0 : |p.r0-estimate.r0|≤d := by simpa [probeParameter] using hg 0
  have hr1 : |p.r1-estimate.r1|≤d := by simpa [probeParameter] using hg 1
  have he0 : |p.e0-estimate.e0|≤d := by simpa [probeParameter] using hg 2
  have he1 : |p.e1-estimate.e1|≤d := by simpa [probeParameter] using hg 3
  have hdiv (r s : ℝ) : r/2-s/2=(r-s)/2 := by ring
  have hcomp (r s : ℝ) : 1-r-(1-s)=s-r := by ring
  fin_cases x <;> fin_cases a <;>
    simp [model,transition,Fin.sum_univ_succ,hdiv,hcomp,abs_div,abs_sub_comm] <;> linarith

def baselineExperiment (p : Param) (hp : Admissible p) (T : ℕ) :=
  causalLaw initial (riskMicroControlKernel observe (fun _ => (model p hp).transitionPMF)
    (observationMarkovPolicy baseline)) T

/-- All original action/state records share the same true/reference source
calibration, before survival conditioning or action erasure. -/
theorem baseline_source_bound (p : Param) (hp : Admissible p) (estimate : Param)
    (he : Admissible estimate) (T : ℕ) (hg : Good p estimate (1/250)) :
    tvDist (baselineExperiment p hp T).toMeasure (baselineExperiment estimate he T).toMeasure ≤
      (T : ℝ)/250 := by
  have hrow (n : ℕ) (h : CausalHistory State (Action×State) n) :
      tvDist
        (riskMicroControlKernel observe (fun _ => (model p hp).transitionPMF)
          (observationMarkovPolicy baseline) n h).toMeasure
        (riskMicroControlKernel observe (fun _ => (model estimate he).transitionPMF)
          (observationMarkovPolicy baseline) n h).toMeasure ≤ 1/250 := by
    change tvDist (pmfExtend (PMF.pure 0) ((model p hp).transitionPMF (riskLastState n h))).toMeasure
      (pmfExtend (PMF.pure 0) ((model estimate he).transitionPMF (riskLastState n h))).toMeasure ≤ _
    rw [coverage_tv_extend_same_initial]
    calc
      _ ≤ ∑ a : Action, ((PMF.pure 0) a).toReal * (1/250 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (source_row_tv_le p hp estimate he _ hg _ a) ENNReal.toReal_nonneg
      _ = 1/250 := by rw [← Finset.sum_mul,coverage_sum_toReal,one_mul]
  have h := causalLaw_tv_bound initial
    (riskMicroControlKernel observe (fun _ => (model p hp).transitionPMF) (observationMarkovPolicy baseline))
    (riskMicroControlKernel observe (fun _ => (model estimate he).transitionPMF) (observationMarkovPolicy baseline))
    (fun _ => (1/250 : ℝ)) (by intro; norm_num) (by intro; norm_num) hrow T
  have ha := one_sub_prod_one_sub_le_sum (fun _ => (1/250 : ℝ))
    (by intro; norm_num) (by intro; norm_num) T
  exact h.trans (by simpa [Finset.sum_const,Finset.card_range,nsmul_eq_mul,div_eq_mul_inv] using ha)

/-- The generic same-event conditioning route is valid but pays the rare-event
normalizer. Structural rank-one stability replaces this denominator in the main
certificate; the generic rare-event theorem itself is unchanged. -/
theorem general_target_stability (p : Param) (hp : Admissible p) (estimate : Param)
    (he : Admissible estimate) (T : ℕ) (hg : Good p estimate (1/250)) :
    tvDist (target p hp T).toMeasure (target estimate he T).toMeasure ≤
      min 1 (((T : ℝ)/250)/(FiniteDataConditioned.mean estimate)^T) := by
  let S : Set (CausalHistory State (Action×State) T) :=
    {g | ¬ riskEverFailure (fun x => x ∉ FiniteDataConditioned.safe) T g}
  have ht := FiniteDataConditioned.source_positive p hp T
  have hepos := FiniteDataConditioned.source_positive estimate he T
  have h := conditioned_readout_tv_le_reference_mass
    (baselineExperiment p hp T) (baselineExperiment estimate he T) S ht hepos
    ((T : ℝ)/250) (baseline_source_bound p hp estimate he T hg)
    (fun g => statePrefix T 0 (eraseActionHistory (T+0) g)) (measurable_of_finite _)
  rw [FiniteDataConditioned.target_eq_actual p hp T,
    FiniteDataConditioned.target_eq_actual estimate he T]
  change tvDist ((conditionedPMF (baselineExperiment p hp T) S ht).map _).toMeasure
    ((conditionedPMF (baselineExperiment estimate he T) S hepos).map _).toMeasure ≤ _
  have hmass : (baselineExperiment estimate he T).toMeasure.real S =
      (FiniteDataConditioned.mean estimate)^T := FiniteDataConditioned.source_mass estimate he T
  rw [hmass] at h
  exact h
/-- Complete generic same-event route for this same consumer. Its deployment
charge includes one source perturbation for the preparatory action as well as
all T later operations. The reference conditioning mass remains explicit. -/
theorem general_approximation (p : Param) (hp : Admissible p) (estimate : Param)
    (he : Admissible estimate) (T : ℕ) (hT : 0<T) (hg : Good p estimate (1/250)) :
    tvDist (deployed p hp estimate he T).toMeasure (target p hp T).toMeasure ≤
      min 1 (((T : ℝ)+1)*max estimate.e0 estimate.e1 + ((T : ℝ)+1)/250 +
        ((T : ℝ)/250)/(FiniteDataConditioned.mean estimate)^T) := by
  have he0 : p.e0-estimate.e0≤1/250 := by simpa [probeParameter] using (abs_le.mp (hg 2)).2
  have he1 : p.e1-estimate.e1≤1/250 := by simpa [probeParameter] using (abs_le.mp (hg 3)).2
  have hm : max p.e0 p.e1 ≤ max estimate.e0 estimate.e1+1/250 := by
    apply max_le <;> linarith [le_max_left estimate.e0 estimate.e1,le_max_right estimate.e0 estimate.e1]
  apply le_min (tvDist_le_one _ _)
  have hc := (deployed_reference_bound p hp estimate he T hT).trans (min_le_right _ _)
  have ht := (general_target_stability p hp estimate he T hg).trans (min_le_right _ _)
  have hs : tvDist (target estimate he T).toMeasure (target p hp T).toMeasure =
      tvDist (target p hp T).toMeasure (target estimate he T).toMeasure := by
    rw [tvDist_eq_one_sub_pmfCommonMass,tvDist_eq_one_sub_pmfCommonMass]
    simp [pmfCommonMass,min_comm]
  have h := UEOT.V3.TransportDefect.tvDist_triangle
    (deployed p hp estimate he T).toMeasure (target estimate he T).toMeasure (target p hp T).toMeasure
  rw [hs] at h
  have h' := h.trans (add_le_add hc ht)
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0≤(T:ℝ)+1)
  nlinarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
