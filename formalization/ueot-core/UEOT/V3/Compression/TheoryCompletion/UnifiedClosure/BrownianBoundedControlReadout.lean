import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQHorizonTargetIntegral

/-!
Original commitment: one fixed controlled source must retain its actual action readout at every integration horizon.
Existing result: same real control has exact original predictable permission and global K bound; native full-predictable spaces exist independently for each horizon.
Premise reduced: construct the actual deployed real control's native input class on arbitrary U, with literal raw readout/primitive and original identity at source horizon A.
Model/witness: fixed original b on A, SAME masked control b/K and original Fs, any U including A=0/U=0; no new control or Lp transport is selected.
Consumer/boundary: all-read-time ownQ target shift/controlled C2 and original occupation source; no desired Ito/SDE/infinite-reward field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedControlReadout
open MeasureTheory ProbabilityTheory Set Filter
open BrownianTimeIntegrand BrownianPredictableInputs BrownianBoundedPredictableApproximation BrownianBoundedControlSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)

def actualControlReadout (p : ℝ × (ℝ≥0 → ℝ)) : ℝ := control A b K p.1 p.2

theorem actualControl_predictable : StronglyMeasurable[predictableSigma] (actualControlReadout A b K) := by
  have hs : MeasurableSet[predictableSigma] (Ioc (0 : ℝ) (A : ℝ) ×ˢ (univ : Set (ℝ≥0 → ℝ))) :=
    predictable_interval_rectangle 0 A MeasurableSet.univ
  have hm := (boundedRepresentative_predictable A b K).indicator hs
  convert hm using 1
  funext p
  by_cases ht : p.1∈Ioc (0 : ℝ) (A : ℝ) <;> simp [actualControlReadout,BrownianBoundedControlSource.control,ht]

include hK

theorem actualControl_memLp_two (U : ℝ≥0) : MemLp (actualControlReadout A b K) 2 (inputLaw U) :=
  MemLp.of_bound (control_joint A b K).aestronglyMeasurable K
    (Eventually.of_forall (fun p => control_bound A b K hK p.1 p.2))

/-- Independently defined ORIGINAL predictable class of the very same
actual real action; no cross-horizon class map or reselected action. -/
def actualControlInput (U : ℝ≥0) : fullPredictableL2 U :=
  ⟨(actualControl_memLp_two A b K hK U).toLp (actualControlReadout A b K),
    mem_lpMeas_iff_aestronglyMeasurable.mpr ((actualControl_predictable A b K).aestronglyMeasurable.congr
      (actualControl_memLp_two A b K hK U).coeFn_toLp.symm)⟩

theorem actualControlInput_coe (U : ℝ≥0) :
    (actualControlInput A b K hK U : Lp ℝ 2 (inputLaw U))=ᵐ[inputLaw U] actualControlReadout A b K :=
  (actualControl_memLp_two A b K hK U).coeFn_toLp

theorem actualControlInput_bound (U : ℝ≥0) :
    ∀ᵐ p ∂inputLaw U, |(actualControlInput A b K hK U : Lp ℝ 2 (inputLaw U)) p|≤K := by
  filter_upwards [actualControlInput_coe A b K hK U] with p hp
  rw [hp]
  simpa only [actualControlReadout,Real.norm_eq_abs] using control_bound A b K hK p.1 p.2

/-- At the source horizon this is the ORIGINAL input b, under the original
explicit bound; no clipping-induced change of problem is hidden. -/
theorem actualControlInput_original (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K) :
    actualControlInput A b K hK A=b := by
  apply Subtype.ext
  apply Lp.ext
  exact (actualControlInput_coe A b K hK A).trans (control_input_ae A b K hB)

omit hK in
/-- The actual real control has the SAME frozen primitive at every read
clock, including beyond its original cutoff A. -/
theorem actualControl_primitive (s : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    (∫ u in (0 : ℝ)..(s : ℝ), control A b K u ω)=drift A b K s ω := by
  rw [intervalIntegral.integral_of_le s.coe_nonneg]
  change (∫ u, (Ioc (0 : ℝ) (A : ℝ)).indicator (fun t => boundedRepresentative A b K (t,ω)) u
    ∂volume.restrict (Ioc (0 : ℝ) (s : ℝ)))=_
  rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,Set.Ioc_inter_Ioc,max_self,
    ← NNReal.coe_min,min_comm A s,← intervalIntegral.integral_of_le (min s A).coe_nonneg]
  exact (drift_primitive A b K s ω).symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedControlReadout
