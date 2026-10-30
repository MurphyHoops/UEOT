import UEOT
namespace VectorMultiplierIndependent
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput
open BrownianVectorIntegralClosure BrownianVectorPredictableInputs BrownianVectorPredictableDensity
open BrownianVectorIntegralTimeSource BrownianVectorIntegralConditionalSource BrownianVectorIntegralContinuousVersion
open BrownianVectorIntegralGridL1 BrownianVectorIntegralTimeEnergy BrownianVectorIntegralEnergyL1
open BrownianVectorCrossPartitionQV BrownianVectorFiniteStateCrossQV BrownianQuadraticVariation
open BrownianTimeIntegrand (timeLaw)
open BrownianVectorPredictableMultiplier BrownianVectorPastMultiplierBinding BrownianVectorLeftMultiplierBinding
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
-- Fresh nonsmooth coefficients, BOTH coordinates use the OTHER coordinate's
-- original START1 sigma. No own-coordinate scalar-filtration substitution.
def H (k : Fin 2) (w : Sample 2) : ℝ :=
  if k=0 then (if 0≤coordinate 2 1 1 w then 1 else -1)
  else (if 0≤coordinate 2 0 1 w then 2 else -2)
theorem H_past (k : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 1] (H k) := by
  have hc (j : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 1] (coordinate 2 j 1) :=
    (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp_stronglyMeasurable (vectorProcess_stronglyAdapted 2 1)
  let : MeasurableSpace (Sample 2) := jointNaturalFiltration 2 1
  have hs (j : Fin 2) : MeasurableSet {w : Sample 2 | 0≤coordinate 2 j 1 w} :=
    measurableSet_le measurable_const (hc j).measurable
  unfold H
  split_ifs
  · exact (Measurable.ite (hs 1) measurable_const measurable_const).stronglyMeasurable
  · exact (Measurable.ite (hs 0) measurable_const measurable_const).stronglyMeasurable
theorem H_bounded (k : Fin 2) : MemLp (H k) ∞ (productLaw 2) := by
  apply memLp_top_of_bound ((H_past k).mono ((jointNaturalFiltration 2).le 1)).aestronglyMeasurable 2
  apply ae_of_all
  intro w
  unfold H
  split_ifs <;> norm_num
theorem H_norm (w : Sample 2) : ‖coefficient 2 H w‖^2=5 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  simp only [coefficient_apply,H,show (1 : Fin 2) ≠ 0 by decide,ite_true,ite_false]
  split_ifs <;> norm_num

def f : fullPredictableL2 2 3 := intervalInput 2 3 1 2 (by norm_num) (by norm_num) H H_past H_bounded

-- g reads a genuinely different earlier history on its second actuator.
def G (k : Fin 2) (w : Sample 2) : ℝ :=
  if k=0 then -10 * H 0 w else (if 0≤coordinate 2 0 (1/2) w then -2 else 2)
theorem G_past (k : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 1] (G k) := by
  have hc : StronglyMeasurable[jointNaturalFiltration 2 1] (coordinate 2 0 (1/2)) :=
    ((EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 2)).continuous.comp_stronglyMeasurable
      (vectorProcess_stronglyAdapted 2 (1/2))).mono ((jointNaturalFiltration 2).mono (by norm_num))
  let : MeasurableSpace (Sample 2) := jointNaturalFiltration 2 1
  have hs : MeasurableSet {w : Sample 2 | 0≤coordinate 2 0 (1/2) w} :=
    measurableSet_le measurable_const hc.measurable
  unfold G
  split_ifs
  · exact stronglyMeasurable_const.mul (H_past 0)
  · exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
theorem G_bounded (k : Fin 2) : MemLp (G k) ∞ (productLaw 2) := by
  apply memLp_top_of_bound ((G_past k).mono ((jointNaturalFiltration 2).le 1)).aestronglyMeasurable 10
  apply ae_of_all
  intro w
  unfold G H
  split_ifs <;> norm_num at *
def g : fullPredictableL2 2 3 := intervalInput 2 3 1 2 (by norm_num) (by norm_num) G G_past G_bounded

def family : Fin 2→fullPredictableL2 2 3 := ![f,g]
-- A different genuinely nonlinear SAME-state readout; no approximate state.
def F (x : EuclideanSpace ℝ (Fin 2)) : ℝ := Real.cos (x 0-2*x 1)
theorem F_continuous : Continuous F := by
  exact Real.continuous_cos.comp ((EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 2)).continuous.sub
    (continuous_const.mul (EuclideanSpace.proj (𝕜:=ℝ) (1 : Fin 2)).continuous))
theorem F_bound (x : EuclideanSpace ℝ (Fin 2)) : ‖F x‖≤1 := Real.abs_cos_le_one _
def R (u : ℝ≥0) (w : Sample 2) : ℝ := F (stateProcess 2 3 family u w)
theorem R_measurable : Measurable (Function.uncurry R) := F_continuous.measurable.comp (stateProcess_measurable 2 3 family)
theorem R_past : StronglyAdapted (jointNaturalFiltration 2) R :=
  fun u=>F_continuous.comp_stronglyMeasurable (stateProcess_stronglyAdapted 2 3 family u)
theorem R_continuous : ∀ᵐ w ∂productLaw 2,Continuous (fun u=>R u w) :=
  (stateProcess_continuous 2 3 family).mono (fun _ h=>F_continuous.comp h)
theorem R_bound (u : ℝ≥0) (w : Sample 2) : ‖R u w‖≤1 := F_bound _
example : (functionOfStateInput 2 3 family F F_continuous 1 F_bound f :
    Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 3)) =ᵐ[inputLaw 2 3]
    fun p=>F (stateProcess 2 3 family (Real.toNNReal p.1) p.2) •
      (f : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 3)) p :=
  functionOfStateInput_coe 2 3 family F F_continuous 1 F_bound f
example : Martingale (continuousIntegralProcess 2 3 (functionOfStateInput 2 3 family F F_continuous 1 F_bound f))
    (jointNaturalFiltration 2) (productLaw 2) := functionOfStateInput_martingale 2 3 family F F_continuous 1 F_bound f
example : Tendsto (fun n=>sampledMultiplier 2 3 (uniformClock 3 n) (uniformClock_mono 3 n)
    R R_past 1 (by norm_num) R_bound f) atTop
    (𝓝 (continuousMultiplier 2 3 R R_measurable R_past R_continuous 1 R_bound f)) :=
  sampledMultiplier_tendsto 2 3 (fun n=>n+1) (uniformClock 3) (uniformClock_mono 3)
    (uniformClock_zero 3) (uniformClock_end 3) (uniformClock_mesh_tendsto 3)
    R R_measurable R_past R_continuous 1 (by norm_num) R_bound f
example : TendstoInMeasure (productLaw 2) (fun n=>weightedIncrementSum 2 3 (uniformClock 3 n) R f)
    atTop (continuousIntegralProcess 2 3 (functionOfStateInput 2 3 family F F_continuous 1 F_bound f) 3) :=
  functionOfState_startSums_tendstoInMeasure 2 3 (fun n=>n+1) (uniformClock 3) (uniformClock_mono 3)
    (uniformClock_zero 3) (uniformClock_end 3) (uniformClock_mesh_tendsto 3) family F F_continuous 1 F_bound f
-- SAME-state sampled integral on a repeated clock literally returns the
-- original observed sums, including the zero-width row, not a new M process.
example : (predictableIntegral 2 3 (sampledMultiplier 2 3 ![0,1,1,3]
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    R R_past 1 (by norm_num) R_bound f) : Sample 2→ℝ) =ᵐ[productLaw 2]
    weightedIncrementSum 2 3 ![0,1,1,3] R f := sampledMultiplier_integral_coe 2 3 _ _ R R_past 1 (by norm_num) R_bound f
example (w : Sample 2) : weightedIncrementSum 2 3 ![0,1,1,3] R f w =
    R 0 w*(continuousIntegralProcess 2 3 f 1 w-continuousIntegralProcess 2 3 f 0 w)+
    R 1 w*(continuousIntegralProcess 2 3 f 3 w-continuousIntegralProcess 2 3 f 1 w) := by
  simp [weightedIncrementSum,Fin.sum_univ_succ]
-- The START window API genuinely accepts only source L-infinity and Fs
-- strong measurability. It neither asks for a global raw bound nor grants F0.
example (J : Sample 2→ℝ) (hp : StronglyMeasurable[jointNaturalFiltration 2 1] J)
    (hi : MemLp J ∞ (productLaw 2)) :
    (predictableIntegral 2 3 (windowMultiplier 2 3 1 4 J hp hi f) : Sample 2→ℝ) =ᵐ[productLaw 2]
      fun w=>J w*(continuousIntegralProcess 2 3 f 4 w-continuousIntegralProcess 2 3 f 1 w) :=
  windowMultiplier_integral_coe 2 3 1 4 (by norm_num) J hp hi f
example (J : Sample 2→ℝ) (hp : StronglyMeasurable[jointNaturalFiltration 2 1] J)
    (hi : MemLp J ∞ (productLaw 2)) :
    predictableIntegral 2 3 (windowMultiplier 2 3 1 1 J hp hi f)=0 := by
  apply Lp.ext
  filter_upwards [windowMultiplier_integral_coe 2 3 1 1 le_rfl J hp hi f,
    Lp.coeFn_zero ℝ 2 (productLaw 2)] with w hw hz
  rw [hw,hz]
  simp
-- Unbounded continuous state readout gains only predictable permission;
-- no L-infinity multiplier/integrability is asserted for it.
example : AEStronglyMeasurable[predictableSigma 2]
    (fun p : ℝ×Sample 2=>stateProcess 2 3 family (Real.toNNReal p.1) p.2 0) (inputLaw 2 3) := by
  apply continuousReadout_predictable 2 3 (fun u w=>stateProcess 2 3 family u w 0)
  · intro u
    exact (EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 2)).continuous.comp_stronglyMeasurable (stateProcess_stronglyAdapted 2 3 family u)
  · exact (stateProcess_continuous 2 3 family).mono (fun _ h=>(EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 2)).continuous.comp h)
-- Empty noise/state/time with an actual empty caller clock.
example (h : fullPredictableL2 0 0) :
    TendstoInMeasure (productLaw 0) (fun _n : ℕ=>weightedIncrementSum 0 0 (fun _ : Fin 1=>0)
      (fun _ _=>1) h) atTop (continuousIntegralProcess 0 0
        (functionOfStateInput 0 0 (fun _ : Fin 0=>h) (fun _=>1) continuous_const 1 (fun _=>by norm_num) h) 0) := by
  apply functionOfState_startSums_tendstoInMeasure 0 0 (fun _=>0) (fun _ _=>0)
    (fun _ _ _ _=>le_rfl) (fun _=>rfl) (fun _=>rfl) _ (fun _ : Fin 0=>h) (fun _=>1)
    continuous_const 1 (fun _=>by norm_num) h
  simp [mesh]
#print axioms continuousReadout_predictable
#print axioms inputMultiplier_norm_le
#print axioms boundedMultiplier_tendsto
#print axioms boundedMultipliedIntegral_tendsto
#print axioms functionOfStateInput_coe
#print axioms functionOfStateInput_martingale
#print axioms windowMultiplier_integral_class
#print axioms windowMultiplier_integral_coe
#print axioms leftCoefficient_bound
#print axioms sampledMultiplier_integral_coe
#print axioms sampledMultiplier_tendsto
#print axioms sampledIntegral_tendsto
#print axioms weightedIncrementSum_tendstoInMeasure
#print axioms functionOfState_startSums_tendstoInMeasure
end
end VectorMultiplierIndependent
