import UEOT
namespace OwnQFixedHorizonIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralLiteralIntervals BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQIntegralClosure BrownianBoundedControlReadout
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
-- Fixed deployment is genuinely path-dependent/nonsmooth in its ORIGINALFs1.
-- Target g below does not replace this b, its Q or shifted noise.
def H (w : ℝ≥0→ℝ) : ℝ := if process (1/2) w≤process 1 w then 3/2 else -1/2
theorem H_past : StronglyMeasurable[naturalFiltration 1] H := by
  let : MeasurableSpace (ℝ≥0→ℝ) := naturalFiltration 1
  have h0 := (process_stronglyAdapted (1/2)).mono (naturalFiltration.mono (by norm_num : (1/2 : ℝ≥0)≤1))
  have hs : MeasurableSet {w : ℝ≥0→ℝ | process (1/2) w≤process 1 w} :=
    measurableSet_le h0.measurable (process_stronglyAdapted 1).measurable
  exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
theorem H_bound (w : ℝ≥0→ℝ) : ‖H w‖≤3/2 := by unfold H; split_ifs <;> norm_num
theorem H_top : MemLp H ∞ sourceLaw :=
  MemLp.of_bound (H_past.mono (naturalFiltration.le 1)).aestronglyMeasurable (3/2) (ae_of_all _ H_bound)
def b : fullPredictableL2 2 := intervalInput 2 1 2 (by norm_num) le_rfl H H_past H_top
theorem b_bound : ∀ᵐ p ∂inputLaw 2, |(b : Lp ℝ 2 (inputLaw 2)) p|≤(3/2 : ℝ) := by
  filter_upwards [intervalInput_coe 2 1 2 (by norm_num) le_rfl H H_past H_top] with p hp
  change (b : Lp ℝ 2 (inputLaw 2)) p=intervalIntegrand H 1 2 p at hp
  rw [hp]
  unfold intervalIntegrand
  change |(Ioc (1 : ℝ) 2).indicator (fun _=>1) p.1*H p.2|≤3/2
  by_cases ht : p.1∈Ioc (1 : ℝ) 2
  · rw [Set.indicator_of_mem ht,one_mul]
    simpa only [Real.norm_eq_abs] using H_bound p.2
  · norm_num [Set.indicator_of_notMem ht]

-- New targets are registered independently for each U. They all integrate
-- against the SAME deployment Q_A and W_A, not a U-renormalized control law.
def unitTarget (U : ℝ≥0) : fullPredictableL2 U := literalPredictableInput (BrownianIntegralClosure.unitInput U)
theorem unit_bound (U : ℝ≥0) : ∀ᵐ p ∂inputLaw U, |(unitTarget U : Lp ℝ 2 (inputLaw U)) p|≤(1 : ℝ) := by
  filter_upwards [(BrownianTimeIntegrand.integrand_memLp_two U
    (BrownianIntegralClosure.unitInput U).clock (BrownianIntegralClosure.unitInput U).coefficient
    (BrownianIntegralClosure.unitInput U).coefficient_bounded).coeFn_toLp] with p hp
  change (unitTarget U : Lp ℝ 2 (inputLaw U)) p=integrand (BrownianIntegralClosure.unitInput U).clock
    (BrownianIntegralClosure.unitInput U).coefficient p at hp
  rw [hp]
  change |∑ i : Fin 1, intervalIntegrand ((BrownianIntegralClosure.unitInput U).coefficient i)
    ((BrownianIntegralClosure.unitInput U).clock i.castSucc) ((BrownianIntegralClosure.unitInput U).clock i.succ) p|≤1
  rw [Fin.sum_univ_one]
  change |intervalIntegrand (fun _=>1) 0 U p|≤1
  unfold intervalIntegrand
  by_cases h : p.1∈Ioc (0 : ℝ) (U : ℝ) <;> simp [h]

def QI (A : ℝ≥0) (base : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hbase : ∀ᵐ p ∂inputLaw A, |(base : Lp ℝ 2 (inputLaw A)) p|≤K) (U : ℝ≥0) : Lp ℝ 2 (fullLaw A base) :=
  BrownianOwnQHorizonTargetIntegral.targetIntegralQ A base K hK hbase U (unitTarget U) 1 (by norm_num) (unit_bound U)
theorem QI_literal (A : ℝ≥0) (base : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hbase : ∀ᵐ p ∂inputLaw A, |(base : Lp ℝ 2 (inputLaw A)) p|≤K) (U : ℝ≥0) :
    QI A base K hK hbase U=outputValueQ A base K hK hbase (BrownianIntegralClosure.unitInput U) :=
  BrownianOwnQHorizonTargetIntegral.targetIntegralQ_returns_literal A base K hK hbase U 1 (by norm_num)
    (BrownianIntegralClosure.unitInput U) (unit_bound U)

theorem QI_variance (A : ℝ≥0) (base : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hbase : ∀ᵐ p ∂inputLaw A, |(base : Lp ℝ 2 (inputLaw A)) p|≤K) (U : ℝ≥0) :
    ‖QI A base K hK hbase U‖^2=(U : ℝ) := by
  rw [QI_literal]
  unfold outputValueQ
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rw [integral_congr_ae ((BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two A base K hK hbase
    (BrownianIntegralClosure.unitInput U)).coeFn_toLp.mono (fun _ h=>congrArg (fun x : ℝ=>x^2) h))]
  let _ := fullLaw_probability A base K hK hbase
  rw [BrownianOwnQSimpleIntegral.simpleIntegral_isometry A base K hK hbase]
  change (∑ i : Fin 1,
    (((BrownianIntegralClosure.unitInput U).clock i.succ : ℝ)-((BrownianIntegralClosure.unitInput U).clock i.castSucc : ℝ))*
      (∫ w, (BrownianIntegralClosure.unitInput U).coefficient i w^2 ∂fullLaw A base))=(U : ℝ)
  rw [Fin.sum_univ_one]
  change ((U : ℝ)-0)*(∫ _ : ℝ≥0→ℝ, (1 : ℝ)^2 ∂fullLaw A base)=(U : ℝ)
  simp
example : ‖QI 2 b (3/2) (by norm_num) b_bound (3/2)‖^2=(3/2 : ℝ) := by
  have h:=QI_variance 2 b (3/2) (by norm_num) b_bound (3/2)
  norm_num at h
  exact h
example : ‖QI 2 b (3/2) (by norm_num) b_bound 3‖^2=(3 : ℝ) := by
  have h:=QI_variance 2 b (3/2) (by norm_num) b_bound 3
  norm_num at h
  exact h
example (U : ℝ≥0) : (∫ w, QI 2 b (3/2) (by norm_num) b_bound U w ∂fullLaw 2 b)=0 :=
  BrownianOwnQHorizonTargetIntegral.targetIntegralQ_mean_zero 2 b (3/2) (by norm_num) b_bound U
    (unitTarget U) 1 (by norm_num) (unit_bound U)
example : QI 2 b (3/2) (by norm_num) b_bound 0=0 := by
  have h:=QI_variance 2 b (3/2) (by norm_num) b_bound 0
  norm_num at h
  exact h

example : actualControlInput 2 b (3/2) (by norm_num) 2=b := actualControlInput_original 2 b (3/2) (by norm_num) b_bound
example (U : ℝ≥0) : (actualControlInput 2 b (3/2) (by norm_num) U : Lp ℝ 2 (inputLaw U))
    =ᵐ[inputLaw U] actualControlReadout 2 b (3/2) := actualControlInput_coe 2 b (3/2) (by norm_num) U
example (U : ℝ≥0) : ∀ᵐ p ∂inputLaw U, |(actualControlInput 2 b (3/2) (by norm_num) U : Lp ℝ 2 (inputLaw U)) p|≤3/2 :=
  actualControlInput_bound 2 b (3/2) (by norm_num) U
example (w : ℝ≥0→ℝ) : control 2 b (3/2) 3 w=0 := by norm_num [BrownianBoundedControlSource.control]
example (w : ℝ≥0→ℝ) : (∫ u in (0 : ℝ)..(3 : ℝ), control 2 b (3/2) u w)=drift 2 b (3/2) 2 w := by
  have h:=actualControl_primitive 2 b (3/2) 3 w
  norm_num at h
  rw [h,drift_after 2 b (3/2) 3 (by norm_num)]
example (w : ℝ≥0→ℝ) : (∫ u in (0 : ℝ)..(3/2 : ℝ), control 2 b (3/2) u w)=drift 2 b (3/2) (3/2) w :=
  actualControl_primitive 2 b (3/2) (3/2) w

-- Literal finite target on ANY U sees the SAME actual global action and
-- drift increments, even when U lies on either side of density horizonA2.
theorem actual_unit_cross (U : ℝ≥0) (w : ℝ≥0→ℝ) :
    (∫ t,integrand (BrownianIntegralClosure.unitInput U).clock (BrownianIntegralClosure.unitInput U).coefficient (t,w)*
      control 2 b (3/2) t w ∂timeLaw U)=drift 2 b (3/2) U w := by
  rw [BrownianOwnQHorizonCrossDrift.literal_cross_integral 2 b (3/2) (by norm_num) U]
  change (∑ i : Fin 1, (BrownianIntegralClosure.unitInput U).coefficient i w*
    (drift 2 b (3/2) ((BrownianIntegralClosure.unitInput U).clock i.succ) w-
      drift 2 b (3/2) ((BrownianIntegralClosure.unitInput U).clock i.castSucc) w))=_
  rw [Fin.sum_univ_one]
  change 1*(drift 2 b (3/2) U w-drift 2 b (3/2) 0 w)=_
  rw [congrFun (drift_zero 2 b (3/2)) w]
  simp
example (w : ℝ≥0→ℝ) :
    (∫ t,integrand (BrownianIntegralClosure.unitInput 3).clock (BrownianIntegralClosure.unitInput 3).coefficient (t,w)*
      control 2 b (3/2) t w ∂timeLaw 3)=drift 2 b (3/2) 2 w := by
  rw [actual_unit_cross,drift_after 2 b (3/2) 3 (by norm_num)]
example (U : ℝ≥0) : (QI 2 b (3/2) (by norm_num) b_bound U : (ℝ≥0→ℝ)→ℝ)=ᵐ[fullLaw 2 b]
    fun w=>outputValue (BrownianIntegralClosure.unitInput U) w-
      crossEnergyClass U U (unitTarget U) (actualControlInput 2 b (3/2) (by norm_num) U) w := by
  rw [QI_literal]
  exact (BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two 2 b (3/2) (by norm_num) b_bound
    (BrownianIntegralClosure.unitInput U)).coeFn_toLp.trans
      ((fullLaw_absolutelyContinuous 2 b).ae_le
        (BrownianOwnQHorizonCrossDrift.literal_integral_shift 2 b (3/2) (by norm_num) U (BrownianIntegralClosure.unitInput U)))

-- The zero deployment horizon kills its control, not the original noise.
def zeroB : fullPredictableL2 0 := 0
theorem zero_bound : ∀ᵐ p ∂inputLaw 0, |(zeroB : Lp ℝ 2 (inputLaw 0)) p|≤(0 : ℝ) := by simp [inputLaw_zero]
example (p : ℝ×(ℝ≥0→ℝ)) : actualControlReadout 0 zeroB 0 p=0 := by simp [actualControlReadout,BrownianBoundedControlSource.control]
example : actualControlInput 0 zeroB 0 (by norm_num) 3=0 := by
  apply Subtype.ext
  change (actualControlInput 0 zeroB 0 (by norm_num) 3 : Lp ℝ 2 (inputLaw 3)) = (0 : Lp ℝ 2 (inputLaw 3))
  apply Lp.ext
  filter_upwards [actualControlInput_coe 0 zeroB 0 (by norm_num) 3,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := inputLaw 3)] with p hc hz
  rw [hc,hz]
  simp [actualControlReadout,BrownianBoundedControlSource.control]
example : ‖QI 0 zeroB 0 (by norm_num) zero_bound 3‖^2=3 := by
  have h:=QI_variance 0 zeroB 0 (by norm_num) zero_bound 3
  norm_num at h
  exact h
example (w : ℝ≥0→ℝ) : (∫ u in (0 : ℝ)..(3 : ℝ),control 0 zeroB 0 u w)=0 := by
  have h:=actualControl_primitive 0 zeroB 0 3 w
  norm_num at h
  rw [h,drift_horizon_zero]
#print axioms BrownianOwnQHorizonTargetIntegral.targetInput_mem_domain
#print axioms BrownianOwnQHorizonTargetIntegral.target_outputs_tendsto
#print axioms BrownianOwnQHorizonTargetIntegral.targetIntegralQ_mean_zero
#print axioms BrownianOwnQHorizonTargetIntegral.targetIntegralQ_returns_literal
#print axioms actualControl_predictable
#print axioms actualControlInput_original
#print axioms actualControl_primitive
#print axioms BrownianOwnQHorizonCrossDrift.literal_cross_integral
#print axioms BrownianOwnQHorizonCrossDrift.crossEnergyClass_literal
#print axioms BrownianOwnQHorizonCrossDrift.literal_integral_shift
#print axioms BrownianOwnQHorizonCrossDrift.target_crossEnergy_tendsto
#print axioms QI_variance
end
end OwnQFixedHorizonIndependent
