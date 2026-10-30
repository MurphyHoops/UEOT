import UEOT
namespace OwnQShiftIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralLiteralIntervals
open BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianBoundedTerminalL2Source BrownianBoundedTerminalKLSource
open BrownianOwnQTimeInput BrownianOwnQBoundedInput BrownianOwnQCrossDrift BrownianOwnQIntegralShift
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
-- Signed nonsmooth response to TWO actual original history times.
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
def f : fullPredictableL2 3 := intervalInput 3 1 2 (by norm_num) (by norm_num) H H_past H_top
theorem f_bound : ∀ᵐ p ∂inputLaw 3, |(f : Lp ℝ 2 (inputLaw 3)) p|≤(3/2 : ℝ) := by
  filter_upwards [intervalInput_coe 3 1 2 (by norm_num) (by norm_num) H H_past H_top] with p hp
  change (f : Lp ℝ 2 (inputLaw 3)) p=intervalIntegrand H 1 2 p at hp
  rw [hp]
  unfold intervalIntegrand
  change |(Ioc (1 : ℝ) 2).indicator (fun _=>1) p.1*H p.2|≤3/2
  by_cases ht : p.1∈Ioc (1 : ℝ) 2
  · rw [Set.indicator_of_mem ht,one_mul]
    simpa only [Real.norm_eq_abs] using H_bound p.2
  · norm_num [Set.indicator_of_notMem ht]
def r : ElementaryInput 3 := intervalRecord 3 1 2 (by norm_num) (by norm_num) H H_past H_top

example (w : ℝ≥0→ℝ) :
    (∫ t, integrand r.clock r.coefficient (t,w)*boundedRepresentative 3 f (3/2) (t,w) ∂timeLaw 3)=
      ∑ i : Fin r.n, r.coefficient i w*(drift 3 f (3/2) (r.clock i.succ) w-
        drift 3 f (3/2) (r.clock i.castSucc) w) := literal_cross_integral 3 f (3/2) (by norm_num) r w
example : BrownianOwnQSimpleIntegral.simpleIntegral 3 f (3/2) r=ᵐ[fullLaw 3 f]
    fun w=>outputValue r w-crossEnergyClass 3 3 (literalPredictableInput r) f w :=
  (fullLaw_absolutelyContinuous 3 f).ae_le (literal_integral_shift 3 f (3/2) (by norm_num) f_bound r)
example : Tendsto (fun n=>crossEnergyClass 3 3
    (literalPredictableInput (approximation 3 f (3/2) (by norm_num) f_bound n)) f) atTop
      (𝓝 (energyClass 3 3 f)) := actual_crossEnergy_tendsto 3 f (3/2) (by norm_num) f_bound
-- SAME nondegenerate actual time energy under OWNQ; no expectation changed to P.
theorem actual_energy_Q : timeEnergy 3 f 3 =ᵐ[fullLaw 3 f] fun w=>H w^2 := by
  have he := timeEnergy_interval_horizon 3 1 2 (by norm_num) (by norm_num) H H_past H_top
  norm_num at he
  exact (fullLaw_absolutelyContinuous 3 f).ae_le he
example : ∀ᵐ w ∂fullLaw 3 f, (1/4 : ℝ)≤timeEnergy 3 f 3 w ∧ timeEnergy 3 f 3 w≤9/4 := by
  apply actual_energy_Q.mono
  intro w hw
  rw [hw]
  change (1/4 : ℝ)≤H w^2 ∧ H w^2≤9/4
  unfold H
  split_ifs <;> norm_num
example : boundedIntegralQ 3 f (3/2) (by norm_num) f_bound=ᵐ[fullLaw 3 f]
    fun w=>(predictableIntegral 3 f : (ℝ≥0→ℝ)→ℝ) w-H w^2 := by
  filter_upwards [boundedIntegralQ_eq_actual 3 f (3/2) (by norm_num) f_bound,actual_energy_Q] with w hi he
  change boundedIntegralQ 3 f (3/2) (by norm_num) f_bound w=(predictableIntegral 3 f : (ℝ≥0→ℝ)→ℝ) w-timeEnergy 3 f 3 w at hi
  rw [hi,he]
example : (predictableIntegral 3 f : (ℝ≥0→ℝ)→ℝ)=ᵐ[fullLaw 3 f]
    fun w=>boundedIntegralQ 3 f (3/2) (by norm_num) f_bound w+
      UEOT.V3.GirsanovPathKL.controlEnergy 3 (control 3 f (3/2)) w :=
  actual_integral_shift 3 f (3/2) (by norm_num) f_bound
example : (BrownianBoundedTerminalKLSource.actualTerminalData 3 f (3/2) (by norm_num) f_bound).controlledIntegral
    =ᵐ[fullLaw 3 f] boundedIntegralQ 3 f (3/2) (by norm_num) f_bound :=
  original_terminal_returns_Q_integral 3 f (3/2) (by norm_num) f_bound
example : (BrownianBoundedTerminalKLSource.actualTerminalData 3 f (3/2) (by norm_num) f_bound).baselineIntegral=
    (predictableIntegral 3 f : (ℝ≥0→ℝ)→ℝ) := rfl
example : fullDensity 3 f=ᵐ[fullLaw 3 f] fun w=>
    Real.exp (boundedIntegralQ 3 f (3/2) (by norm_num) f_bound w+(1/2 : ℝ)*H w^2) := by
  filter_upwards [actual_density_eq_Q_integral 3 f (3/2) (by norm_num) f_bound,actual_energy_Q] with w hd he
  rw [hd,he]
example : (BrownianBoundedTerminalKLSource.actualTerminalData 3 f (3/2) (by norm_num) f_bound).density=
    fun w=>ENNReal.ofReal (fullDensity 3 f w) := rfl

-- BaseT0 actual identities use actual constructed Q integral, not a stipulated0.
def zeroF : fullPredictableL2 0 := 0
theorem zero_bound : ∀ᵐ p ∂inputLaw 0, |(zeroF : Lp ℝ 2 (inputLaw 0)) p|≤(0 : ℝ) := by simp [inputLaw_zero]
private theorem zero_QI : boundedIntegralQ 0 zeroF 0 (by norm_num) zero_bound=0 := by
  apply norm_eq_zero.mp
  rw [boundedIntegralQ_norm]
  have hm : inputLawQ 0 zeroF 0=0 := by simp [inputLawQ,timeLaw]
  have hz : boundedInputValueQ 0 zeroF 0 (by norm_num) zero_bound=0 := by
    apply Lp.ext
    exact ae_iff.mpr (by simp [hm])
  rw [hz,norm_zero]
example : fullDensity 0 zeroF=ᵐ[fullLaw 0 zeroF] fun _=>1 := by
  filter_upwards [actual_density_eq_Q_integral 0 zeroF 0 (by norm_num) zero_bound,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := fullLaw 0 zeroF)] with w hd hz
  rw [zero_QI] at hd
  rw [hd,hz,congrFun (timeEnergy_zero 0 zeroF) w]
  norm_num
example : (BrownianBoundedTerminalKLSource.actualTerminalData 0 zeroF 0 (by norm_num) zero_bound).controlledIntegral
    =ᵐ[fullLaw 0 zeroF] fun _=>0 := by
  apply (original_terminal_returns_Q_integral 0 zeroF 0 (by norm_num) zero_bound).trans
  rw [zero_QI]
  exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := fullLaw 0 zeroF)
#print axioms literal_cross_integral
#print axioms crossEnergyClass_literal
#print axioms literal_integral_shift
#print axioms actual_crossEnergy_tendsto
#print axioms boundedIntegralQ_eq_actual
#print axioms original_terminal_returns_Q_integral
#print axioms actual_integral_shift
#print axioms actual_density_eq_Q_integral
#print axioms actual_energy_Q
end
end OwnQShiftIndependent
