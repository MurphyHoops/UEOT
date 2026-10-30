import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepShiftedSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianConstantGirsanovSource

/-!
Original commitment: ORIGINAL P-KL-05 needs actual random START action/integral/energy/density bindings.
Existing result: SAME actual one-block Q has a true shifted Brownian under ORIGINALFt, with preserved START law and derived Q-energy.
Premise reduced: construct ORIGINAL TerminalGirsanovData for the actual bounded START coefficient, actual returned baseline integral and shifted elementary prefix.
Model/witness: H originalFa-measurable and sourceMemLp∞, a<=b, control 1_(a,b]H on [0,b], SAME P/Q/W and supplied H.
Consumer: original full-noise KL equality and measurable state-path upper bound; finite/simple/general predictable Girsanov remains separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepGirsanovSource
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianOneStepIntegral
open BrownianPastStepExponentialSource BrownianPastStepTiltKernelSource BrownianPastStepGaussianResidualSource BrownianPastStepShiftedSource
open BrownianIntegralLiteralIntervals BrownianPredictableInputs BrownianPredictableDensity BrownianCommonRefinement
open UEOT.V3.GirsanovPathKL
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def stepControl (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => H ω) t

private theorem control_square (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    (fun t => ‖stepControl H a b t ω‖^2)=(Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => ‖H ω‖^2) := by
  funext t
  by_cases ht : t ∈ Ioc (a : ℝ) (b : ℝ)
  · simp [stepControl,ht]
  · simp [stepControl,ht]

/-- Real clock dt energy uses the supplied interval and actual coefficient. -/
theorem stepControl_energy (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b) (ω : ℝ≥0 → ℝ) :
    controlEnergy b (stepControl H a b) ω=stepEnergy H a b ω := by
  have hs : Ioc (a : ℝ) (b : ℝ) ⊆ Ioc (0 : ℝ) (b : ℝ) := by
    intro t ht
    exact ⟨lt_of_le_of_lt a.coe_nonneg ht.1,ht.2⟩
  rw [controlEnergy,control_square,intervalIntegral.integral_of_le b.coe_nonneg,
    integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hs,← intervalIntegral.integral_of_le (show (a : ℝ)≤(b : ℝ) from hab)]
  rfl

/-- Permissions are derived by the literal zero readout before START and
original START permission afterwards, for the original real-clock filtration. -/
theorem stepControl_progressive (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    IsProgressive BrownianConstantGirsanovSource.controlFiltration (stepControl H a b) := by
  intro s
  by_cases hs : s ≤ (a : ℝ)
  · have he : (fun p : Iic s × (ℝ≥0 → ℝ) => stepControl H a b p.1 p.2)=fun _ => (0 : ℝ) := by
      funext p
      apply Set.indicator_of_notMem
      intro hp
      exact (not_lt_of_ge (p.1.property.trans hs)) hp.1
    rw [he]
    exact measurable_const
  · have ha : a ≤ Real.toNNReal s := by
      have h := Real.toNNReal_mono (le_of_not_ge hs : (a : ℝ) ≤ s)
      simpa only [Real.toNNReal_coe] using h
    have hh : @Measurable (ℝ≥0 → ℝ) ℝ (BrownianConstantGirsanovSource.controlFiltration s) inferInstance H :=
      (hH.mono (naturalFiltration.mono ha)).measurable
    have ht : @MeasurableSet (Iic s × (ℝ≥0 → ℝ))
        (Subtype.instMeasurableSpace.prod (BrownianConstantGirsanovSource.controlFiltration s))
        {p | (p.1 : ℝ) ∈ Ioc (a : ℝ) (b : ℝ)} :=
      (measurable_subtype_coe.comp measurable_fst) measurableSet_Ioc
    exact (hh.comp measurable_snd).indicator ht

def baselineInput (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hHtop : MemLp H ∞ sourceLaw) : fullPredictableL2 b :=
  intervalInput b a b hab le_rfl H hH hHtop

def baselineIntegral (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) : (ℝ≥0 → ℝ) → ℝ := oneStep H a b

theorem baseline_returns_actual_integral (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hHtop : MemLp H ∞ sourceLaw) :
    (predictableIntegral b (baselineInput H a b hab hH hHtop) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw] baselineIntegral H a b := by
  rw [baselineInput,integral_interval_literal]
  exact (oneStep_memLp_two hHtop a b).coeFn_toLp

def controlledIntegral (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  H ω*(shiftedProcess H a b b ω-shiftedProcess H a b a ω)

def controlledPath (H : (ℝ≥0 → ℝ) → ℝ) (a b t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  H ω*(shiftedProcess H a b (clamp a b t) ω-shiftedProcess H a b a ω)

theorem controlledIntegral_eq_centered (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b) :
    controlledIntegral H a b=H*centeredIncrement H a b := by
  funext ω
  unfold controlledIntegral shiftedProcess overlap centeredIncrement increment
  simp only [Pi.mul_apply,min_self,min_eq_left hab,min_eq_right hab,sub_self,mul_zero,sub_zero,NNReal.coe_sub hab]
  ring

private theorem H_memLp_two_Q (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hHtop : MemLp H ∞ sourceLaw) : MemLp H 2 (stepLaw H a b) :=
  (memLp_two_iff_integrable_sq (hH.mono (naturalFiltration.le a)).aestronglyMeasurable).mpr
    (stepLaw_square_integrable H a b hab hH (hHtop.mono_exponent le_top))

theorem controlledIntegral_integrable (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hHtop : MemLp H ∞ sourceLaw) :
    Integrable (controlledIntegral H a b) (stepLaw H a b) := by
  rw [controlledIntegral_eq_centered H a b hab]
  exact (H_memLp_two_Q H a b hab hH hHtop).integrable_mul
    (centeredIncrement_law_indep H a b hab hH).1.hasGaussianLaw.memLp_two

private theorem controlledIntegral_end_past (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    StronglyMeasurable[naturalFiltration b] (controlledIntegral H a b) :=
  (hH.mono (naturalFiltration.mono hab)).mul ((shiftedProcess_stronglyAdapted H a b hab hH b).sub
    ((shiftedProcess_stronglyAdapted H a b hab hH a).mono (naturalFiltration.mono hab)))

/-- Actual shifted elementary integral has zero conditional mean under
original F0, derived via Fa and genuine source conditional noise law. -/
theorem controlledIntegral_condExp_zero (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hHtop : MemLp H ∞ sourceLaw) :
    (stepLaw H a b)[controlledIntegral H a b | naturalFiltration 0] =ᵐ[stepLaw H a b] fun _ => 0 := by
  let _ := stepLaw_probability H a b hab hH
  have hc : (stepLaw H a b)[controlledIntegral H a b | naturalFiltration a] =ᵐ[stepLaw H a b] fun _ => 0 := by
    rw [controlledIntegral_eq_centered H a b hab]
    have hi : Integrable (H*centeredIncrement H a b) (stepLaw H a b) := by
      rw [← controlledIntegral_eq_centered H a b hab]
      exact controlledIntegral_integrable H a b hab hH hHtop
    have hz := (centeredIncrement_law_indep H a b hab hH).1.hasGaussianLaw.integrable
    apply (condExp_mul_of_stronglyMeasurable_left hH hi hz).trans
    filter_upwards [centeredIncrement_condExp_zero H a b hab hH] with ω hω
    simp only [Pi.mul_apply,hω,mul_zero]
  have ht := condExp_condExp_of_le (μ := stepLaw H a b) (f := controlledIntegral H a b)
    (naturalFiltration.mono (show (0 : ℝ≥0)≤a from bot_le)) (naturalFiltration.le a)
  apply ht.symm.trans
  apply (condExp_congr_ae (m := naturalFiltration 0) hc).trans
  change (stepLaw H a b)[(0 : (ℝ≥0 → ℝ) → ℝ) | naturalFiltration 0] =ᵐ[stepLaw H a b] (0 : (ℝ≥0 → ℝ) → ℝ)
  rw [condExp_zero]

private theorem path_zero (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) : controlledPath H a b 0=0 := by
  funext ω
  simp [controlledPath,clamp]

private theorem path_terminal (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b) : controlledPath H a b b=controlledIntegral H a b := by
  funext ω
  simp [controlledPath,controlledIntegral,clamp,max_eq_right hab]

theorem terminalIntegral_martingale (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hHtop : MemLp H ∞ sourceLaw) :
    Martingale (fun i => controlledPath H a b (BrownianConstantGirsanovSource.terminalClock b i))
      (BrownianConstantGirsanovSource.terminalFiltration b) (stepLaw H a b) := by
  let _ := stepLaw_probability H a b hab hH
  refine ⟨fun i => ?_,fun i j hij => ?_⟩
  · fin_cases i
    · change StronglyMeasurable[naturalFiltration 0] (controlledPath H a b 0)
      rw [path_zero]; exact stronglyMeasurable_zero
    · change StronglyMeasurable[naturalFiltration b] (controlledPath H a b b)
      rw [path_terminal H a b hab]; exact controlledIntegral_end_past H a b hab hH
  · fin_cases i <;> fin_cases j
    · change (stepLaw H a b)[controlledPath H a b 0 | naturalFiltration 0] =ᵐ[stepLaw H a b] controlledPath H a b 0
      rw [path_zero,condExp_zero]
    · change (stepLaw H a b)[controlledPath H a b b | naturalFiltration 0] =ᵐ[stepLaw H a b] controlledPath H a b 0
      rw [path_terminal H a b hab,path_zero]
      exact controlledIntegral_condExp_zero H a b hab hH hHtop
    · norm_num at hij
    · change (stepLaw H a b)[controlledPath H a b b | naturalFiltration b] =ᵐ[stepLaw H a b] controlledPath H a b b
      rw [path_terminal H a b hab]
      rw [condExp_of_stronglyMeasurable (naturalFiltration.le b) (controlledIntegral_end_past H a b hab hH)
        (controlledIntegral_integrable H a b hab hH hHtop)]

/-- ORIGINAL record from the actual START action, returned baseline input,
actual Q Brownian elementary integral and true original clock-time energy. -/
def actualTerminalData (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hHtop : MemLp H ∞ sourceLaw) :
    TerminalGirsanovData sourceLaw (stepLaw H a b) b (stepControl H a b) where
  density ω := ENNReal.ofReal (stepExponential H a b ω)
  baselineIntegral := baselineIntegral H a b
  controlledIntegral := controlledIntegral H a b
  controlFiltration := BrownianConstantGirsanovSource.controlFiltration
  control_progressive := stepControl_progressive H a b hH
  energy_intervalIntegrable := Eventually.of_forall (fun ω => by
    rw [control_square,intervalIntegrable_iff_integrableOn_Ioc_of_le b.coe_nonneg]
    exact (integrable_const (μ := volume.restrict (Ioc 0 (b : ℝ))) (‖H ω‖^2)).indicator measurableSet_Ioc)
  measurable_density := ((stepExponential_end_past H a b hab hH).mono (naturalFiltration.le b)).measurable.ennreal_ofReal
  changeOfMeasure := rfl
  density_eq_exp := Eventually.of_forall (fun ω => by
    rw [stepControl_energy H a b hab ω,stepEnergy_eq]
    change ENNReal.ofReal (Real.exp (oneStep H a b ω-H ω^2*((b-a : ℝ≥0) : ℝ)/2)) =
      ENNReal.ofReal (Real.exp (oneStep H a b ω-(2 : ℝ)⁻¹*(H ω^2*((b : ℝ)-(a : ℝ)))))
    rw [NNReal.coe_sub hab]
    congr 2
    ring)
  integral_shift := Eventually.of_forall (fun ω => by
    rw [stepControl_energy H a b hab ω,stepEnergy_eq,controlledIntegral_eq_centered H a b hab]
    change H ω*increment a b ω=H ω*(increment a b ω-H ω*((b-a : ℝ≥0) : ℝ))+H ω^2*((b : ℝ)-(a : ℝ))
    rw [NNReal.coe_sub hab]
    ring)
  controlledIntegralProcess i := controlledPath H a b (BrownianConstantGirsanovSource.terminalClock b i)
  controlledFiltration := BrownianConstantGirsanovSource.terminalFiltration b
  controlledIntegral_martingale := terminalIntegral_martingale H a b hab hH hHtop
  controlledIntegral_initial := path_zero H a b
  controlledIntegral_terminal := path_terminal H a b hab
  energy_integrable := by
    have he : controlEnergy b (stepControl H a b)=stepEnergy H a b := funext (stepControl_energy H a b hab)
    rw [he]
    exact stepLaw_energy_integrable H a b hab hH (hHtop.mono_exponent le_top)

/-- Actual expected energy is evaluated from the ORIGINAL coefficient law;
the Q-energy is not an externally supplied budget or selected sample. -/
theorem actual_energy_mean (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    (∫ ω, controlEnergy b (stepControl H a b) ω ∂stepLaw H a b)=
      (∫ ω, H ω^2 ∂sourceLaw)*((b : ℝ)-(a : ℝ)) := by
  have he : controlEnergy b (stepControl H a b)=fun ω => H ω^2*((b : ℝ)-(a : ℝ)) :=
    funext (fun ω => (stepControl_energy H a b hab ω).trans (stepEnergy_eq H a b ω))
  rw [he,integral_mul_const]
  congr 1
  have hg : Measurable H := (hH.mono (naturalFiltration.le a)).measurable
  rw [← integral_map hg.aemeasurable (f := fun x : ℝ => x^2) (by fun_prop),stepLaw_map_coefficient H a b hab hH,
    integral_map hg.aemeasurable (by fun_prop)]

/-- Direct ORIGINAL P-KL-05 on an actual bounded observed START action,
with computed original-source expected energy and ANY measurable readout. -/
theorem actual_p_kl_05 {Γ : Type*} [MeasurableSpace Γ]
    (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hHtop : MemLp H ∞ sourceLaw)
    (readout : (ℝ≥0 → ℝ) → Γ) (hreadout : Measurable readout) :
    klDiv (stepLaw H a b) sourceLaw = ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, H ω^2 ∂sourceLaw)*((b : ℝ)-(a : ℝ))) ∧
    klDiv ((stepLaw H a b).map readout) (sourceLaw.map readout) ≤
      ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, H ω^2 ∂sourceLaw)*((b : ℝ)-(a : ℝ))) := by
  let _ := stepLaw_probability H a b hab hH
  have h := (actualTerminalData H a b hab hH hHtop).p_kl_05 readout hreadout
  rw [actual_energy_mean H a b hab hH] at h
  simpa only [one_div,mul_assoc] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepGirsanovSource
