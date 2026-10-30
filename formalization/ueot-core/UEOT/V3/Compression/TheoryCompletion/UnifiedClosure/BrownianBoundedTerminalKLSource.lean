import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalMeanSource

/-!
Original commitment: original P-KL-05 must consume SAME full predictable control, actual input integral and own change of measure.
Existing result: SAME bounded input owns normalized exponential Q, actual real progressive control/energy and actual controlled terminal mean zero.
Premise reduced: construct ORIGINAL TerminalGirsanovData including a true terminal martingale in original Fs0/FsT, without desired fields.
Model/witness: canonical nonzero-noise Brownian source, native fullPredictableL2 f bounded AE by K, real dt energy, T=0 included.
Consumer/boundary: actual KL and every measurable readout; a general Q stochastic-integral framework and broader filtered/vector sources remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalKLSource
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeEnergy BrownianIntegralContinuousVersion
open BrownianBoundedControlSource BrownianBoundedExponentialLimitSource BrownianBoundedTerminalL2Source BrownianBoundedTerminalMeanSource
open UEOT.V3.GirsanovPathKL
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual terminal version preserves exact original FsT measurability;
its SAME native L2 terminal class is proved below, not substituted by choice. -/
def terminalValue (T : ℝ≥0) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) : ℝ :=
  continuousIntegralProcess T f T ω-timeEnergy T f T ω

theorem terminalValue_past (T : ℝ≥0) (f : fullPredictableL2 T) :
    StronglyMeasurable[naturalFiltration T] (terminalValue T f) :=
  (continuousIntegralProcess_stronglyAdapted T f T).sub (timeEnergy_stronglyAdapted T f T)

theorem terminalValue_eq_actual (T : ℝ≥0) (f : fullPredictableL2 T) :
    terminalValue T f=ᵐ[sourceLaw] controlledTerminal T f :=
  (continuousIntegralProcess_horizon T f).sub (EventuallyEq.refl _ _)

theorem terminalValue_integrable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Integrable (terminalValue T f) (fullLaw T f) :=
  (controlledTerminal_integrable_fullLaw T f K hK hbound).congr
    ((fullLaw_absolutelyContinuous T f).ae_le (terminalValue_eq_actual T f).symm)

theorem terminalValue_mean_zero (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    (∫ ω, terminalValue T f ω ∂fullLaw T f)=0 := by
  rw [integral_congr_ae ((fullLaw_absolutelyContinuous T f).ae_le (terminalValue_eq_actual T f))]
  exact controlledTerminal_mean_zero T f K hK hbound

/-- Entire original zero past is constant on ONE actual-Q full-measure
set. Independence and terminal conditional mean are therefore derived in
original Fs0, without replacing that filtration by bottom. -/
theorem terminalValue_condExp_zero (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    (fullLaw T f)[terminalValue T f | naturalFiltration 0]=ᵐ[fullLaw T f] fun _ => 0 := by
  let := fullLaw_probability T f K hK hbound
  have hPast : (fun ω (u : Iic (0 : ℝ≥0)) => process u ω)=ᵐ[fullLaw T f] fun _ => (0 : Iic (0 : ℝ≥0) → ℝ) := by
    filter_upwards [(fullLaw_absolutelyContinuous T f).ae_le process_zero] with ω hz
    funext u
    have hu : (u : ℝ≥0)=0 := le_antisymm u.property (zero_le)
    simpa only [hu,Pi.zero_apply] using hz
  have hind : Indep (MeasurableSpace.comap (terminalValue T f) inferInstance) (naturalFiltration 0) (fullLaw T f) := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact (indepFun_const_right (μ := fullLaw T f) (terminalValue T f) (0 : Iic (0 : ℝ≥0) → ℝ)).congr
      (EventuallyEq.refl _ _) hPast.symm
  have hm := (terminalValue_past T f).mono (naturalFiltration.le T)
  have hc : @Measurable (ℝ≥0 → ℝ) ℝ (MeasurableSpace.comap (terminalValue T f) inferInstance)
      inferInstance (terminalValue T f) := measurable_iff_comap_le.mpr le_rfl
  have h := condExp_indep_eq hm.measurable.comap_le (naturalFiltration.le 0) hc.stronglyMeasurable hind
  simpa only [terminalValue_mean_zero T f K hK hbound] using h

/-- Literal two-clock terminal process, returning the actual terminal
version. This does not posit a general stochastic integrator under Q. -/
def terminalProcess (T : ℝ≥0) (f : fullPredictableL2 T) (i : Fin 2) : (ℝ≥0 → ℝ) → ℝ :=
  if i=0 then 0 else terminalValue T f

theorem terminalProcess_martingale (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Martingale (terminalProcess T f) (BrownianConstantGirsanovSource.terminalFiltration T) (fullLaw T f) := by
  let := fullLaw_probability T f K hK hbound
  refine ⟨fun i => ?_,fun i j hij => ?_⟩
  · fin_cases i
    · exact stronglyMeasurable_zero
    · exact terminalValue_past T f
  · fin_cases i <;> fin_cases j
    · change (fullLaw T f)[0 | naturalFiltration 0]=ᵐ[fullLaw T f] (0 : (ℝ≥0 → ℝ) → ℝ)
      rw [condExp_zero]
    · change (fullLaw T f)[terminalValue T f | naturalFiltration 0]=ᵐ[fullLaw T f] (0 : (ℝ≥0 → ℝ) → ℝ)
      exact terminalValue_condExp_zero T f K hK hbound
    · norm_num at hij
    · change (fullLaw T f)[terminalValue T f | naturalFiltration T]=ᵐ[fullLaw T f] terminalValue T f
      rw [condExp_of_stronglyMeasurable (naturalFiltration.le T) (terminalValue_past T f)
        (terminalValue_integrable T f K hK hbound)]

theorem actualEnergy_integrable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Integrable (timeEnergy T f T) (fullLaw T f) := by
  let := fullLaw_probability T f K hK hbound
  apply (MemLp.of_bound ((timeEnergy_stronglyAdapted T f T).mono (naturalFiltration.le T)).aestronglyMeasurable
    (K^2*(T : ℝ)) (p := 1) ?_).integrable le_rfl
  filter_upwards [(fullLaw_absolutelyContinuous T f).ae_le (fullEnergy_bound T f K hK hbound)] with ω h
  simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2

/-- ORIGINAL terminal certificate, with every source field constructed
from SAME f, its actual own density, actual real control and derived martingale. -/
def actualTerminalData (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    TerminalGirsanovData sourceLaw (fullLaw T f) T (control T f K) where
  density ω := ENNReal.ofReal (fullDensity T f ω)
  baselineIntegral := (predictableIntegral T f : (ℝ≥0 → ℝ) → ℝ)
  controlledIntegral := terminalValue T f
  controlFiltration := BrownianConstantGirsanovSource.controlFiltration
  control_progressive := control_progressive T f K
  energy_intervalIntegrable := Eventually.of_forall (control_energy_intervalIntegrable T f K hK)
  measurable_density := (fullDensity_measurable T f).ennreal_ofReal
  changeOfMeasure := rfl
  density_eq_exp := by
    filter_upwards [control_energy_eq_actual T f K hbound] with ω he
    rw [he]
    simp only [fullDensity,one_div]
  integral_shift := by
    filter_upwards [(fullLaw_absolutelyContinuous T f).ae_le (continuousIntegralProcess_horizon T f),
      (fullLaw_absolutelyContinuous T f).ae_le (control_energy_eq_actual T f K hbound)] with ω hi he
    rw [he,terminalValue,hi]
    ring
  controlledIntegralProcess := terminalProcess T f
  controlledFiltration := BrownianConstantGirsanovSource.terminalFiltration T
  controlledIntegral_martingale := terminalProcess_martingale T f K hK hbound
  controlledIntegral_initial := by simp [terminalProcess]
  controlledIntegral_terminal := by norm_num [terminalProcess]
  energy_integrable := (actualEnergy_integrable T f K hK hbound).congr
    ((fullLaw_absolutelyContinuous T f).ae_le (control_energy_eq_actual T f K hbound).symm)

/-- Direct original P-KL-05 for the actual bounded full input. Its energy
expectation is under OWN final Q; it is not replaced by its source-P expectation. -/
theorem actual_p_kl_05 (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)
    {Γ : Type*} [MeasurableSpace Γ] (readout : (ℝ≥0 → ℝ) → Γ) (hreadout : Measurable readout) :
    klDiv (fullLaw T f) sourceLaw=ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, timeEnergy T f T ω ∂fullLaw T f)) ∧
    klDiv ((fullLaw T f).map readout) (sourceLaw.map readout)≤
      ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, timeEnergy T f T ω ∂fullLaw T f)) := by
  let := fullLaw_probability T f K hK hbound
  have h := (actualTerminalData T f K hK hbound).p_kl_05 readout hreadout
  have he := integral_congr_ae ((fullLaw_absolutelyContinuous T f).ae_le (control_energy_eq_actual T f K hbound))
  simpa only [he,one_div] using h

/-- Explicit sufficient energy bound, under SAME final Q, for the full
path law and every measurable readout. No source-P cost substitution. -/
theorem actual_kl_bound (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)
    {Γ : Type*} [MeasurableSpace Γ] (readout : (ℝ≥0 → ℝ) → Γ) (hreadout : Measurable readout) :
    klDiv (fullLaw T f) sourceLaw≤ENNReal.ofReal ((1/2 : ℝ)*K^2*(T : ℝ)) ∧
    klDiv ((fullLaw T f).map readout) (sourceLaw.map readout)≤ENNReal.ofReal ((1/2 : ℝ)*K^2*(T : ℝ)) := by
  let := fullLaw_probability T f K hK hbound
  have hbQ : ∀ᵐ ω ∂fullLaw T f, timeEnergy T f T ω≤K^2*(T : ℝ) := by
    filter_upwards [(fullLaw_absolutelyContinuous T f).ae_le (fullEnergy_bound T f K hK hbound)] with ω h
    exact h.2
  have hE : (∫ ω, timeEnergy T f T ω ∂fullLaw T f)≤K^2*(T : ℝ) := by
    have h := integral_mono_ae (actualEnergy_integrable T f K hK hbound)
      (integrable_const (K^2*(T : ℝ)))
      hbQ
    simpa using h
  have hhalf : ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, timeEnergy T f T ω ∂fullLaw T f))≤
      ENNReal.ofReal ((1/2 : ℝ)*K^2*(T : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have h := actual_p_kl_05 T f K hK hbound readout hreadout
  exact ⟨h.1.le.trans hhalf,h.2.trans hhalf⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalKLSource
