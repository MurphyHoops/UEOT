import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteGaussianTiltSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralLiteralIntervals
import UEOT.V3.GirsanovPathKL

/-!
Original commitment: ORIGINAL P-KL-05 must consume an actual source integral/density/shifted Brownian construction.
Existing result: SAME Q_T exponential density gives actual W_t=B_t-u min(t,T) Brownian and originalFt martingale; native baseline integral exists.
Premise reduced: construct ORIGINAL TerminalGirsanovData from actual constant input/output, actual shifted literal integral and literal energy, then consume original KL theorem.
Model/witness: every constant real u and finite T including zero, SAME sourceLaw/Q_T/original natural past, genuine nonzero u example.
Consumer: original full-noise KL equality and arbitrary measurable observed-path upper bound; arbitrary predictable control and general SDE remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianConstantGirsanovSource
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianGaussianTiltSource
open BrownianFiniteGaussianTiltSource BrownianOneStepIntegral BrownianIntegralLiteralIntervals
open BrownianPredictableInputs BrownianPredictableDensity
open UEOT.V3.GirsanovPathKL
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def constantControl (u : ℝ) : ℝ → (ℝ≥0 → ℝ) → ℝ := fun _ _ => u

/-- Original real-clock permissions, clipped only at the unavoidable
negative-time extension of the original nonnegative clock. -/
def controlFiltration : Filtration ℝ (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) where
  seq t := naturalFiltration (Real.toNNReal t)
  mono' := fun _ _ h => naturalFiltration.mono (Real.toNNReal_mono h)
  le' := fun t => naturalFiltration.le (Real.toNNReal t)

def baselineInput (u : ℝ) (T : ℝ≥0) : fullPredictableL2 T :=
  intervalInput T 0 T bot_le le_rfl (fun _ => u) stronglyMeasurable_const (memLp_top_const u)

/-- SAME actual finite allowed input and literal original Brownian increment. -/
def baselineIntegral (u : ℝ) (T : ℝ≥0) : (ℝ≥0 → ℝ) → ℝ := oneStep (fun _ => u) 0 T

theorem baseline_returns_actual_integral (u : ℝ) (T : ℝ≥0) :
    (predictableIntegral T (baselineInput u T) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw] baselineIntegral u T := by
  rw [baselineInput,integral_interval_literal]
  exact (oneStep_memLp_two (memLp_top_const u) 0 T).coeFn_toLp

/-- Actual constant-coefficient elementary integral against the proved Q
Brownian, with literal zero initial value before any AE simplification. -/
def controlledIntegralProcess (u : ℝ) (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  u*(shiftedProcess u T t ω-shiftedProcess u T 0 ω)

theorem controlledIntegralProcess_martingale (u : ℝ) (T : ℝ≥0) :
    Martingale (controlledIntegralProcess u T) naturalFiltration (tiltedLaw u T) := by
  have hconst := martingale_const_fun naturalFiltration (tiltedLaw u T)
    (shiftedProcess_stronglyAdapted u T 0) ((shiftedProcess_isPreBrownian u T).integrable_eval 0)
  exact ((shiftedProcess_martingale u T).sub hconst).smul u

def terminalClock (T : ℝ≥0) : Fin 2 → ℝ≥0 := ![0,T]

theorem terminalClock_mono (T : ℝ≥0) : Monotone (terminalClock T) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [terminalClock]

def terminalFiltration (T : ℝ≥0) : Filtration (Fin 2) (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) where
  seq i := naturalFiltration (terminalClock T i)
  mono' := fun _ _ h => naturalFiltration.mono (terminalClock_mono T h)
  le' := fun i => naturalFiltration.le (terminalClock T i)

theorem terminalIntegral_martingale (u : ℝ) (T : ℝ≥0) :
    Martingale (fun i => controlledIntegralProcess u T (terminalClock T i)) (terminalFiltration T) (tiltedLaw u T) := by
  have hm := controlledIntegralProcess_martingale u T
  exact ⟨fun i => hm.stronglyAdapted (terminalClock T i),fun i j hij => hm.condExp_ae_eq (terminalClock_mono T hij)⟩

/-- Energy is computed from the literal original dt integral and supplied
constant, with no energy/source field assumed. -/
theorem constantControl_energy (u : ℝ) (T : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    controlEnergy T (constantControl u) ω=u^2*(T : ℝ) := by
  simp only [controlEnergy,constantControl,intervalIntegral.integral_const,sub_zero,smul_eq_mul,
    Real.norm_eq_abs,sq_abs]
  ring

/-- Actual constant integral shift on the SAME original source, pointwise;
zero-time noise is retained on both sides rather than silently dropped. -/
theorem actual_integral_shift (u : ℝ) (T : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    baselineIntegral u T ω=controlledIntegralProcess u T T ω+controlEnergy T (constantControl u) ω := by
  rw [constantControl_energy]
  unfold baselineIntegral oneStep increment controlledIntegralProcess shiftedProcess
  simp only [Pi.mul_apply,min_self,zero_min,NNReal.coe_zero,mul_zero,sub_zero]
  ring

/-- ORIGINAL terminal record is constructed from the actual source. None
of its density/integral/shift/martingale conclusions is an input hypothesis. -/
def actualTerminalData (u : ℝ) (T : ℝ≥0) :
    TerminalGirsanovData sourceLaw (tiltedLaw u T) T (constantControl u) where
  density ω := ENNReal.ofReal (exponentialProcess u T ω)
  baselineIntegral := baselineIntegral u T
  controlledIntegral := controlledIntegralProcess u T T
  controlFiltration := controlFiltration
  control_progressive := isProgressive_const controlFiltration u
  energy_intervalIntegrable := Eventually.of_forall (fun _ => by
    change IntervalIntegrable (fun _ : ℝ => ‖u‖^2) volume 0 (T : ℝ)
    exact intervalIntegrable_const)
  measurable_density := (measurable_exponentialProcess u T).ennreal_ofReal
  changeOfMeasure := rfl
  density_eq_exp := by
    filter_upwards [process_zero] with ω hω
    rw [constantControl_energy]
    change ENNReal.ofReal (Real.exp (u*process T ω-u^2*(T : ℝ)/2)) =
      ENNReal.ofReal (Real.exp (u*(process T ω-process 0 ω)-(2 : ℝ)⁻¹*(u^2*(T : ℝ))))
    rw [hω]
    congr 2
    ring
  integral_shift := Eventually.of_forall (actual_integral_shift u T)
  controlledIntegralProcess i := controlledIntegralProcess u T (terminalClock T i)
  controlledFiltration := terminalFiltration T
  controlledIntegral_martingale := terminalIntegral_martingale u T
  controlledIntegral_initial := by
    funext ω
    simp [terminalClock,controlledIntegralProcess]
  controlledIntegral_terminal := rfl
  energy_integrable := by
    have he : controlEnergy T (constantControl u) = fun _ => u^2*(T : ℝ) := funext (constantControl_energy u T)
    rw [he]
    exact integrable_const _

/-- ORIGINAL full-noise P-KL equality, for the SAME normalized Q and
constructed baseline/controlled integrals, with actual computed energy. -/
theorem actual_fullSpaceKL (u : ℝ) (T : ℝ≥0) :
    klDiv (tiltedLaw u T) sourceLaw = ENNReal.ofReal ((1/2 : ℝ)*u^2*(T : ℝ)) := by
  rw [(actualTerminalData u T).fullSpaceKL_eq_halfEnergy]
  have he : controlEnergy T (constantControl u) = fun _ => u^2*(T : ℝ) := funext (constantControl_energy u T)
  rw [he,integral_const,probReal_univ,one_smul]
  congr 1
  ring

/-- ORIGINAL P-KL-05 data-processing bound for ANY caller measurable
observed path/readout of the SAME source experiment. -/
theorem actual_observedPathKL {Γ : Type*} [MeasurableSpace Γ] (u : ℝ) (T : ℝ≥0)
    (readout : (ℝ≥0 → ℝ) → Γ) (hreadout : Measurable readout) :
    klDiv ((tiltedLaw u T).map readout) (sourceLaw.map readout) ≤ ENNReal.ofReal ((1/2 : ℝ)*u^2*(T : ℝ)) := by
  rw [← actual_fullSpaceKL u T]
  exact klDiv_map_le (tiltedLaw u T) sourceLaw hreadout

/-- Direct ORIGINAL P-KL-05 consumer of the actual source-derived record. -/
theorem actual_p_kl_05 {Γ : Type*} [MeasurableSpace Γ] (u : ℝ) (T : ℝ≥0)
    (readout : (ℝ≥0 → ℝ) → Γ) (hreadout : Measurable readout) :
    klDiv (tiltedLaw u T) sourceLaw = ENNReal.ofReal ((1/2 : ℝ)*u^2*(T : ℝ)) ∧
    klDiv ((tiltedLaw u T).map readout) (sourceLaw.map readout) ≤ ENNReal.ofReal ((1/2 : ℝ)*u^2*(T : ℝ)) := by
  have h := (actualTerminalData u T).p_kl_05 readout hreadout
  have he : controlEnergy T (constantControl u) = fun _ => u^2*(T : ℝ) := funext (constantControl_energy u T)
  have hx : (2 : ℝ)⁻¹*(u^2*(T : ℝ))=(1/2 : ℝ)*u^2*(T : ℝ) := by ring
  simpa only [he,integral_const,probReal_univ,one_smul,hx] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianConstantGirsanovSource
