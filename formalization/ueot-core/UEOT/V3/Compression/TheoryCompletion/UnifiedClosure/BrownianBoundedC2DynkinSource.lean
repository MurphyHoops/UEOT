import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianScalarItoSource
import UEOT.V3.RecoveryDynkin

/-!
Original commitment: the original P-REC-02 Dynkin interface needs an actual stochastic source, not a desired derivative field.
Existing result: actual scalar C2 Ito for the SAME continuous integral, genuine predictable inputs and source Brownian motion.
Premise reduced: construct constant-noise input and derive the actual expectation primitive, AC and generator identity.
Model/witness: X=x0+sigma*B on the SAME sourceLaw, explicit globally bounded first/second derivatives, including a nonzero-noise witness.
Consumer: ORIGINAL DynkinExpectationCertificate/P-REC-02; general drift/SDE, other filtered sources and recurrence/coercivity remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedC2DynkinSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianIntegralClosure BrownianTimeIntegrand
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralFinitePaths BrownianCommonRefinement
open BrownianIntegralContinuousVersion BrownianIntegralMartingale BrownianIntegralTimeEnergy
open BrownianScalarItoSource BrownianIntegralWeightedQV
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual one-step input: the coefficient only uses the original zero-time past. -/
def constantRecord (T : ℝ≥0) (σ : ℝ) : ElementaryInput T where
  n := 1
  clock := ![0,T]
  coefficient := fun _ _ => σ
  clock_mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := fun _ => stronglyMeasurable_const
  coefficient_bounded := fun _ => memLp_top_const σ

def constantInput (T : ℝ≥0) (σ : ℝ) : fullPredictableL2 T :=
  literalPredictableInput (constantRecord T σ)

/-- The actual returned process uses the original Brownian readout, at every
clock in the actual horizon, on one common full-measure event. -/
theorem constantInput_process (T : ℝ≥0) (σ : ℝ) :
    ∀ᵐ ω ∂sourceLaw, ∀ u : ℝ≥0, u ≤ T →
      continuousIntegralProcess T (constantInput T σ) u ω = σ*BrownianContinuousSource.process u ω := by
  filter_upwards [continuousIntegralProcess_returns_literal (constantRecord T σ),
    BrownianContinuousSource.process_zero] with ω hω hz
  intro u hu
  have he := hω u
  change continuousIntegralProcess T (constantInput T σ) u ω = _ at he
  change continuousIntegralProcess T (constantInput T σ) u ω =
    ∑ i : Fin 1, σ*(BrownianContinuousSource.process (clamp (![0,T] i.castSucc) (![0,T] i.succ) u) ω-
      BrownianContinuousSource.process (![0,T] i.castSucc) ω) at he
  rw [Fin.sum_univ_one] at he
  simpa [clamp,min_eq_right hu,max_eq_right (show 0 ≤ u from bot_le),hz] using he

/-- Actual native product-L2 representative is the supplied constant on the
original time support; no input/candidate rebinding is assumed. -/
theorem constantInput_coe (T : ℝ≥0) (σ : ℝ) :
    (constantInput T σ : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T] fun _ => σ := by
  have hc := (integrand_memLp_two T (constantRecord T σ).clock (constantRecord T σ).coefficient
    (constantRecord T σ).coefficient_bounded).coeFn_toLp
  filter_upwards [hc,time_support_ae T] with p hp hs
  change (constantInput T σ : Lp ℝ 2 (inputLaw T)) p = _ at hp
  rw [hp]
  change (∑ i : Fin 1, intervalIntegrand (fun _ => σ) (![0,T] i.castSucc) (![0,T] i.succ) p) = σ
  rw [Fin.sum_univ_one]
  simp [intervalIntegrand,hs]

theorem constantInput_representative (T : ℝ≥0) (σ : ℝ) :
    representative T (constantInput T σ) =ᵐ[inputLaw T] fun _ => σ :=
  (representative_ae T (constantInput T σ)).symm.trans (constantInput_coe T σ)

/-- Mean zero is inherited from the original actual natural-filtration
martingale, not imposed on the continuous modification. -/
theorem continuousIntegralProcess_mean_zero (T u : ℝ≥0) (f : fullPredictableL2 T) :
    (∫ ω, continuousIntegralProcess T f u ω ∂sourceLaw) = 0 := by
  rw [integral_congr_ae (continuousIntegralProcess_eq_actual T u f)]
  exact integralProcess_mean_zero T u f

/-- Actual real-time process, with nonnegative-time readout for the original
real-clock Dynkin interface. -/
def state (x₀ σ t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  x₀+σ*BrownianContinuousSource.process (Real.toNNReal t) ω

def stateLaw (x₀ σ t : ℝ) : Measure ℝ := sourceLaw.map (state x₀ σ t)

def generator (σ : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (σ^2/2)*iteratedDeriv 2 φ x

theorem state_measurable (x₀ σ t : ℝ) : Measurable (state x₀ σ t) :=
  measurable_const.add (measurable_const.mul (BrownianContinuousSource.measurable_process _))

theorem state_continuous_time (x₀ σ : ℝ) (ω : ℝ≥0 → ℝ) : Continuous (fun t => state x₀ σ t ω) :=
  continuous_const.add (continuous_const.mul ((BrownianContinuousSource.process_continuous ω).comp continuous_real_toNNReal))

instance stateLaw_probability (x₀ σ t : ℝ) : IsProbabilityMeasure (stateLaw x₀ σ t) :=
  Measure.isProbabilityMeasure_map (state_measurable x₀ σ t).aemeasurable

/-- The shifted test retains the caller's actual derivatives. -/
theorem shift_deriv (φ : ℝ → ℝ) (x₀ x : ℝ) :
    deriv (fun y => φ (x₀+y)) x = deriv φ (x₀+x) := by
  simpa only [iteratedDeriv_one] using congrFun (iteratedDeriv_comp_const_add 1 φ x₀) x

theorem shift_second (φ : ℝ → ℝ) (x₀ x : ℝ) :
    iteratedDeriv 2 (fun y => φ (x₀+y)) x = iteratedDeriv 2 φ (x₀+x) :=
  congrFun (iteratedDeriv_comp_const_add 2 φ x₀) x

/-- Same original product/time source: the actual Ito correction for the
constructed input is the literal Brownian generator integrand. -/
theorem constantInput_second_integrand (T : ℝ≥0) (x₀ σ : ℝ) (φ : ℝ → ℝ) :
    weightedTimeIntegrand T
      (fun u ω => iteratedDeriv 2 (fun y => φ (x₀+y))
        (continuousIntegralProcess T (constantInput T σ) u ω)) (constantInput T σ)
    =ᵐ[inputLaw T] fun p => σ^2*iteratedDeriv 2 φ (state x₀ σ p.1 p.2) := by
  have hp : ∀ᵐ p ∂inputLaw T, ∀ u : ℝ≥0, u ≤ T →
      continuousIntegralProcess T (constantInput T σ) u p.2 = σ*BrownianContinuousSource.process u p.2 :=
    Measure.quasiMeasurePreserving_snd.ae (constantInput_process T σ)
  filter_upwards [hp,time_support_ae T,constantInput_representative T σ] with p hp hs hr
  have hu : Real.toNNReal p.1 ≤ T := (Real.toNNReal_le_iff_le_coe).mpr hs.2
  simp only [weightedTimeIntegrand,hr,hp _ hu,shift_second,state]
  ring

/-- Bounded second derivative makes the actual time correction integrable;
Fubini then computes its mean on the SAME inputLaw. -/
theorem constantInput_second_mean (T : ℝ≥0) (x₀ σ : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ 2 φ) (K₂ : ℝ) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖ ≤ K₂) :
    (∫ ω, itoSecondEnergy T (constantInput T σ) (fun y => φ (x₀+y)) ω ∂sourceLaw) =
      ∫ t, ∫ ω, σ^2*iteratedDeriv 2 φ (state x₀ σ t ω) ∂sourceLaw ∂timeLaw T := by
  have hψ : ContDiff ℝ 2 (fun y => φ (x₀+y)) := hφ.comp (contDiff_const.add contDiff_id)
  have hm : Measurable (Function.uncurry (fun u ω => iteratedDeriv 2 (fun y => φ (x₀+y))
      (continuousIntegralProcess T (constantInput T σ) u ω))) :=
    (hψ.continuous_iteratedDeriv' 2).measurable.comp (continuousIntegralProcess_measurable T (constantInput T σ))
  have hb : ∀ u ω, ‖iteratedDeriv 2 (fun y => φ (x₀+y))
      (continuousIntegralProcess T (constantInput T σ) u ω)‖ ≤ K₂ := by
    intro u ω; rw [shift_second]; exact hb₂ _
  have hi := weightedTimeIntegrand_integrable T _ hm K₂ hb (constantInput T σ)
  unfold itoSecondEnergy weightedTimeEnergy
  rw [← integral_prod_symm _ hi]
  change (∫ p, weightedTimeIntegrand T _ (constantInput T σ) p ∂inputLaw T) = _
  exact (integral_congr_ae (constantInput_second_integrand T x₀ σ φ)).trans
    (integral_prod _ (hi.congr (constantInput_second_integrand T x₀ σ φ)))

/-- Source expectation form of actual Ito. Its martingale term has actual
mean zero, derived from the original filtration and returned integral. -/
theorem constantInput_expectation (T : ℝ≥0) (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hb₁ : ∀ x, ‖deriv φ x‖ ≤ K₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖ ≤ K₂) :
    (∫ ω, φ (state x₀ σ T ω) ∂sourceLaw) = φ x₀+
      ∫ t, ∫ ω, generator σ φ (state x₀ σ t ω) ∂sourceLaw ∂timeLaw T := by
  let ψ := fun y => φ (x₀+y)
  have hψ : ContDiff ℝ 2 ψ := hφ.comp (contDiff_const.add contDiff_id)
  have hbψ : ∀ x, ‖deriv ψ x‖ ≤ K₁ := by
    intro x; rw [show deriv ψ x = deriv φ (x₀+x) from shift_deriv φ x₀ x]; exact hb₁ _
  have hbψ₂ : ∀ x, ‖iteratedDeriv 2 ψ x‖ ≤ K₂ := by
    intro x; rw [show iteratedDeriv 2 ψ x = iteratedDeriv 2 φ (x₀+x) from shift_second φ x₀ x]; exact hb₂ _
  have hito := actual_scalar_ito T (constantInput T σ) ψ hψ K₁ K₂ hK₁ hK₂ hbψ hbψ₂
  have he : (fun ω => φ (state x₀ σ T ω)) =ᵐ[sourceLaw] fun ω =>
      ψ 0+continuousIntegralProcess T (itoInput T (constantInput T σ) ψ hψ K₁ hK₁ hbψ) T ω+
      (1/2 : ℝ)*itoSecondEnergy T (constantInput T σ) ψ ω := by
    filter_upwards [hito,constantInput_process T σ] with ω hi hp
    rw [hp T le_rfl] at hi
    simpa [ψ,state] using hi
  have hI := (continuousIntegralProcess_memLp_two T T (itoInput T (constantInput T σ) ψ hψ K₁ hK₁ hbψ)).integrable (by norm_num)
  have hm : Measurable (Function.uncurry (fun u ω => iteratedDeriv 2 ψ
      (continuousIntegralProcess T (constantInput T σ) u ω))) :=
    (hψ.continuous_iteratedDeriv' 2).measurable.comp (continuousIntegralProcess_measurable T (constantInput T σ))
  have hA : Integrable (itoSecondEnergy T (constantInput T σ) ψ) sourceLaw :=
    (weightedTimeIntegrand_integrable T _ hm K₂ (fun u ω => hbψ₂ _) (constantInput T σ)).integral_prod_right
  rw [integral_congr_ae he,integral_add (f := fun ω => ψ 0+continuousIntegralProcess T (itoInput T (constantInput T σ) ψ hψ K₁ hK₁ hbψ) T ω)
    (g := fun ω => (1/2 : ℝ)*itoSecondEnergy T (constantInput T σ) ψ ω)
    ((integrable_const _).add hI) (hA.const_mul _),
    integral_add (f := fun _ => ψ 0) (integrable_const _) hI,continuousIntegralProcess_mean_zero,integral_const,
    probReal_univ,one_smul,add_zero,integral_const_mul]
  change φ (x₀+0)+(1/2 : ℝ)*(∫ ω, itoSecondEnergy T (constantInput T σ) (fun y => φ (x₀+y)) ω ∂sourceLaw) = _
  rw [constantInput_second_mean T x₀ σ φ hφ K₂ hb₂,← integral_const_mul]
  simp only [generator,integral_const_mul,add_zero]
  congr 1
  ring

/-- Actual source readout has native L2 integrability, inherited from the
constructed literal input and its returned integral. -/
theorem state_memLp_two (x₀ σ t : ℝ) : MemLp (state x₀ σ t) 2 sourceLaw := by
  have hm := continuousIntegralProcess_memLp_two (Real.toNNReal t) (Real.toNNReal t)
    (constantInput (Real.toNNReal t) σ)
  have he : continuousIntegralProcess (Real.toNNReal t) (constantInput (Real.toNNReal t) σ) (Real.toNNReal t)
      =ᵐ[sourceLaw] fun ω => σ*BrownianContinuousSource.process (Real.toNNReal t) ω :=
    (constantInput_process (Real.toNNReal t) σ).mono (fun _ h => h _ le_rfl)
  exact (memLp_const x₀).add (hm.ae_eq he)

/-- Bounded first derivative provides integrability of the actual test on
its actual pushforward law; no moment/domain certificate is assumed. -/
theorem stateLaw_test_integrable (x₀ σ t : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, ‖deriv φ x‖ ≤ K) : Integrable φ (stateLaw x₀ σ t) := by
  have hl : LipschitzWith ⟨K,hK⟩ φ :=
    lipschitzWith_of_nnnorm_deriv_le (hφ.differentiable (by norm_num))
      (fun x => by exact_mod_cast hb x)
  have hx := (state_memLp_two x₀ σ t).integrable (by norm_num)
  have hdom : Integrable (fun ω => ‖φ 0‖+K*‖state x₀ σ t ω‖) sourceLaw :=
    (integrable_const _).add (hx.norm.const_mul _)
  have hi : Integrable (fun ω => φ (state x₀ σ t ω)) sourceLaw := by
    apply hdom.mono' (hφ.continuous.measurable.comp (state_measurable x₀ σ t)).aestronglyMeasurable
    filter_upwards [] with ω
    have hd := hl.norm_sub_le (state x₀ σ t ω) 0
    have hn := norm_add_le (φ (state x₀ σ t ω)-φ 0) (φ 0)
    simp only [sub_zero] at hd
    change ‖φ (state x₀ σ t ω)-φ 0‖ ≤ K*‖state x₀ σ t ω‖ at hd
    change ‖φ (state x₀ σ t ω)‖ ≤ _
    rw [sub_add_cancel] at hn
    linarith
  exact (integrable_map_measure hφ.continuous.aestronglyMeasurable (state_measurable x₀ σ t).aemeasurable).2 hi

/-- The actual expected generator is continuous by dominated convergence
on the original probability source. -/
theorem expected_generator_continuous (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₂ : ℝ) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖ ≤ K₂) :
    Continuous (fun t => ∫ x, generator σ φ x ∂stateLaw x₀ σ t) := by
  have hc : Continuous (generator σ φ) := continuous_const.mul (hφ.continuous_iteratedDeriv' 2)
  have he (t : ℝ) : (∫ x, generator σ φ x ∂stateLaw x₀ σ t) =
      ∫ ω, generator σ φ (state x₀ σ t ω) ∂sourceLaw :=
    integral_map (state_measurable x₀ σ t).aemeasurable hc.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖σ^2/2‖*K₂)
  · intro t
    exact (hc.measurable.comp (state_measurable x₀ σ t)).aestronglyMeasurable
  · intro t
    filter_upwards [] with ω
    simpa only [generator,norm_mul] using mul_le_mul_of_nonneg_left (hb₂ (state x₀ σ t ω)) (norm_nonneg (σ^2/2))
  · exact integrable_const _
  · exact Eventually.of_forall (fun ω => hc.comp (state_continuous_time x₀ σ ω))

/-- Real-clock actual expectation equals its generator primitive, obtained
from actual Ito, actual zero mean and native Fubini. -/
theorem stateLaw_expectation_primitive (x₀ σ t : ℝ) (ht : 0 ≤ t) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hb₁ : ∀ x, ‖deriv φ x‖ ≤ K₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖ ≤ K₂) :
    (∫ x, φ x ∂stateLaw x₀ σ t) = φ x₀+
      ∫ s in 0..t, ∫ x, generator σ φ x ∂stateLaw x₀ σ s := by
  rw [stateLaw,integral_map (state_measurable x₀ σ t).aemeasurable hφ.continuous.aestronglyMeasurable]
  have he := constantInput_expectation (Real.toNNReal t) x₀ σ φ hφ K₁ K₂ hK₁ hK₂ hb₁ hb₂
  rw [Real.coe_toNNReal _ ht] at he
  rw [he]
  congr 1
  change (∫ s in Icc 0 (Real.toNNReal t : ℝ), ∫ ω, generator σ φ (state x₀ σ s ω) ∂sourceLaw) = _
  rw [Real.coe_toNNReal _ ht,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht]
  apply intervalIntegral.integral_congr
  intro s _
  exact (integral_map (state_measurable x₀ σ s).aemeasurable
    (continuous_const.mul (hφ.continuous_iteratedDeriv' 2)).aestronglyMeasurable).symm

/-- ORIGINAL DynkinExpectationCertificate is now a theorem of the actual
source, actual constant input and original C2 test, not an external premise. -/
theorem actual_boundedC2_dynkin (x₀ σ T : ℝ) (hT : 0 ≤ T) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hb₁ : ∀ x, ‖deriv φ x‖ ≤ K₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖ ≤ K₂) :
    UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate
      (fun t => ∫ x, φ x ∂stateLaw x₀ σ t)
      (fun t => ∫ x, generator σ φ x ∂stateLaw x₀ σ t) T := by
  let ell := fun t => ∫ x, generator σ φ x ∂stateLaw x₀ σ t
  let primitive := fun t => φ x₀+∫ s in 0..t, ell s
  have hell : Continuous ell := expected_generator_continuous x₀ σ φ hφ K₂ hb₂
  have hp (t : ℝ) : HasDerivAt primitive (ell t) t := by
    simpa [primitive] using (intervalIntegral.integral_hasDerivAt_right (hell.intervalIntegrable 0 t)
      hell.aestronglyMeasurable.stronglyMeasurableAtFilter hell.continuousAt).const_add (φ x₀)
  have hpc : ContDiff ℝ 1 primitive := contDiff_one_iff_deriv.mpr ⟨fun t => (hp t).differentiableAt,by
    have he : deriv primitive = ell := funext (fun t => (hp t).deriv)
    rw [he]; exact hell⟩
  have heq := stateLaw_expectation_primitive x₀ σ
  constructor
  · apply ContDiffOn.absolutelyContinuousOnInterval
    apply hpc.contDiffOn.congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact heq t ht.1 φ hφ K₁ K₂ hK₁ hK₂ hb₁ hb₂
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht hne
    have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hne)
    have hev : (fun t => ∫ x, φ x ∂stateLaw x₀ σ t) =ᶠ[𝓝 t] primitive := by
      filter_upwards [Ioi_mem_nhds hpos] with s hs
      exact heq s hs.le φ hφ K₁ K₂ hK₁ hK₂ hb₁ hb₂
    exact ((hp t).congr_of_eventuallyEq hev).deriv

/-- Literal initial law, with the actual Brownian zero-time identity. -/
theorem stateLaw_initial (x₀ σ : ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (∫ x, φ x ∂stateLaw x₀ σ 0) = φ x₀ := by
  rw [stateLaw,integral_map (state_measurable x₀ σ 0).aemeasurable hφ.aestronglyMeasurable]
  have he : (fun ω => φ (state x₀ σ 0 ω)) =ᵐ[sourceLaw] fun _ => φ x₀ := by
    filter_upwards [BrownianContinuousSource.process_zero] with ω hω
    simp [state,hω]
  rw [integral_congr_ae he]
  simp

/-- Actual generator-domain integrability follows from the displayed
bounded second derivative on the actual probability law. -/
theorem stateLaw_generator_integrable (x₀ σ t : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₂ : ℝ) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖ ≤ K₂) :
    Integrable (generator σ φ) (stateLaw x₀ σ t) := by
  apply (integrable_const (μ := stateLaw x₀ σ t) (‖σ^2/2‖*K₂)).mono'
    (continuous_const.mul (hφ.continuous_iteratedDeriv' 2)).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [generator,Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_left (hb₂ x) (norm_nonneg (σ^2/2))

/-- ORIGINAL P-REC-02 now consumes the constructed source certificate.
The pointwise recovery drift and distance domination remain caller hypotheses;
this theorem does not claim that free Brownian motion is recurrent/coercive. -/
theorem actual_source_p_rec_02 (x₀ σ T : ℝ) (hT : 0 ≤ T) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hb₁ : ∀ x, ‖deriv φ x‖ ≤ K₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖ ≤ K₂)
    (d2 : ℝ → ℝ) (hd2 : ∀ t ∈ Icc 0 T, Integrable d2 (stateLaw x₀ σ t))
    (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c)
    (hdrift : ∀ x, generator σ φ x ≤ -a*φ x+b) (hdom : ∀ x, c*d2 x ≤ φ x) :
    ∀ t ∈ Icc 0 T, (∫ x, d2 x ∂stateLaw x₀ σ t) ≤
      (Real.exp (-a*t)*φ x₀+(b/a)*(1-Real.exp (-a*t)))/c :=
  UEOT.V3.RecoveryDynkin.p_rec_02 (stateLaw x₀ σ) φ (generator σ φ) d2 x₀ a b c T ha hb hc hT
    (fun _ _ => inferInstance) (fun t _ => stateLaw_test_integrable x₀ σ t φ hφ K₁ hK₁ hb₁)
    (fun t _ => stateLaw_generator_integrable x₀ σ t φ hφ K₂ hb₂) hd2
    (actual_boundedC2_dynkin x₀ σ T hT φ hφ K₁ K₂ hK₁ hK₂ hb₁ hb₂)
    (stateLaw_initial x₀ σ φ hφ.continuous) hdrift hdom

/-- Genuine nonzero noise is retained by the SAME actual process, rather
than a degenerate deterministic witness hidden behind a certificate. -/
theorem state_displacement_second_moment (x₀ σ t : ℝ) (ht : 0 ≤ t) :
    (∫ ω, (state x₀ σ t ω-x₀)^2 ∂sourceLaw) = σ^2*t := by
  have he : (fun ω => (state x₀ σ t ω-x₀)^2) =ᵐ[sourceLaw]
      fun ω => σ^2*(increment 0 (Real.toNNReal t) ω)^2 := by
    filter_upwards [BrownianContinuousSource.process_zero] with ω hω
    simp [state,increment,hω]
    ring
  rw [integral_congr_ae he,integral_const_mul,increment_square_mean 0 _ bot_le,
    Real.coe_toNNReal _ ht]
  simp

theorem actual_nonzero_noise_witness :
    (∫ ω, (state 3 2 1 ω-3)^2 ∂sourceLaw) = 4 := by
  norm_num [state_displacement_second_moment 3 2 1 (by norm_num)]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedC2DynkinSource
