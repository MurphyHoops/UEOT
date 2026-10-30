import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUSemigroupSource
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Original commitment: continuous recovery must use an actual OU state with derived restoring dynamics driven by SAME physical-clock Brownian source.
Existing result: canonical continuous Brownian B/sourceLaw is constructed; old time-changed OU Gaussian transition kernel/semigroup and quadratic recovery hold on their explicit time-changed filtration.
Premise reduced: construct physical-clock Volterra state and derive its real integral equation, continuity and actual initial identity; no OU/SDE source certificate input.
Model/witness: fixed canonical B, real k/sigma/x0 (k>0 for later recovery), nonzero k1/sigma2 witness; k0/sigma0 and time0 are literal boundaries.
Consumer/boundary: physical OU conditional Gaussian/moment and ORIGINAL kernel/p_rec_02 source bridge; new physical state is NOT identified samplewise with old time-changed OU before a genuine law bridge.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalVolterraSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Real-clock readout of the SAME constructed source, extended constantly
at negative times only to apply ordinary real FTC without endpoint artifacts. -/
def brownianReadout (t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ := process (Real.toNNReal t) ω-process 0 ω

theorem brownianReadout_continuous (ω : ℝ≥0 → ℝ) : Continuous (fun t => brownianReadout t ω) :=
  ((process_continuous ω).comp continuous_real_toNNReal).sub continuous_const

theorem brownianReadout_joint : Measurable (Function.uncurry brownianReadout) :=
  (measurable_joint_process.comp ((measurable_fst.real_toNNReal).prodMk measurable_snd)).sub
    ((measurable_process 0).comp measurable_snd)

def primitive (k : ℝ) (t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, Real.exp (k*s)*brownianReadout s ω

/-- Joint measurability of the actual real path primitive, from native
parameter integration. No desired process/measurability certificate is supplied. -/
theorem primitive_joint (k : ℝ) : Measurable (Function.uncurry (primitive k)) := by
  let F : (ℝ × (ℝ≥0 → ℝ)) × ℝ → ℝ := fun q =>
    (Ioc (0 : ℝ) q.1.1).indicator (fun s => Real.exp (k*s)*brownianReadout s q.1.2) q.2
  let G : (ℝ × (ℝ≥0 → ℝ)) × ℝ → ℝ := fun q =>
    (Ioc q.1.1 (0 : ℝ)).indicator (fun s => Real.exp (k*s)*brownianReadout s q.1.2) q.2
  have hw : Measurable (fun q : (ℝ × (ℝ≥0 → ℝ)) × ℝ => Real.exp (k*q.2)*brownianReadout q.2 q.1.2) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (brownianReadout_joint.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hf : Measurable F := by
    exact hw.indicator ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst)))
  have hg : Measurable G := by
    exact hw.indicator ((measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).sub
    (hg.stronglyMeasurable.integral_prod_right' (ν := volume))
  have he : (fun p : ℝ × (ℝ≥0 → ℝ) => primitive k p.1 p.2)=
      fun p => (∫ s, F (p,s))-(∫ s, G (p,s)) := by
    funext p
    rw [primitive,intervalIntegral]
    rw [← integral_indicator measurableSet_Ioc,← integral_indicator measurableSet_Ioc]
  rw [show Function.uncurry (primitive k)=(fun p : ℝ × (ℝ≥0 → ℝ) => primitive k p.1 p.2) from rfl,he]
  exact hi.measurable

theorem weighted_path_continuous (k : ℝ) (ω : ℝ≥0 → ℝ) :
    Continuous (fun s => Real.exp (k*s)*brownianReadout s ω) :=
  (Real.continuous_exp.comp (show Continuous (fun s : ℝ => k*s) from continuous_const.mul continuous_id)).mul (brownianReadout_continuous ω)

theorem primitive_hasDerivAt (k : ℝ) (ω : ℝ≥0 → ℝ) (t : ℝ) :
    HasDerivAt (fun u => primitive k u ω) (Real.exp (k*t)*brownianReadout t ω) t := by
  have hc := weighted_path_continuous k ω
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

def regularPart (k σ x₀ : ℝ) (t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  Real.exp (-k*t)*(x₀-k*σ*primitive k t ω)

/-- Actual physical state, constructed directly from SAME original source
path and its ordinary Lebesgue primitive; no stochastic identity is a field. -/
def state (k σ x₀ : ℝ) (t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ := regularPart k σ x₀ t ω+σ*brownianReadout t ω

theorem regularPart_hasDerivAt (k σ x₀ : ℝ) (ω : ℝ≥0 → ℝ) (t : ℝ) :
    HasDerivAt (fun u => regularPart k σ x₀ u ω) (-k*state k σ x₀ t ω) t := by
  have hd := (((hasDerivAt_id t).const_mul (-k)).exp).mul
    ((hasDerivAt_const t x₀).sub ((primitive_hasDerivAt k ω t).const_mul (k*σ)))
  have he : Real.exp (-k*t)*Real.exp (k*t)=1 := by
    rw [← Real.exp_add]
    have hz : -k*t+k*t=0 := by ring
    rw [hz,Real.exp_zero]
  change HasDerivAt (fun u => regularPart k σ x₀ u ω)
    (Real.exp (-k*t)*(-k*1)*(x₀-k*σ*primitive k t ω)+Real.exp (-k*t)*(0-k*σ*(Real.exp (k*t)*brownianReadout t ω))) t at hd
  apply hd.congr_deriv
  dsimp only [regularPart,state]
  have hh := congrArg (fun z : ℝ => k*σ*brownianReadout t ω*z) he
  nlinarith

theorem regularPart_continuous (k σ x₀ : ℝ) (ω : ℝ≥0 → ℝ) :
    Continuous (fun t => regularPart k σ x₀ t ω) :=
  (show Differentiable ℝ (fun t => regularPart k σ x₀ t ω) from fun t => (regularPart_hasDerivAt k σ x₀ ω t).differentiableAt).continuous

theorem state_continuous (k σ x₀ : ℝ) (ω : ℝ≥0 → ℝ) : Continuous (fun t => state k σ x₀ t ω) :=
  (regularPart_continuous k σ x₀ ω).add (continuous_const.mul (brownianReadout_continuous ω))

theorem regularPart_zero (k σ x₀ : ℝ) (ω : ℝ≥0 → ℝ) : regularPart k σ x₀ 0 ω=x₀ := by
  simp [regularPart,primitive]

/-- Ordinary FTC derives genuine restoring dynamics of the SAME constructed
state at EVERY clock/sample. No desired Volterra/SDE identity is supplied. -/
theorem actual_integral_equation (k σ x₀ : ℝ) (t : ℝ) (ω : ℝ≥0 → ℝ) :
    state k σ x₀ t ω=x₀+σ*brownianReadout t ω-k*(∫ s in (0 : ℝ)..t, state k σ x₀ s ω) := by
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_hs : s∈uIcc (0 : ℝ) t) => regularPart_hasDerivAt k σ x₀ ω s)
    ((continuous_const.mul (state_continuous k σ x₀ ω)).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul,regularPart_zero] at hd
  change regularPart k σ x₀ t ω+σ*brownianReadout t ω=_
  linarith

/-- Centering by the original F0 readout gives literal fixed initial state,
including samples outside the Brownian probability-one event. -/
theorem state_initial (k σ x₀ : ℝ) (ω : ℝ≥0 → ℝ) : state k σ x₀ 0 ω=x₀ := by
  simp [state,regularPart_zero,brownianReadout]

theorem actual_initial (k σ x₀ : ℝ) : state k σ x₀ 0=ᵐ[sourceLaw] fun _ => x₀ :=
  Eventually.of_forall (state_initial k σ x₀)

/-- ONE original B0=0 event gives the physical-clock equation driven by
original canonical B for ALL nonnegative clocks simultaneously. -/
theorem actual_original_source_equation (k σ x₀ : ℝ) : ∀ᵐ ω ∂sourceLaw, ∀ t : ℝ≥0,
    state k σ x₀ t ω=x₀+σ*process t ω-k*(∫ s in (0 : ℝ)..(t : ℝ),state k σ x₀ s ω) := by
  filter_upwards [process_zero] with ω hω
  intro t
  simpa only [brownianReadout,Real.toNNReal_coe,hω,sub_zero] using actual_integral_equation k σ x₀ t ω

theorem zero_restoring_rate (σ x₀ t : ℝ) (ω : ℝ≥0 → ℝ) : state 0 σ x₀ t ω=x₀+σ*brownianReadout t ω := by
  simp [state,regularPart]

theorem zero_noise (k x₀ t : ℝ) (ω : ℝ≥0 → ℝ) : state k 0 x₀ t ω=Real.exp (-k*t)*x₀ := by
  simp [state,regularPart]

/-- Nonzero restoring and noise parameters consume the actual source path,
not a deterministic/zero-noise proxy. Random spread is a subsequent law proof. -/
theorem actual_nonzero_parameter_equation (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    state 1 2 3 t ω=3+2*(process t ω-process 0 ω)-(∫ s in (0 : ℝ)..(t : ℝ), state 1 2 3 s ω) := by
  simpa only [one_mul,brownianReadout,Real.toNNReal_coe] using actual_integral_equation 1 2 3 t ω

theorem state_joint (k σ x₀ : ℝ) : Measurable (Function.uncurry (state k σ x₀)) := by
  change Measurable (fun p : ℝ × (ℝ≥0 → ℝ) => Real.exp (-k*p.1)*(x₀-k*σ*primitive k p.1 p.2)+σ*brownianReadout p.1 p.2)
  exact ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
    (measurable_const.sub (measurable_const.mul (primitive_joint k)))).add
      (measurable_const.mul brownianReadout_joint)

/-- The primitive reads only the original physical-clock past, through an
explicit clipped time readout on its integration support. -/
theorem primitive_stronglyAdapted (k : ℝ) :
    StronglyAdapted naturalFiltration (fun t : ℝ≥0 => primitive k t) := by
  intro t
  let c : ℝ → Iic t := fun s => ⟨min (Real.toNNReal s) t,by exact min_le_right (Real.toNNReal s) t⟩
  have hc : Measurable c := (measurable_id.real_toNNReal.min measurable_const).subtype_mk
  have hp := process_stronglyAdapted.isStronglyProgressive_of_continuous process_continuous
  have hm : StronglyMeasurable[MeasurableSpace.prod inferInstance (naturalFiltration t)]
      (fun p : ℝ × (ℝ≥0 → ℝ) => process (min (Real.toNNReal p.1) t) p.2) :=
    (hp t).comp_measurable ((hc.comp measurable_fst).prodMk measurable_snd)
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration t
  have hz : StronglyMeasurable (fun p : ℝ × (ℝ≥0 → ℝ) => process 0 p.2) :=
    ((process_stronglyAdapted 0).mono (naturalFiltration.mono (bot_le : (0 : ℝ≥0)≤t))).comp_measurable measurable_snd
  have hw : StronglyMeasurable (fun p : ℝ × (ℝ≥0 → ℝ) => Real.exp (k*p.1)*
      (process (min (Real.toNNReal p.1) t) p.2-process 0 p.2)) :=
    ((Real.continuous_exp.comp (show Continuous (fun s : ℝ => k*s) from continuous_const.mul continuous_id)).measurable.comp measurable_fst).stronglyMeasurable.mul
      (hm.sub hz)
  have he : (fun ω : ℝ≥0 → ℝ => primitive k t ω)=fun ω =>
      ∫ s in Ioc (0 : ℝ) (t : ℝ), Real.exp (k*s)*(process (min (Real.toNNReal s) t) ω-process 0 ω) := by
    funext ω
    rw [primitive,intervalIntegral.integral_of_le t.coe_nonneg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hst : Real.toNNReal s≤t := (Real.toNNReal_le_iff_le_coe).mpr hs.2
    simp only [brownianReadout,min_eq_left hst]
  change StronglyMeasurable (fun ω : ℝ≥0 → ℝ => primitive k (t : ℝ) ω)
  rw [he]
  exact hw.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))

theorem state_stronglyAdapted (k σ x₀ : ℝ) :
    StronglyAdapted naturalFiltration (fun t : ℝ≥0 => state k σ x₀ t) := by
  intro t
  have hb : StronglyMeasurable[naturalFiltration t] (fun ω => brownianReadout t ω) := by
    change StronglyMeasurable[naturalFiltration t] (fun ω => process (Real.toNNReal (t : ℝ)) ω-process 0 ω)
    rw [Real.toNNReal_coe]
    change StronglyMeasurable[naturalFiltration t] (process t-process 0)
    exact (process_stronglyAdapted t).sub
      ((process_stronglyAdapted 0).mono (naturalFiltration.mono (bot_le : (0 : ℝ≥0)≤t)))
  exact (stronglyMeasurable_const.mul (stronglyMeasurable_const.sub
    (stronglyMeasurable_const.mul (primitive_stronglyAdapted k t)))).add (stronglyMeasurable_const.mul hb)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalVolterraSource
