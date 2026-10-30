import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedExponentialLimitSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianConstantGirsanovSource

/-!
Original commitment: bounded full-input change of measure must retain an actual permitted control, not raw Lp coercion permissions.
Existing result: native predictable SAME-f representative clipped to SAME K, actual terminal exponential normalized from actual finite tables.
Premise reduced: construct real-time masked progressive control and its actual dt drift/energy on the ORIGINAL filtration.
Model/witness: chosen native predictable representative, literal support(0,T], original Fs clock, same dt×P class, T=0 and all nonnegative reads.
Consumer/boundary: actual full-Q shifted path/whole original-past laws; no limit natural-filtration inversion or general Q integrator is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedControlSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeEnergy BrownianIntegralTimeTruncation
open BrownianBoundedPredictableApproximation
open UEOT.V3.GirsanovPathKL
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem clip_continuous (K : ℝ) : Continuous (BrownianContinuousAdaptedInputs.clip K) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Actual real-time control. The negative/zero/outside-horizon values are
literally zero, with no global future-good-event branch. -/
def control (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  (Ioc (0 : ℝ) (T : ℝ)).indicator (fun u => boundedRepresentative T f K (u,ω)) t

theorem control_bound (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K) (t : ℝ) (ω : ℝ≥0 → ℝ) :
    ‖control T f K t ω‖≤K := by
  by_cases ht : t∈Ioc (0 : ℝ) (T : ℝ)
  · rw [control,Set.indicator_of_mem ht]
    exact boundedRepresentative_bound T f K hK _
  · rw [control,Set.indicator_of_notMem ht,norm_zero]
    exact hK

theorem control_joint (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) :
    Measurable (Function.uncurry (control T f K)) := by
  have he : Function.uncurry (control T f K)=
      (Ioc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set (ℝ≥0 → ℝ))).indicator (boundedRepresentative T f K) := by
    funext p
    by_cases ht : p.1∈Ioc (0 : ℝ) (T : ℝ) <;> simp [Function.uncurry,control,ht]
  rw [he]
  exact ((boundedRepresentative_predictable T f K).mono predictableSigma_le).measurable.indicator
    (measurableSet_Ioc.prod MeasurableSet.univ)

private theorem native_predictable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) :
    IsStronglyPredictable naturalFiltration (fun u ω => boundedRepresentative T f K ((u : ℝ),ω)) :=
  (clip_continuous K).comp_stronglyMeasurable (representative_native_predictable T f)

/-- The original real-clock filtration sees only permitted current past.
The Ioc mask is proved explicitly, rather than upgrading an AE Lp coercion. -/
theorem control_progressive (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) :
    IsProgressive BrownianConstantGirsanovSource.controlFiltration (control T f K) := by
  intro s
  let a := Real.toNNReal s
  let c : ℝ → Iic a := fun u => ⟨min (Real.toNNReal u) a,by change min (Real.toNNReal u) a ≤ a; exact min_le_right _ _⟩
  have hc : Measurable c := (measurable_id.real_toNNReal.min measurable_const).subtype_mk
  have hm : @Measurable (Iic s × (ℝ≥0 → ℝ)) ℝ
      (Subtype.instMeasurableSpace.prod (BrownianConstantGirsanovSource.controlFiltration s)) inferInstance
      (fun p => boundedRepresentative T f K (((c (p.1 : ℝ) : ℝ≥0) : ℝ),p.2)) :=
    ((native_predictable T f K).isStronglyProgressive a).measurable.comp
      ((hc.comp (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd)
  have ht : @MeasurableSet (Iic s × (ℝ≥0 → ℝ))
      (Subtype.instMeasurableSpace.prod (BrownianConstantGirsanovSource.controlFiltration s))
      {p | (p.1 : ℝ)∈Ioc (0 : ℝ) (T : ℝ)} :=
    (measurable_subtype_coe.comp measurable_fst) measurableSet_Ioc
  have he : (fun p : Iic s × (ℝ≥0 → ℝ) => control T f K p.1 p.2)=
      {p : Iic s × (ℝ≥0 → ℝ) | (p.1 : ℝ)∈Ioc (0 : ℝ) (T : ℝ)}.indicator
        (fun p => boundedRepresentative T f K (((c (p.1 : ℝ) : ℝ≥0) : ℝ),p.2)) := by
    funext p
    by_cases hp : (p.1 : ℝ)∈Ioc (0 : ℝ) (T : ℝ)
    · have hp' : p∈{q : Iic s × (ℝ≥0 → ℝ) | (q.1 : ℝ)∈Ioc (0 : ℝ) (T : ℝ)} := hp
      rw [control,Set.indicator_of_mem hp,Set.indicator_of_mem hp']
      have hpa : Real.toNNReal (p.1 : ℝ)≤a := Real.toNNReal_mono p.1.property
      have hx : ((c (p.1 : ℝ) : ℝ≥0) : ℝ)=(p.1 : ℝ) := by
        change ((min (Real.toNNReal (p.1 : ℝ)) a : ℝ≥0) : ℝ)=(p.1 : ℝ)
        rw [min_eq_left hpa,Real.coe_toNNReal _ hp.1.le]
      rw [hx]
    · have hp' : p∉{q : Iic s × (ℝ≥0 → ℝ) | (q.1 : ℝ)∈Ioc (0 : ℝ) (T : ℝ)} := hp
      rw [control,Set.indicator_of_notMem hp,Set.indicator_of_notMem hp']
  rw [he]
  exact hm.indicator ht

/-- Actual control is the SAME original f in its original product class. -/
theorem control_input_ae (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    (fun p : ℝ × (ℝ≥0 → ℝ) => control T f K p.1 p.2) =ᵐ[inputLaw T] (f : Lp ℝ 2 (inputLaw T)) := by
  filter_upwards [time_support_ae T,boundedRepresentative_ae T f K hbound] with p ht hp
  rw [control,Set.indicator_of_mem ht]
  exact hp.symm

private theorem representative_intervalIntegrable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (ω : ℝ≥0 → ℝ) (a b : ℝ) : IntervalIntegrable (fun t => boundedRepresentative T f K (t,ω)) volume a b := by
  have hm : Measurable (fun t => boundedRepresentative T f K (t,ω)) :=
    ((boundedRepresentative_predictable T f K).mono predictableSigma_le).measurable.comp
      (measurable_id.prodMk measurable_const)
  let _ : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min a b) (max a b)))
    infer_instance
  have htop : MemLp (fun t => boundedRepresentative T f K (t,ω)) ∞ (volume.restrict (uIoc a b)) :=
    MemLp.of_bound hm.aestronglyMeasurable K (Eventually.of_forall (fun t => boundedRepresentative_bound T f K hK _))
  rw [intervalIntegrable_iff]
  exact htop.integrable (by norm_num)

def driftIntegrand (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s : ℝ≥0) : ℝ × (ℝ≥0 → ℝ) → ℝ :=
  (timeSet T s).indicator (boundedRepresentative T f K)

/-- Actual drift uses the SAME timeLaw and predictable representative,
with the SAME cutoff clock as the native stochastic integral. -/
def drift (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∫ t, driftIntegrand T f K s (t,ω) ∂timeLaw T

theorem driftIntegrand_past (T s : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) :
    StronglyMeasurable[MeasurableSpace.prod inferInstance (naturalFiltration s)] (driftIntegrand T f K s) := by
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  let c (t : ℝ) : Iic s := ⟨min (Real.toNNReal t) (min s T),by
    exact (min_le_right (Real.toNNReal t) (min s T)).trans (min_le_left s T)⟩
  have hc : Measurable c := (measurable_id.real_toNNReal.min measurable_const).subtype_mk
  have hm : StronglyMeasurable (fun p : ℝ × (ℝ≥0 → ℝ) =>
      boundedRepresentative T f K (((c p.1 : ℝ≥0) : ℝ),p.2)) :=
    ((native_predictable T f K).isStronglyProgressive s).comp_measurable ((hc.comp measurable_fst).prodMk measurable_snd)
  have ht : MeasurableSet (timeSet T s) := measurableSet_Ioc.prod MeasurableSet.univ
  have he : driftIntegrand T f K s=(timeSet T s).indicator
      (fun p : ℝ × (ℝ≥0 → ℝ) => boundedRepresentative T f K (((c p.1 : ℝ≥0) : ℝ),p.2)) := by
    funext p
    by_cases hp : p∈timeSet T s
    · rw [driftIntegrand,Set.indicator_of_mem hp,Set.indicator_of_mem hp]
      have hn : Real.toNNReal p.1≤min s T := Real.toNNReal_le_iff_le_coe.mpr hp.1.2
      have hx : ((c p.1 : ℝ≥0) : ℝ)=p.1 := by
        change ((min (Real.toNNReal p.1) (min s T) : ℝ≥0) : ℝ)=p.1
        rw [min_eq_left hn,Real.coe_toNNReal _ hp.1.1.le]
      rw [hx]
    · simp only [driftIntegrand,Set.indicator_of_notMem hp]
  rw [he]
  exact hm.indicator ht

theorem drift_stronglyAdapted (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) :
    StronglyAdapted naturalFiltration (drift T f K) := by
  intro s
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  exact (driftIntegrand_past T s f K).integral_prod_left'

/-- Same literal Lebesgue primitive, with the correct clipped clock. -/
theorem drift_primitive (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    drift T f K s ω=∫ t in (0 : ℝ)..(min s T : ℝ≥0), boundedRepresentative T f K (t,ω) := by
  have he : (fun t => driftIntegrand T f K s (t,ω))=
      (Ioc (0 : ℝ) (min s T : ℝ≥0)).indicator (fun t => boundedRepresentative T f K (t,ω)) := by
    funext t
    change (timeSet T s).indicator (boundedRepresentative T f K) (t,ω)=_
    by_cases ht : t∈Ioc (0 : ℝ) (min s T : ℝ≥0)
    · have hp : (t,ω)∈timeSet T s := ⟨ht,Set.mem_univ _⟩
      rw [Set.indicator_of_mem hp,Set.indicator_of_mem ht]
    · have hp : (t,ω)∉timeSet T s := fun h => ht h.1
      rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem ht]
  have hs : Ioc (0 : ℝ) (min s T : ℝ≥0) ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro t ht
    exact ⟨ht.1.le,ht.2.trans (by exact_mod_cast min_le_right s T)⟩
  rw [drift,he,timeLaw,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hs,← intervalIntegral.integral_of_le (min s T).coe_nonneg]

theorem drift_continuous (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K) (ω : ℝ≥0 → ℝ) :
    Continuous (fun s => drift T f K s ω) := by
  simp_rw [drift_primitive]
  exact (intervalIntegral.continuous_primitive (representative_intervalIntegrable T f K hK ω) 0).comp
    (continuous_subtype_val.comp (continuous_id.min continuous_const))

theorem drift_zero (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) : drift T f K 0=0 := by
  funext ω
  rw [drift_primitive]
  simp

/-- The actual masked real control has a genuine finite dt energy on every
sample under the explicit K bound, including T=0. -/
theorem control_energy_intervalIntegrable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K) (ω : ℝ≥0 → ℝ) :
    IntervalIntegrable (fun t => ‖control T f K t ω‖^2) volume 0 (T : ℝ) := by
  have hm : Measurable (fun t => control T f K t ω) := (control_joint T f K).comp (measurable_id.prodMk measurable_const)
  let _ : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) (T : ℝ))) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min 0 (T : ℝ)) (max 0 (T : ℝ))))
    infer_instance
  have htop : MemLp (fun t => control T f K t ω) ∞ (volume.restrict (uIoc (0 : ℝ) (T : ℝ))) :=
    MemLp.of_bound hm.aestronglyMeasurable K (Eventually.of_forall (fun t => control_bound T f K hK t ω))
  rw [intervalIntegrable_iff]
  change Integrable (fun t => ‖control T f K t ω‖^2) (volume.restrict (uIoc (0 : ℝ) (T : ℝ)))
  simpa only [Real.norm_eq_abs,sq_abs] using
    (show MemLp (fun t => control T f K t ω) 2 (volume.restrict (uIoc (0 : ℝ) (T : ℝ))) from htop.mono_exponent le_top).integrable_sq

/-- Original P-KL clock-time energy is the ACTUAL SAME-f time energy,
proved by native product-AE and Fubini, not inserted as a field. -/
theorem control_energy_eq_actual (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    controlEnergy T (control T f K) =ᵐ[sourceLaw] timeEnergy T f T := by
  have he : (fun p : ℝ × (ℝ≥0 → ℝ) => control T f K p.1 p.2^2)=ᵐ[inputLaw T] energyIntegrand T T f := by
    filter_upwards [control_input_ae T f K hbound,representative_ae T f,time_support_ae T] with p hc hr ht
    have hp : p∈timeSet T T := by
      change p∈Ioc (0 : ℝ) (min T T : ℝ≥0) ×ˢ univ
      rw [min_self]
      exact ⟨ht,Set.mem_univ _⟩
    rw [energyIntegrand,Set.indicator_of_mem hp,hc,hr]
  have hsec : ∀ᵐ ω ∂sourceLaw, (fun t => control T f K t ω^2)=ᵐ[timeLaw T] fun t => energyIntegrand T T f (t,ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw T)).quasiMeasurePreserving.ae he)
  filter_upwards [hsec] with ω hω
  have hclock : controlEnergy T (control T f K) ω=∫ t, control T f K t ω^2 ∂timeLaw T := by
    simp only [controlEnergy,Real.norm_eq_abs,sq_abs]
    rw [intervalIntegral.integral_of_le T.coe_nonneg,timeLaw,integral_Icc_eq_integral_Ioc]
  exact hclock.trans (integral_congr_ae hω)

/-- Actual complete shifted readout; its Brownian/original-past law under
fullLaw is the next required source theorem, not a field of this definition. -/
def shiftedProcess (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  BrownianContinuousSource.process s ω-drift T f K s ω

theorem shiftedProcess_stronglyAdapted (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) :
    StronglyAdapted naturalFiltration (shiftedProcess T f K) :=
  fun s => (process_stronglyAdapted s).sub (drift_stronglyAdapted T f K s)

theorem shiftedProcess_continuous (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K) (ω : ℝ≥0 → ℝ) :
    Continuous (fun s => shiftedProcess T f K s ω) :=
  (BrownianContinuousSource.process_continuous ω).sub (drift_continuous T f K hK ω)

/-- Drift is literally frozen after the declared horizon, for every sample. -/
theorem drift_after (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s : ℝ≥0) (hs : T≤s) (ω : ℝ≥0 → ℝ) :
    drift T f K s ω=drift T f K T ω := by
  rw [drift_primitive,drift_primitive,min_eq_right hs,min_self]

theorem drift_horizon_zero (f : fullPredictableL2 0) (K : ℝ) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    drift 0 f K s ω=0 := by
  rw [drift_primitive]
  simp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedControlSource
