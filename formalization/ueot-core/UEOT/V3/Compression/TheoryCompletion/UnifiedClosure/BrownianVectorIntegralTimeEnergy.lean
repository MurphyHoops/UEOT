import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralGridL1

/-!
Original commitment: same joint-vector QV/state calculus requires actual pathwise dt energy, not merely expected energy or an assumed bracket.
Existing result: actual full predictable Euclidean input/native cutoff integral and its genuine continuous joint-past version.
Premise reduced: derive actual Euclidean norm-square time integral, originalFs adaptation and original product-law Fubini/second-moment binding.
Model: unchanged productLaw d/timeLaw T/jointNaturalFiltration/fullPredictableL2 dT, finite d including0 and T0, no future coefficient permission.
Consumer: finite-row QV limits and full-input natural-L1 energy stability; conditional compensator/QV/state Ito are not assumed or completed here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralTimeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianVectorIntegralConditionalSource BrownianVectorIntegralContinuousVersion
open BrownianTimeIntegrand (timeLaw)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Actual native predictable representative of the SAME original L2 class. -/
def representative (T : ℝ≥0) (f : fullPredictableL2 d T) : ℝ × (Sample d) → EuclideanSpace ℝ (Fin d) :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp f.property).mk (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))

theorem representative_predictable (T : ℝ≥0) (f : fullPredictableL2 d T) :
    StronglyMeasurable[(predictableSigma d)] (representative d T f) :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp f.property).stronglyMeasurable_mk

theorem representative_ae (T : ℝ≥0) (f : fullPredictableL2 d T) :
    (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T] representative d T f :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp f.property).ae_eq_mk

theorem representative_memLp_two (T : ℝ≥0) (f : fullPredictableL2 d T) :
    MemLp (representative d T f) 2 (inputLaw d T) :=
  (memLp_congr_ae (representative_ae d T f)).mp (Lp.memLp (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)))

private theorem measurable_real_embedding :
    @Measurable (ℝ≥0 × (Sample d)) (ℝ × (Sample d))
      (jointNaturalFiltration d).predictable (predictableSigma d) (fun p => ((p.1 : ℝ),p.2)) := by
  apply measurable_iff_comap_le.mpr
  change MeasurableSpace.comap (fun p : ℝ≥0 × (Sample d) => ((p.1 : ℝ),p.2))
    (MeasurableSpace.comap (timeReadout d) (jointNaturalFiltration d).predictable) ≤ _
  rw [MeasurableSpace.comap_comp]
  have he : timeReadout d ∘ (fun p : ℝ≥0 × (Sample d) => ((p.1 : ℝ),p.2)) = id := by
    ext p <;> simp [timeReadout]
  rw [he,MeasurableSpace.comap_id]

theorem representative_native_predictable (T : ℝ≥0) (f : fullPredictableL2 d T) :
    IsStronglyPredictable (jointNaturalFiltration d) (fun u ω => representative d T f ((u : ℝ),ω)) :=
  (representative_predictable d T f).comp_measurable (measurable_real_embedding d)

/-- Literal actual time-energy integrand on the ORIGINAL product measure. -/
def energyIntegrand (T s : ℝ≥0) (f : fullPredictableL2 d T) : ℝ × (Sample d) → ℝ :=
  (timeSet d T s).indicator (fun p => ‖representative d T f p‖ ^ 2)

theorem energyIntegrand_integrable (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    Integrable (energyIntegrand d T s f) (inputLaw d T) :=
  ((representative_memLp_two d T f).norm.integrable_sq).indicator (timeSet_measurable d T s)

/-- The genuine predictable inclusion gives original Fs measurability for
the actual cutoff integrand. Clipping is only a proof device outside its support. -/
theorem energyIntegrand_stronglyMeasurable_past (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    StronglyMeasurable[MeasurableSpace.prod inferInstance ((jointNaturalFiltration d) s)] (energyIntegrand d T s f) := by
  let : MeasurableSpace (Sample d) := (jointNaturalFiltration d) s
  let clip (t : ℝ) : Iic s := ⟨min (Real.toNNReal t) (min s T),by
    exact (min_le_right (Real.toNNReal t) (min s T)).trans (min_le_left s T)⟩
  have hc : Measurable clip :=
    (measurable_id.real_toNNReal.min measurable_const).subtype_mk
  have hm : StronglyMeasurable (fun p : ℝ × (Sample d) =>
      representative d T f (((clip p.1 : ℝ≥0) : ℝ),p.2)) :=
    ((representative_native_predictable d T f).isStronglyProgressive s).comp_measurable
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have ht : MeasurableSet (timeSet d T s) := measurableSet_Ioc.prod MeasurableSet.univ
  have he : energyIntegrand d T s f = (timeSet d T s).indicator
      (fun p : ℝ × (Sample d) => ‖representative d T f (((clip p.1 : ℝ≥0) : ℝ),p.2)‖^2) := by
    ext p
    by_cases hp : p ∈ timeSet d T s
    · rw [energyIntegrand,Set.indicator_of_mem hp,Set.indicator_of_mem hp]
      have hn : Real.toNNReal p.1 ≤ min s T := (Real.toNNReal_le_iff_le_coe).mpr hp.1.2
      have heq : ((clip p.1 : ℝ≥0) : ℝ) = p.1 := by
        change ((min (Real.toNNReal p.1) (min s T) : ℝ≥0) : ℝ) = p.1
        rw [min_eq_left hn,Real.coe_toNNReal _ hp.1.1.le]
      rw [heq]
    · simp only [energyIntegrand,Set.indicator_of_notMem hp]
  rw [he]
  exact (hm.norm.pow 2).indicator ht

/-- ACTUAL pathwise time integral, over the SAME original timeLaw T and
with the SAME cutoff used by the actual stochastic integral. -/
def timeEnergy (T : ℝ≥0) (f : fullPredictableL2 d T) (s : ℝ≥0) (ω : Sample d) : ℝ :=
  ∫ t, energyIntegrand d T s f (t,ω) ∂timeLaw T

theorem timeEnergy_stronglyAdapted (T : ℝ≥0) (f : fullPredictableL2 d T) :
    StronglyAdapted (jointNaturalFiltration d) (timeEnergy d T f) := by
  intro s
  let : MeasurableSpace (Sample d) := (jointNaturalFiltration d) s
  exact (energyIntegrand_stronglyMeasurable_past d T s f).integral_prod_left'

theorem timeEnergy_integrable (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    Integrable (timeEnergy d T f s) (productLaw d) :=
  (energyIntegrand_integrable d T s f).integral_prod_right

theorem timeEnergy_nonneg (T s : ℝ≥0) (f : fullPredictableL2 d T) (ω : Sample d) :
    0 ≤ timeEnergy d T f s ω := by
  apply integral_nonneg
  intro t
  exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

/-- Native Fubini binds the actual time integral to the ORIGINAL same-input
product energy. It is not supplied as a compensator or desired-output field. -/
theorem timeEnergy_mean (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    (∫ ω, timeEnergy d T f s ω ∂(productLaw d)) =
      ∫ p in timeSet d T s, ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖ ^ 2 ∂inputLaw d T := by
  unfold timeEnergy
  rw [← integral_prod_symm _ (energyIntegrand_integrable d T s f)]
  have he : energyIntegrand d T s f =ᵐ[inputLaw d T]
      (timeSet d T s).indicator (fun p => ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖ ^ 2) := by
    filter_upwards [representative_ae d T f] with p hp
    by_cases hs : p ∈ timeSet d T s <;> simp [energyIntegrand,hs,hp]
  change (∫ p, energyIntegrand d T s f p ∂inputLaw d T) = _
  rw [integral_congr_ae he,integral_indicator (timeSet_measurable d T s)]

theorem timeEnergy_zero (T : ℝ≥0) (f : fullPredictableL2 d T) : timeEnergy d T f 0 = 0 := by
  ext ω
  simp [timeEnergy,energyIntegrand,timeSet]

/-- SAME actual continuous integral has its actual time-energy in expectation;
this is derived here at the natural L1 scale, not an L2 bracket assertion. -/
theorem continuousIntegralProcess_secondMoment_eq_timeEnergy (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    (∫ ω, continuousIntegralProcess d T f s ω ^ 2 ∂(productLaw d)) =
      ∫ ω, timeEnergy d T f s ω ∂(productLaw d) := by
  rw [continuousIntegralProcess_energy,timeEnergy_mean d]

private theorem integral_section_ae {g h : ℝ × (Sample d) → ℝ}
    (he : g =ᵐ[inputLaw d T] h) :
    (fun ω => ∫ t, g (t,ω) ∂timeLaw T) =ᵐ[(productLaw d)] (fun ω => ∫ t, h (t,ω) ∂timeLaw T) := by
  have hs := (Measure.measurePreserving_swap (μ := (productLaw d)) (ν := timeLaw T)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact integral_congr_ae hω

/-- Actual energy is the SAME native time interval integral, for each source
sample. This is a definition-derived identity, not a chosen compensator. -/
theorem timeEnergy_eq_setIntegral (T s : ℝ≥0) (f : fullPredictableL2 d T) (ω : Sample d) :
    timeEnergy d T f s ω = ∫ t in Ioc (0 : ℝ) (min s T : ℝ≥0), ‖representative d T f (t,ω)‖^2 ∂timeLaw T := by
  unfold timeEnergy
  have he : (fun t => energyIntegrand d T s f (t,ω)) =
      (Ioc (0 : ℝ) (min s T : ℝ≥0)).indicator (fun t => ‖representative d T f (t,ω)‖^2) := by
    ext t
    have hm : (t,ω)∈timeSet d T s ↔ t∈Ioc (0 : ℝ) (min s T : ℝ≥0) := by
      simp only [timeSet,mem_prod,mem_univ,and_true]
    by_cases ht : t ∈ Ioc (0 : ℝ) (min s T : ℝ≥0)
    · rw [energyIntegrand,Set.indicator_of_mem (hm.mpr ht),Set.indicator_of_mem ht]
    · rw [energyIntegrand,Set.indicator_of_notMem (fun h=>ht (hm.mp h)),Set.indicator_of_notMem ht]
  rw [he,integral_indicator measurableSet_Ioc]

/-- ONE product-Fubini full-section event suffices for ALL time comparisons;
there is no uncountable intersection of time-indexed exceptional events. -/
theorem timeEnergy_monotone_ae (T : ℝ≥0) (f : fullPredictableL2 d T) :
    ∀ᵐ ω ∂productLaw d, Monotone (fun s => timeEnergy d T f s ω) := by
  filter_upwards [(representative_memLp_two d T f).norm.integrable_sq.prod_left_ae] with ω hω
  intro s t hst
  simp_rw [timeEnergy_eq_setIntegral]
  apply setIntegral_mono_set hω.integrableOn (Eventually.of_forall (fun _ => sq_nonneg _))
  exact Eventually.of_forall (fun x hx => ⟨hx.1,hx.2.trans (by exact_mod_cast min_le_min_right T hst)⟩)

/-- Native continuous primitive of the SAME norm-square time section yields
all-time continuous energy on ONE original product-source full event. -/
theorem timeEnergy_continuous_ae (T : ℝ≥0) (f : fullPredictableL2 d T) :
    ∀ᵐ ω ∂productLaw d, Continuous (fun s => timeEnergy d T f s ω) := by
  filter_upwards [(representative_memLp_two d T f).norm.integrable_sq.prod_left_ae] with ω hω
  let : NullSingletonClass (timeLaw T) := by
    unfold timeLaw
    infer_instance
  have hc := hω.continuous_primitive (0 : ℝ)
  have ht : Continuous (fun s : ℝ≥0 => ((min s T : ℝ≥0) : ℝ)) :=
    continuous_subtype_val.comp (continuous_id.min continuous_const)
  convert hc.comp ht using 1
  ext s
  rw [Function.comp_apply,timeEnergy_eq_setIntegral,intervalIntegral.integral_of_le (min s T).coe_nonneg]

/-- The original stochastic cutoff has precisely its same actual time-energy. -/
theorem timeEnergy_truncate (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    timeEnergy d T (truncate d T s f) T =ᵐ[productLaw d] timeEnergy d T f s := by
  apply integral_section_ae d
  filter_upwards [representative_ae d T (truncate d T s f),representative_ae d T f,
    truncate_coe d T s f,time_support_ae d T] with p hg hf ht hsupp
  have hp : p ∈ timeSet d T T := by simpa only [timeSet,min_self,mem_prod,mem_univ,and_true] using hsupp
  rw [energyIntegrand,energyIntegrand,Set.indicator_of_mem hp,← hg,ht]
  by_cases hs : p ∈ timeSet d T s <;> simp [hs,hf]

private theorem timeLaw_interval_mass (T a b : ℝ≥0) (hab : a≤b) (hbT : b≤T) :
    (timeLaw T).real (Ioc (a : ℝ) (b : ℝ))=(b : ℝ)-(a : ℝ) := by
  have hsub : Ioc (a : ℝ) (b : ℝ) ⊆ Icc 0 (T : ℝ) := by
    intro t ht
    exact ⟨a.coe_nonneg.trans ht.1.le,ht.2.trans (by exact_mod_cast hbT)⟩
  rw [measureReal_def,timeLaw,Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr hsub,
    Real.volume_Ioc,ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (by exact_mod_cast hab)

/-- SAME literal vector block's actual pathwise norm-square energy. Coefficients
retain entire joint-START permission and original product-source bound. -/
theorem timeEnergy_interval_horizon (T a b : ℝ≥0) (hab : a≤b) (hbT : b≤T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    timeEnergy d T (BrownianVectorIntegralConditionalSource.intervalInput d T a b hab hbT H hHpast hH) T
      =ᵐ[productLaw d] fun ω => ((b : ℝ)-(a : ℝ))*‖BrownianVectorOneStepIntegral.coefficient d H ω‖^2 := by
  let f := BrownianVectorIntegralConditionalSource.intervalInput d T a b hab hbT H hHpast hH
  have he : energyIntegrand d T T f =ᵐ[inputLaw d T]
      (fun p => ‖BrownianVectorTimeInput.intervalInput d H a b p‖^2) := by
    filter_upwards [representative_ae d T f,intervalInput_coe d T a b hab hbT H hHpast hH,time_support_ae d T]
      with p hr hi ht
    have hp : p ∈ timeSet d T T := by simpa only [timeSet,min_self,mem_prod,mem_univ,and_true] using ht
    rw [energyIntegrand,Set.indicator_of_mem hp,← hr,hi]
  apply (integral_section_ae d he).trans
  apply Eventually.of_forall
  intro ω
  have hi : (fun t => ‖BrownianVectorTimeInput.intervalInput d H a b (t,ω)‖^2)=
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => ‖BrownianVectorOneStepIntegral.coefficient d H ω‖^2) := by
    ext t
    by_cases ht : t ∈ Ioc (a : ℝ) (b : ℝ) <;> simp [BrownianVectorTimeInput.intervalInput,ht]
  change (∫ t, ‖BrownianVectorTimeInput.intervalInput d H a b (t,ω)‖^2 ∂timeLaw T)=_
  rw [hi,integral_indicator measurableSet_Ioc,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change (timeLaw T).real (Ioc (a : ℝ) (b : ℝ))*_= _
  rw [timeLaw_interval_mass T a b hab hbT]

/-- Before START the elapsed block is genuinely empty, not a future coefficient
pulled from an earlier conditional expectation. -/
theorem timeEnergy_interval (T a b u : ℝ≥0) (hab : a≤b) (hbT : b≤T)
    (H : Fin d → Sample d → ℝ) (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    timeEnergy d T (BrownianVectorIntegralConditionalSource.intervalInput d T a b hab hbT H hHpast hH) u
      =ᵐ[productLaw d] fun ω =>
        (((BrownianCommonRefinement.clamp a b u : ℝ≥0) : ℝ)-(a : ℝ))*
          ‖BrownianVectorOneStepIntegral.coefficient d H ω‖^2 := by
  have he := (timeEnergy_truncate d T u
    (BrownianVectorIntegralConditionalSource.intervalInput d T a b hab hbT H hHpast hH)).symm
  rw [truncate_intervalInput] at he
  exact he.trans (timeEnergy_interval_horizon d T a (BrownianCommonRefinement.clamp a b u)
    (BrownianCommonRefinement.clamp_bounds a b u hab).1
    ((BrownianCommonRefinement.clamp_bounds a b u hab).2.trans hbT) H hHpast hH)

theorem timeEnergy_zero_horizon (u : ℝ≥0) (f : fullPredictableL2 d 0) : timeEnergy d 0 f u=0 := by
  ext ω
  simp [timeEnergy,energyIntegrand,timeSet]

theorem timeEnergy_zero_dimension (T u : ℝ≥0) (f : fullPredictableL2 0 T) : timeEnergy 0 T f u=0 := by
  have hr : representative 0 T f=0 := funext (fun p => Subsingleton.elim _ _)
  ext ω
  simp [timeEnergy,energyIntegrand,hr]


end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralTimeEnergy
