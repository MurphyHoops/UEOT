import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralContinuousVersion
import Mathlib.MeasureTheory.Integral.Prod

/-!
Original commitment: an actual integral compensator must use the SAME input's actual time-energy, not a certificate field.
Existing result: full genuine predictable L2, same source continuous integral, and native predictable inclusion/Fubini.
Premise reduced: construct actual truncated time integral of the predictable representative squared and derive Fs permissions.
Model/witness: SAME fixed inputLaw T = timeLaw T times sourceLaw, original naturalFiltration, all f and T including zero.
Consumer: L1 square/energy approximation and actual integral compensator; no unconditional L2 bracket or Ito is claimed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTimeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeTruncation
open BrownianIntegralContinuousVersion BrownianIntegralLiteralIntervals BrownianCommonRefinement
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual native predictable representative of the SAME original L2 class. -/
def representative (T : ℝ≥0) (f : fullPredictableL2 T) : ℝ × (ℝ≥0 → ℝ) → ℝ :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp f.property).mk (f : Lp ℝ 2 (inputLaw T))

theorem representative_predictable (T : ℝ≥0) (f : fullPredictableL2 T) :
    StronglyMeasurable[predictableSigma] (representative T f) :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp f.property).stronglyMeasurable_mk

theorem representative_ae (T : ℝ≥0) (f : fullPredictableL2 T) :
    (f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T] representative T f :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp f.property).ae_eq_mk

theorem representative_memLp_two (T : ℝ≥0) (f : fullPredictableL2 T) :
    MemLp (representative T f) 2 (inputLaw T) :=
  (memLp_congr_ae (representative_ae T f)).mp (Lp.memLp (f : Lp ℝ 2 (inputLaw T)))

private theorem measurable_real_embedding :
    @Measurable (ℝ≥0 × (ℝ≥0 → ℝ)) (ℝ × (ℝ≥0 → ℝ))
      naturalFiltration.predictable predictableSigma (fun p => ((p.1 : ℝ),p.2)) := by
  apply measurable_iff_comap_le.mpr
  change MeasurableSpace.comap (fun p : ℝ≥0 × (ℝ≥0 → ℝ) => ((p.1 : ℝ),p.2))
    (MeasurableSpace.comap timeReadout naturalFiltration.predictable) ≤ _
  rw [MeasurableSpace.comap_comp]
  have he : timeReadout ∘ (fun p : ℝ≥0 × (ℝ≥0 → ℝ) => ((p.1 : ℝ),p.2)) = id := by
    ext p <;> simp [timeReadout]
  rw [he,MeasurableSpace.comap_id]

theorem representative_native_predictable (T : ℝ≥0) (f : fullPredictableL2 T) :
    IsStronglyPredictable naturalFiltration (fun u ω => representative T f ((u : ℝ),ω)) :=
  (representative_predictable T f).comp_measurable measurable_real_embedding

/-- Literal actual time-energy integrand on the ORIGINAL product measure. -/
def energyIntegrand (T s : ℝ≥0) (f : fullPredictableL2 T) : ℝ × (ℝ≥0 → ℝ) → ℝ :=
  (timeSet T s).indicator (fun p => representative T f p ^ 2)

theorem energyIntegrand_integrable (T s : ℝ≥0) (f : fullPredictableL2 T) :
    Integrable (energyIntegrand T s f) (inputLaw T) :=
  ((representative_memLp_two T f).integrable_sq).indicator (timeSet_measurable T s)

/-- The genuine predictable inclusion gives original Fs measurability for
the actual cutoff integrand. Clipping is only a proof device outside its support. -/
theorem energyIntegrand_stronglyMeasurable_past (T s : ℝ≥0) (f : fullPredictableL2 T) :
    StronglyMeasurable[MeasurableSpace.prod inferInstance (naturalFiltration s)] (energyIntegrand T s f) := by
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  let clip (t : ℝ) : Iic s := ⟨min (Real.toNNReal t) (min s T),by
    exact (min_le_right (Real.toNNReal t) (min s T)).trans (min_le_left s T)⟩
  have hc : Measurable clip :=
    (measurable_id.real_toNNReal.min measurable_const).subtype_mk
  have hm : StronglyMeasurable (fun p : ℝ × (ℝ≥0 → ℝ) =>
      representative T f (((clip p.1 : ℝ≥0) : ℝ),p.2)) :=
    ((representative_native_predictable T f).isStronglyProgressive s).comp_measurable
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have ht : MeasurableSet (timeSet T s) := measurableSet_Ioc.prod MeasurableSet.univ
  have he : energyIntegrand T s f = (timeSet T s).indicator
      (fun p : ℝ × (ℝ≥0 → ℝ) => representative T f (((clip p.1 : ℝ≥0) : ℝ),p.2)^2) := by
    ext p
    by_cases hp : p ∈ timeSet T s
    · rw [energyIntegrand,Set.indicator_of_mem hp,Set.indicator_of_mem hp]
      have hn : Real.toNNReal p.1 ≤ min s T := (Real.toNNReal_le_iff_le_coe).mpr hp.1.2
      have heq : ((clip p.1 : ℝ≥0) : ℝ) = p.1 := by
        change ((min (Real.toNNReal p.1) (min s T) : ℝ≥0) : ℝ) = p.1
        rw [min_eq_left hn,Real.coe_toNNReal _ hp.1.1.le]
      rw [heq]
    · simp only [energyIntegrand,Set.indicator_of_notMem hp]
  rw [he]
  exact (hm.pow 2).indicator ht

/-- ACTUAL pathwise time integral, over the SAME original timeLaw T and
with the SAME cutoff used by the actual stochastic integral. -/
def timeEnergy (T : ℝ≥0) (f : fullPredictableL2 T) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∫ t, energyIntegrand T s f (t,ω) ∂timeLaw T

theorem timeEnergy_stronglyAdapted (T : ℝ≥0) (f : fullPredictableL2 T) :
    StronglyAdapted naturalFiltration (timeEnergy T f) := by
  intro s
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  exact (energyIntegrand_stronglyMeasurable_past T s f).integral_prod_left'

theorem timeEnergy_integrable (T s : ℝ≥0) (f : fullPredictableL2 T) :
    Integrable (timeEnergy T f s) sourceLaw :=
  (energyIntegrand_integrable T s f).integral_prod_right

theorem timeEnergy_nonneg (T s : ℝ≥0) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) :
    0 ≤ timeEnergy T f s ω := by
  apply integral_nonneg
  intro t
  exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

/-- Native Fubini binds the actual time integral to the ORIGINAL same-input
product energy. It is not supplied as a compensator or desired-output field. -/
theorem timeEnergy_mean (T s : ℝ≥0) (f : fullPredictableL2 T) :
    (∫ ω, timeEnergy T f s ω ∂sourceLaw) =
      ∫ p in timeSet T s, (f : Lp ℝ 2 (inputLaw T)) p ^ 2 ∂inputLaw T := by
  unfold timeEnergy
  rw [← integral_prod_symm _ (energyIntegrand_integrable T s f)]
  have he : energyIntegrand T s f =ᵐ[inputLaw T]
      (timeSet T s).indicator (fun p => (f : Lp ℝ 2 (inputLaw T)) p ^ 2) := by
    filter_upwards [representative_ae T f] with p hp
    by_cases hs : p ∈ timeSet T s <;> simp [energyIntegrand,hs,hp]
  change (∫ p, energyIntegrand T s f p ∂inputLaw T) = _
  rw [integral_congr_ae he,integral_indicator (timeSet_measurable T s)]

theorem timeEnergy_zero (T : ℝ≥0) (f : fullPredictableL2 T) : timeEnergy T f 0 = 0 := by
  ext ω
  simp [timeEnergy,energyIntegrand,timeSet]

/-- SAME actual continuous integral has its actual time-energy in expectation;
this is derived here at the natural L1 scale, not an L2 bracket assertion. -/
theorem continuousIntegralProcess_secondMoment_eq_timeEnergy (T s : ℝ≥0) (f : fullPredictableL2 T) :
    (∫ ω, continuousIntegralProcess T f s ω ^ 2 ∂sourceLaw) =
      ∫ ω, timeEnergy T f s ω ∂sourceLaw := by
  rw [continuousIntegralProcess_energy,timeEnergy_mean]

private theorem integral_section_ae {g h : ℝ × (ℝ≥0 → ℝ) → ℝ}
    (he : g =ᵐ[inputLaw T] h) :
    (fun ω => ∫ t, g (t,ω) ∂timeLaw T) =ᵐ[sourceLaw] (fun ω => ∫ t, h (t,ω) ∂timeLaw T) := by
  have hs := (Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw T)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact integral_congr_ae hω

private theorem timeLaw_interval_mass (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) :
    (timeLaw T).real (Ioc (a : ℝ) (b : ℝ)) = (b : ℝ)-(a : ℝ) := by
  have hsub : Ioc (a : ℝ) (b : ℝ) ⊆ Icc 0 (T : ℝ) := by
    intro t ht
    exact ⟨a.coe_nonneg.trans ht.1.le,ht.2.trans (by exact_mod_cast hbT)⟩
  rw [measureReal_def,timeLaw,Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr hsub,
    Real.volume_Ioc,ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (by exact_mod_cast hab)

/-- Literal interval energy is the actual original coefficient squared times
actual elapsed clock, derived by SAME-class identities and native Fubini. -/
theorem timeEnergy_interval_horizon (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) :
    timeEnergy T (intervalInput T a b hab hbT H hHpast hH) T =ᵐ[sourceLaw]
      fun ω => ((b : ℝ)-(a : ℝ))*H ω^2 := by
  let f := intervalInput T a b hab hbT H hHpast hH
  have he : energyIntegrand T T f =ᵐ[inputLaw T] (fun p => intervalIntegrand H a b p ^ 2) := by
    filter_upwards [representative_ae T f,intervalInput_coe T a b hab hbT H hHpast hH,time_support_ae T]
      with p hr hi ht
    have hp : p ∈ timeSet T T := by simpa only [timeSet,min_self,mem_prod,mem_univ,and_true] using ht
    rw [energyIntegrand,Set.indicator_of_mem hp,← hr,hi]
  apply (integral_section_ae he).trans
  apply Eventually.of_forall
  intro ω
  have hi : (fun t => intervalIntegrand H a b (t,ω)^2) =
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => H ω^2) := by
    ext t
    by_cases ht : t ∈ Ioc (a : ℝ) (b : ℝ) <;> simp [intervalIntegrand,ht]
  change (∫ t, intervalIntegrand H a b (t,ω)^2 ∂timeLaw T) = ((b : ℝ)-(a : ℝ))*H ω^2
  rw [hi,integral_indicator measurableSet_Ioc,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change (timeLaw T).real (Ioc (a : ℝ) (b : ℝ))*H ω^2 = _
  rw [timeLaw_interval_mass T a b hab hbT]

/-- The actual time cutoff and the actual original input cutoff agree on
path energy. This is a derived source identity, not a version-selection field. -/
theorem timeEnergy_truncate (T s : ℝ≥0) (f : fullPredictableL2 T) :
    timeEnergy T (truncate T s f) T =ᵐ[sourceLaw] timeEnergy T f s := by
  apply integral_section_ae
  filter_upwards [representative_ae T (truncate T s f),representative_ae T f,
    truncate_coe T s f,time_support_ae T] with p hg hf ht hsupp
  have hp : p ∈ timeSet T T := by simpa only [timeSet,min_self,mem_prod,mem_univ,and_true] using hsupp
  rw [energyIntegrand,energyIntegrand,Set.indicator_of_mem hp,← hg]
  rw [ht]
  by_cases hs : p ∈ timeSet T s <;> simp [hs,hf]

/-- Actual interval time-energy at EVERY observation time, including before
its original start: the original H is retained and only its elapsed prefix is used. -/
theorem timeEnergy_interval (T a b s : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) :
    timeEnergy T (intervalInput T a b hab hbT H hHpast hH) s =ᵐ[sourceLaw]
      fun ω => (((clamp a b s : ℝ≥0) : ℝ)-(a : ℝ))*H ω^2 := by
  have he := (timeEnergy_truncate T s (intervalInput T a b hab hbT H hHpast hH)).symm
  rw [truncate_intervalInput] at he
  exact he.trans (timeEnergy_interval_horizon T a (clamp a b s)
    (clamp_bounds a b s hab).1 ((clamp_bounds a b s hab).2.trans hbT) H hHpast hH)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTimeEnergy
