import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedControlSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepShiftedSource

/-!
Original commitment: the normalized limit density must consume the same actual dt drift as the finite actual Brownian paths.
Existing result: SAME bounded f gives real progressive control/drift and same-K finite tables with native input L2 convergence.
Premise reduced: bind actual time marginals to native L1, and derive actual finite drift/path convergence on the SAME source.
Model/witness: fixed inputLaw T and original Fs, actual clipped control representative, exact finite table clocks/coefficients; T=0 allowed.
Consumer/boundary: moving-density original-Fs joint Brownian transport; no general natural-filtration inverse equality is asserted.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedDriftLimitSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeEnergy BrownianIntegralTimeTruncation
open BrownianIntegralEnergyL1 BrownianBoundedPredictableApproximation BrownianBoundedControlSource
open BrownianCommonRefinement BrownianPastStepGaussianResidualSource BrownianFiniteStepShiftedSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Native finite-measure exponent inclusion, retaining the SAME functions. -/
private def toOne {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (g : Lp ℝ 2 μ) : Lp ℝ 1 μ :=
  ((Lp.memLp g).mono_exponent (by norm_num : (1 : ℝ≥0∞)≤2)).toLp g
private theorem toOne_coe {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (g : Lp ℝ 2 μ) :
    toOne μ g =ᵐ[μ] g := ((Lp.memLp g).mono_exponent (by norm_num : (1 : ℝ≥0∞)≤2)).coeFn_toLp

private theorem toOne_tendsto {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : ℕ → Lp ℝ 2 μ} {f : Lp ℝ 2 μ} (h : Tendsto g atTop (𝓝 f)) :
    Tendsto (fun n => toOne μ (g n)) atTop (𝓝 (toOne μ f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  have hh := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp h
  let C : ℝ≥0∞ := μ univ ^ (1/(1 : ℝ≥0∞).toReal-1/(2 : ℝ≥0∞).toReal)
  have hc : C≠∞ := by
    unfold C
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have hz := ENNReal.Tendsto.mul_const hh (Or.inr hc)
  simp only [zero_mul] at hz
  have hcomp (n : ℕ) : eLpNorm (⇑(toOne μ (g n))-⇑(toOne μ f)) 1 μ≤eLpNorm (⇑(g n)-⇑f) 2 μ*C := by
    have he : (⇑(toOne μ (g n))-⇑(toOne μ f))=ᵐ[μ] (⇑(g n)-⇑f) := (toOne_coe μ (g n)).sub (toOne_coe μ f)
    rw [eLpNorm_congr_ae he]
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞)≤2)
      ((Lp.aestronglyMeasurable (g n)).sub (Lp.aestronglyMeasurable f))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz (fun _ => bot_le) hcomp

/-- Actual first time marginal of the original truncated input, in native L1. -/
def driftClass (T s : ℝ≥0) (f : fullPredictableL2 T) : Lp ℝ 1 sourceLaw :=
  timeMarginal T (toOne (inputLaw T) (truncate T s f : Lp ℝ 2 (inputLaw T)))

private theorem integral_section_ae {T : ℝ≥0} {g h : ℝ × (ℝ≥0 → ℝ) → ℝ} (he : g =ᵐ[inputLaw T] h) :
    (fun ω => ∫ t, g (t,ω) ∂timeLaw T)=ᵐ[sourceLaw] fun ω => ∫ t, h (t,ω) ∂timeLaw T := by
  have hs := (Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw T)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact integral_congr_ae hω

theorem driftClass_coe (T s : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    driftClass T s f =ᵐ[sourceLaw] drift T f K s := by
  apply (timeMarginal_coe T _).trans
  apply integral_section_ae
  filter_upwards [toOne_coe (inputLaw T) (truncate T s f : Lp ℝ 2 (inputLaw T)),truncate_coe T s f,
    boundedRepresentative_ae T f K hbound] with p h1 ht hf
  rw [h1,ht]
  by_cases hp : p∈timeSet T s
  · rw [Set.indicator_of_mem hp]
    exact hf.trans (Set.indicator_of_mem hp _).symm
  · simp only [driftIntegrand,Set.indicator_of_notMem hp]

theorem driftClass_tendsto (T s : ℝ≥0) {f : ℕ → fullPredictableL2 T} {g : fullPredictableL2 T}
    (h : Tendsto f atTop (𝓝 g)) : Tendsto (fun n => driftClass T s (f n)) atTop (𝓝 (driftClass T s g)) := by
  have ht : Tendsto (fun n => (truncate T s (f n) : Lp ℝ 2 (inputLaw T))) atTop
      (𝓝 (truncate T s g : Lp ℝ 2 (inputLaw T))) :=
    tendsto_subtype_rng.mp (((truncate T s).continuous.tendsto g).comp h)
  exact ((timeMarginal T).continuous.tendsto _).comp (toOne_tendsto (inputLaw T) ht)

private theorem cutoff_interval_eq (T a b u : ℝ≥0) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) :
    (timeSet T u).indicator (intervalIntegrand H a b) = intervalIntegrand H a (clamp a b u) := by
  funext p
  have hmem : (p ∈ timeSet T u ∧ p.1 ∈ Ioc (a : ℝ) (b : ℝ)) ↔
      p.1 ∈ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := by
    simp only [timeSet,mem_prod,mem_Ioc,mem_univ,and_true,clamp,NNReal.coe_max,NNReal.coe_min]
    constructor
    · intro h
      exact ⟨h.2.1,(le_min h.2.2 (h.1.2.trans (min_le_left _ _))).trans (le_max_right _ _)⟩
    · intro h
      have hx : p.1 ≤ min (b : ℝ) (u : ℝ) := (le_max_iff.mp h.2).resolve_left (not_le.mpr h.1)
      have hbt : (b : ℝ) ≤ (T : ℝ) := by exact_mod_cast hbT
      exact ⟨⟨a.coe_nonneg.trans_lt h.1,
        le_min (hx.trans (min_le_right _ _)) ((hx.trans (min_le_left _ _)).trans hbt)⟩,
        ⟨h.1,hx.trans (min_le_left _ _)⟩⟩
  by_cases hc : p ∈ timeSet T u
  · by_cases hi : p.1 ∈ Ioc (a : ℝ) (b : ℝ)
    · have hp := hmem.mp ⟨hc,hi⟩
      simp [intervalIntegrand,hc,hi,hp]
    · have hp : p.1 ∉ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := fun hp => hi (hmem.mpr hp).2
      simp [intervalIntegrand,hc,hi,hp]
  · have hp : p.1 ∉ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := fun hp => hc (hmem.mpr hp).1
    simp [intervalIntegrand,hc,hp]


private theorem interval_mass (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) :
    (timeLaw T).real (Ioc (a : ℝ) (b : ℝ))=(b : ℝ)-(a : ℝ) := by
  have hs : Ioc (a : ℝ) (b : ℝ) ⊆ Icc 0 (T : ℝ) := by
    intro t ht
    exact ⟨a.coe_nonneg.trans ht.1.le,ht.2.trans (by exact_mod_cast hbT)⟩
  rw [measureReal_def,timeLaw,Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr hs,
    Real.volume_Ioc,ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (by exact_mod_cast hab)

private theorem interval_section_integral (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) :
    (∫ t, intervalIntegrand H a b (t,ω) ∂timeLaw T)=((b : ℝ)-(a : ℝ))*H ω := by
  have he : (fun t => intervalIntegrand H a b (t,ω))=(Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => H ω) := by
    funext t
    by_cases ht : t∈Ioc (a : ℝ) (b : ℝ) <;> simp [intervalIntegrand,ht]
  rw [he,integral_indicator measurableSet_Ioc,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  rw [show ((timeLaw T) (Ioc (a : ℝ) (b : ℝ))).toReal=((b : ℝ)-(a : ℝ)) from interval_mass T a b hab hbT]

private theorem clamp_elapsed (a b s : ℝ≥0) (hab : a ≤ b) :
    ((clamp a b s : ℝ≥0) : ℝ)-(a : ℝ)=overlap a b s := by
  rcases le_total s a with hs | hs
  · simp only [clamp,overlap,min_eq_right (hs.trans hab),max_eq_left hs,min_eq_left (hs.trans hab),min_eq_left hs,sub_self]
  · rcases le_total s b with hb | hb
    · simp only [clamp,overlap,min_eq_right hb,max_eq_right hs,min_eq_left hb,min_eq_right hs]
    · simp only [clamp,overlap,min_eq_left hb,max_eq_right hab,min_eq_right hb,min_eq_right (hab.trans hb)]

/-- Exact original raw finite time input has precisely the returned finite
drift, with its supplied coefficients and elapsed clipped intervals. -/
theorem literal_time_integral {T : ℝ≥0} (r : ElementaryInput T) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    (∫ t, (timeSet T s).indicator (integrand r.clock r.coefficient) (t,ω) ∂timeLaw T)=
      ∑ i : Fin r.n, r.coefficient i ω*overlap (r.clock i.castSucc) (r.clock i.succ) s := by
  have hab (i : Fin r.n) : r.clock i.castSucc ≤ r.clock i.succ :=
    r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
  have hbT (i : Fin r.n) : r.clock i.succ ≤ T := (r.clock_mono (Fin.le_last _)).trans r.clock_end.le
  have he : (timeSet T s).indicator (integrand r.clock r.coefficient)=
      fun p => ∑ i : Fin r.n, intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (clamp (r.clock i.castSucc) (r.clock i.succ) s) p := by
    funext p
    have hf (i : Fin r.n) := congrFun (cutoff_interval_eq T (r.clock i.castSucc) (r.clock i.succ) s (hbT i) (r.coefficient i)) p
    rw [← Finset.sum_congr rfl (fun i _ => hf i)]
    by_cases hp : p∈timeSet T s
    · simp only [Set.indicator_of_mem hp,integrand]
    · simp only [Set.indicator_of_notMem hp,Finset.sum_const_zero]
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [interval_section_integral T _ _ (clamp_bounds _ _ _ (hab i)).1
      ((clamp_bounds _ _ _ (hab i)).2.trans (hbT i)),clamp_elapsed _ _ _ (hab i),mul_comm]
  · intro i _
    have hf : (fun t => intervalIntegrand (r.coefficient i) (r.clock i.castSucc)
        (clamp (r.clock i.castSucc) (r.clock i.succ) s) (t,ω))=
        (Ioc (r.clock i.castSucc : ℝ) (clamp (r.clock i.castSucc) (r.clock i.succ) s : ℝ≥0)).indicator
          (fun _ => r.coefficient i ω) := by
      funext t
      by_cases ht : t∈Ioc (r.clock i.castSucc : ℝ) (clamp (r.clock i.castSucc) (r.clock i.succ) s : ℝ≥0) <;>
        simp [intervalIntegrand,ht]
    rw [hf]
    exact (integrable_const _).indicator measurableSet_Ioc

/-- Native L1 time marginal is the SAME actual returned full finite-path
drift. This supplies the source identity for limiting the actual paths. -/
theorem driftClass_literal_coe {T : ℝ≥0} (r : ElementaryInput T) (s : ℝ≥0) :
    driftClass T s (literalPredictableInput r)=ᵐ[sourceLaw]
      fun ω => process s ω-tableProcess r s ω := by
  apply (timeMarginal_coe T _).trans
  have he : toOne (inputLaw T) (truncate T s (literalPredictableInput r) : Lp ℝ 2 (inputLaw T))=ᵐ[inputLaw T]
      (timeSet T s).indicator (integrand r.clock r.coefficient) := by
    filter_upwards [toOne_coe (inputLaw T) (truncate T s (literalPredictableInput r) : Lp ℝ 2 (inputLaw T)),
      truncate_coe T s (literalPredictableInput r),
      (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp] with p h1 ht hr
    change (literalPredictableInput r : Lp ℝ 2 (inputLaw T)) p=integrand r.clock r.coefficient p at hr
    rw [h1,ht]
    by_cases hp : p∈timeSet T s
    · simp only [Set.indicator_of_mem hp,hr]
    · simp only [Set.indicator_of_notMem hp]
  apply (integral_section_ae he).trans
  apply Eventually.of_forall
  intro ω
  change (∫ t, (timeSet T s).indicator (integrand r.clock r.coefficient) (t,ω) ∂timeLaw T)=process s ω-tableProcess r s ω
  rw [literal_time_integral r s ω,tableProcess_formula]
  ring

/-- Actual computed finite-table drifts converge to the SAME original f's
actual permitted dt drift, at every fixed read time on original source P. -/
theorem actual_drifts_tendstoInMeasure (T s : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    TendstoInMeasure sourceLaw
      (fun n ω => process s ω-tableProcess (approximation T f K hK hbound n) s ω) atTop (drift T f K s) := by
  have h := tendstoInMeasure_of_tendsto_Lp
    (driftClass_tendsto T s (approximation_full_tendsto T f K hK hbound))
  exact TendstoInMeasure.congr (fun n => driftClass_literal_coe _ s) (driftClass_coe T s f K hbound) h

/-- SAME actual shifted paths converge at each fixed time. This is an
in-measure source statement; it does not interchange an uncountable AE family. -/
theorem actual_paths_tendstoInMeasure (T s : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    TendstoInMeasure sourceLaw (fun n => tableProcess (approximation T f K hK hbound n) s) atTop
      (BrownianBoundedControlSource.shiftedProcess T f K s) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n =>
    (prefixProcess_measurable (approximation T f K hK hbound n) _ s).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms,hms,ha⟩ := ((actual_drifts_tendstoInMeasure T s f K hK hbound).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [ha] with ω hω
  have hc : Tendsto (fun _ : ℕ => process s ω) atTop (𝓝 (process s ω)) := tendsto_const_nhds
  have h := hc.sub hω
  change Tendsto (fun n => process s ω-(process s ω-tableProcess (approximation T f K hK hbound (ns (ms n))) s ω))
    atTop (𝓝 (process s ω-drift T f K s ω)) at h
  simpa only [sub_sub_cancel,tableProcess,BrownianBoundedControlSource.shiftedProcess] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedDriftLimitSource
