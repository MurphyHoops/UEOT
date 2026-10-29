import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTimeEnergy

/-!
Original commitment: actual conditional second energy requires localizing the SAME future integral by an allowed past event.
Existing result: native actual integral isometry/density, literal interval consumers and original predictable event rectangles.
Premise reduced: derive actual Fs-event future-window commutation from the original literal data and native continuity.
Model/witness: SAME fixed inputLaw T/sourceLaw/naturalFiltration, original A measurable at s, future window (s,t].
Consumer: actual full-input squared-integral time-energy compensator; no local-isometry certificate is input.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralPastLocalization
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianOneStepIntegral BrownianSimplePredictableIntegral
open BrownianCommonRefinement BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs
open BrownianPredictableDensity BrownianIntegralTimeTruncation BrownianIntegralLiteralIntervals
open BrownianIntegralFinitePaths BrownianIntegralMartingale BrownianIntegralTimeEnergy BrownianIntegralContinuousVersion
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private def indicatorClass {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α) (hS : MeasurableSet S) :
    Lp ℝ ∞ μ :=
  ((memLp_top_const (μ := μ) (1 : ℝ)).indicator hS).toLp (S.indicator (fun _ => (1 : ℝ)))

private def indicatorMultiply {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α) (hS : MeasurableSet S) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2 (indicatorClass μ S hS)

private theorem indicatorMultiply_coe {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Set α) (hS : MeasurableSet S) (f : Lp ℝ 2 μ) :
    indicatorMultiply μ S hS f =ᵐ[μ] S.indicator f := by
  have hc := ((memLp_top_const (μ := μ) (1 : ℝ)).indicator hS).coeFn_toLp
  have hh := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (indicatorClass μ S hS) f
  apply hh.trans
  filter_upwards [hc] with p hp
  change indicatorClass μ S hS p*f p = S.indicator f p
  change indicatorClass μ S hS p = _ at hp
  rw [hp]
  by_cases ht : p ∈ S <;> simp [ht]

/-- Actual source-event multiplication, with its original Fs permission explicit. -/
def sourceIndicator (s : ℝ≥0) (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) :
    Lp ℝ 2 sourceLaw →L[ℝ] Lp ℝ 2 sourceLaw :=
  indicatorMultiply sourceLaw A (naturalFiltration.le s A hA)

theorem sourceIndicator_coe (s : ℝ≥0) (A : Set (ℝ≥0 → ℝ))
    (hA : MeasurableSet[naturalFiltration s] A) (g : Lp ℝ 2 sourceLaw) :
    sourceIndicator s A hA g =ᵐ[sourceLaw] A.indicator g := indicatorMultiply_coe _ _ _ _

/-- Lower endpoint s is unchanged; if s>T this literal window is empty.
Thus original Fs permission is never silently shifted to an earlier F_min(s,T). -/
def eventWindow (T s t : ℝ≥0) (A : Set (ℝ≥0 → ℝ)) : Set (ℝ × (ℝ≥0 → ℝ)) :=
  Ioc (s : ℝ) ((min t T : ℝ≥0) : ℝ) ×ˢ A

theorem eventWindow_predictable (T s t : ℝ≥0) {A : Set (ℝ≥0 → ℝ)}
    (hA : MeasurableSet[naturalFiltration s] A) : MeasurableSet[predictableSigma] (eventWindow T s t A) :=
  predictable_interval_rectangle s (min t T) hA

private theorem eventWindow_measurable (T s t : ℝ≥0) {A : Set (ℝ≥0 → ℝ)}
    (hA : MeasurableSet[naturalFiltration s] A) : MeasurableSet (eventWindow T s t A) :=
  predictableSigma_le _ (eventWindow_predictable T s t hA)

private theorem localized_predictable (T s t : ℝ≥0) {A : Set (ℝ≥0 → ℝ)}
    (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    indicatorMultiply (inputLaw T) (eventWindow T s t A) (eventWindow_measurable T s t hA) f ∈ fullPredictableL2 T := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  refine ⟨(eventWindow T s t A).indicator (representative T f),
    (representative_predictable T f).indicator (eventWindow_predictable T s t hA),?_⟩
  filter_upwards [indicatorMultiply_coe (inputLaw T) (eventWindow T s t A) (eventWindow_measurable T s t hA) f,
    representative_ae T f] with p hp hf
  rw [hp]
  by_cases h : p ∈ eventWindow T s t A <;> simp [h,hf]

/-- Actual permitted future-window localization on original full predictable L2. -/
def localize (T s t : ℝ≥0) (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) :
    fullPredictableL2 T →L[ℝ] fullPredictableL2 T :=
  ((indicatorMultiply (inputLaw T) (eventWindow T s t A) (eventWindow_measurable T s t hA)).comp
    (fullPredictableL2 T).subtypeL).codRestrict (fullPredictableL2 T) (localized_predictable T s t hA)

theorem localize_coe (T s t : ℝ≥0) (A : Set (ℝ≥0 → ℝ))
    (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    (localize T s t A hA f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      (eventWindow T s t A).indicator (f : Lp ℝ 2 (inputLaw T)) := indicatorMultiply_coe _ _ _ _

private theorem interval_prefix_class (T a b u : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHp : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    integralAt T u (intervalInput T a b hab hbT H hHp hH) =
      (oneStep_memLp_two hH a (clamp a b u)).toLp (oneStep H a (clamp a b u)) := by
  change predictableIntegral T (truncate T u (intervalInput T a b hab hbT H hHp hH)) = _
  rw [truncate_intervalInput,integral_interval_literal]

private theorem clamp_overlap (a b s t : ℝ≥0) (hab : a ≤ b)
    (ht : a ≤ t) (hs : s ≤ b) :
    clamp a b s = max a s ∧ clamp a b t = min b t := by
  constructor
  · simp only [clamp,min_eq_right hs]
  · exact max_eq_right (le_min hab ht)

private theorem window_interval_function (T a b s t : ℝ≥0) (hbT : b ≤ T)
    (A : Set (ℝ≥0 → ℝ)) (H : (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) :
    (eventWindow T s t A).indicator (intervalIntegrand H a b) p =
      intervalIntegrand (A.indicator H) (max a s) (min b t) p := by
  have he : (p.1 ∈ Ioc (a : ℝ) (b : ℝ) ∧ p ∈ eventWindow T s t A) ↔
      (p.1 ∈ Ioc ((max a s : ℝ≥0) : ℝ) ((min b t : ℝ≥0) : ℝ) ∧ p.2 ∈ A) := by
    simp only [eventWindow,mem_prod,mem_Ioc,NNReal.coe_max,NNReal.coe_min,max_lt_iff,le_min_iff]
    constructor
    · rintro ⟨⟨ha,hb⟩,⟨⟨hs,ht,hT⟩,hA⟩⟩
      exact ⟨⟨⟨ha,hs⟩,⟨hb,ht⟩⟩,hA⟩
    · rintro ⟨⟨⟨ha,hs⟩,⟨hb,ht⟩⟩,hA⟩
      exact ⟨⟨ha,hb⟩,⟨⟨hs,ht,hb.trans (by exact_mod_cast hbT)⟩,hA⟩⟩
  by_cases hw : p ∈ eventWindow T s t A
  · by_cases ho : p.1 ∈ Ioc (a : ℝ) (b : ℝ)
    · obtain ⟨hn,hA⟩ := he.mp ⟨ho,hw⟩
      simp only [Set.indicator_of_mem hw,intervalIntegrand,Set.indicator_of_mem ho,Set.indicator_of_mem hn,
        Set.indicator_of_mem hA,one_mul]
    · have hn : p.1 ∉ Ioc ((max a s : ℝ≥0) : ℝ) ((min b t : ℝ≥0) : ℝ) := by
        intro hn
        exact ho (he.mpr ⟨hn,hw.2⟩).1
      simp only [Set.indicator_of_mem hw,intervalIntegrand,Set.indicator_of_notMem ho,
        Set.indicator_of_notMem hn,zero_mul]
  · by_cases hn : p.1 ∈ Ioc ((max a s : ℝ≥0) : ℝ) ((min b t : ℝ≥0) : ℝ)
    · have hA : p.2 ∉ A := fun hA => hw (he.mpr ⟨hn,hA⟩).2
      simp only [Set.indicator_of_notMem hw,intervalIntegrand,Set.indicator_of_mem hn,
        Set.indicator_of_notMem hA,one_mul]
    · simp only [Set.indicator_of_notMem hw,intervalIntegrand,Set.indicator_of_notMem hn,zero_mul]

private theorem localize_interval_overlap (T a b s t : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (hcd : max a s ≤ min b t) (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHp : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    localize T s t A hA (intervalInput T a b hab hbT H hHp hH) =
      intervalInput T (max a s) (min b t) hcd ((min_le_left b t).trans hbT) (A.indicator H)
        ((hHp.mono (naturalFiltration.mono (le_max_left a s))).indicator
          ((naturalFiltration.mono (le_max_right a s)) A hA))
        (hH.indicator (naturalFiltration.le s A hA)) := by
  apply Subtype.ext
  apply Lp.ext
  have hi := intervalInput_coe T a b hab hbT H hHp hH
  have hk := intervalInput_coe T (max a s) (min b t) hcd ((min_le_left b t).trans hbT) (A.indicator H)
    ((hHp.mono (naturalFiltration.mono (le_max_left a s))).indicator
      ((naturalFiltration.mono (le_max_right a s)) A hA))
    (hH.indicator (naturalFiltration.le s A hA))
  filter_upwards [localize_coe T s t A hA (intervalInput T a b hab hbT H hHp hH),hi,hk] with p hl hi hk
  rw [hl,hk]
  by_cases he : p ∈ eventWindow T s t A
  · rw [Set.indicator_of_mem he,hi]
    simpa only [Set.indicator_of_mem he] using window_interval_function T a b s t hbT A H p
  · rw [Set.indicator_of_notMem he]
    simpa only [Set.indicator_of_notMem he] using window_interval_function T a b s t hbT A H p

private theorem localize_interval_zero (T a b s t : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (hzero : min b t ≤ max a s) (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHp : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    localize T s t A hA (intervalInput T a b hab hbT H hHp hH) = 0 := by
  apply Subtype.ext
  apply Lp.ext
  have hempty : Ioc ((max a s : ℝ≥0) : ℝ) ((min b t : ℝ≥0) : ℝ) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun x hx =>
      (not_lt_of_ge (hx.2.trans (by exact_mod_cast hzero))) hx.1)
  filter_upwards [localize_coe T s t A hA (intervalInput T a b hab hbT H hHp hH),
    intervalInput_coe T a b hab hbT H hHp hH,Lp.coeFn_zero ℝ 2 (inputLaw T)] with p hl hi hz
  change (localize T s t A hA (intervalInput T a b hab hbT H hHp hH) : Lp ℝ 2 (inputLaw T)) p =
    (0 : Lp ℝ 2 (inputLaw T)) p
  rw [hl,hz]
  change (eventWindow T s t A).indicator (intervalInput T a b hab hbT H hHp hH : Lp ℝ 2 (inputLaw T)) p = 0
  have hf := window_interval_function T a b s t hbT A H p
  simp only [intervalIntegrand,hempty,Set.indicator_empty,zero_mul] at hf
  by_cases he : p ∈ eventWindow T s t A
  · rw [Set.indicator_of_mem he,hi]
    simpa only [Set.indicator_of_mem he] using hf
  · rw [Set.indicator_of_notMem he]

/-- Actual literal interval source is localized using ONLY A in Fs and the
FUTURE window. Original H is never allowed earlier than its original a. -/
theorem localize_interval_integral (T a b s t : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHp : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    predictableIntegral T (localize T s t A hA (intervalInput T a b hab hbT H hHp hH)) =
      sourceIndicator s A hA ((integralAt T t-integralAt T s) (intervalInput T a b hab hbT H hHp hH)) := by
  by_cases hbefore : t ≤ a
  · have hzero : min b t ≤ max a s := (min_le_right b t).trans (hbefore.trans (le_max_left a s))
    have hc₁ : clamp a b s = a := by
      simp only [clamp,min_eq_right ((hst.trans hbefore).trans hab),max_eq_left (hst.trans hbefore)]
    have hc₂ : clamp a b t = a := by
      simp only [clamp,min_eq_right (hbefore.trans hab),max_eq_left hbefore]
    rw [localize_interval_zero T a b s t hab hbT hzero A hA H hHp hH,map_zero,
      sub_apply,interval_prefix_class,interval_prefix_class,hc₁,hc₂,sub_self,map_zero]
  · have hat : a ≤ t := (lt_of_not_ge hbefore).le
    by_cases hafter : b ≤ s
    · have hzero : min b t ≤ max a s := (min_le_left b t).trans (hafter.trans (le_max_right a s))
      have hc₁ : clamp a b s = b := by simp only [clamp,min_eq_left hafter,max_eq_right hab]
      have hc₂ : clamp a b t = b := by simp only [clamp,min_eq_left (hafter.trans hst),max_eq_right hab]
      rw [localize_interval_zero T a b s t hab hbT hzero A hA H hHp hH,map_zero,
        sub_apply,interval_prefix_class,interval_prefix_class,hc₁,hc₂,sub_self,map_zero]
    · have hsb : s ≤ b := (lt_of_not_ge hafter).le
      have hcd : max a s ≤ min b t := max_le (le_min hab hat) (le_min hsb hst)
      obtain ⟨hcs,hct⟩ := clamp_overlap a b s t hab hat hsb
      rw [localize_interval_overlap T a b s t hab hbT hcd A hA H hHp hH,integral_interval_literal,
        sub_apply,interval_prefix_class,interval_prefix_class,hct,hcs]
      apply Lp.ext
      filter_upwards [
        (oneStep_memLp_two (hH.indicator (naturalFiltration.le s A hA)) (max a s) (min b t)).coeFn_toLp,
        sourceIndicator_coe s A hA
          ((oneStep_memLp_two hH a (min b t)).toLp (oneStep H a (min b t))-
            (oneStep_memLp_two hH a (max a s)).toLp (oneStep H a (max a s))),
        Lp.coeFn_sub ((oneStep_memLp_two hH a (min b t)).toLp (oneStep H a (min b t)))
          ((oneStep_memLp_two hH a (max a s)).toLp (oneStep H a (max a s))),
        (oneStep_memLp_two hH a (min b t)).coeFn_toLp,
        (oneStep_memLp_two hH a (max a s)).coeFn_toLp] with ω hl hr hd ht hs
      rw [hl,hr]
      by_cases he : ω ∈ A
      · rw [Set.indicator_of_mem he]
        simp only [Pi.sub_apply] at hd
        rw [hd,ht,hs]
        simp only [oneStep,Pi.mul_apply,increment,Set.indicator_of_mem he]
        ring
      · rw [Set.indicator_of_notMem he]
        simp only [oneStep,Pi.mul_apply,Set.indicator_of_notMem he,zero_mul]

private theorem lp_sum_coe (S : Finset ι) (F : ι → Lp ℝ 2 (inputLaw T)) :
    (∑ i ∈ S, F i : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T] fun p => ∑ i ∈ S, F i p := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 (inputLaw T)] with p hp
    simp only [Finset.sum_empty]
    exact hp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ S, F j),ih] with p ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

private def recordPart {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : fullPredictableL2 T :=
  intervalInput T (r.clock i.castSucc) (r.clock i.succ)
    (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ)))
    ((r.clock_mono (Fin.le_last i.succ)).trans r.clock_end.le)
    (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)

/-- Minimal native typed adapter: the original finite input decomposes into
its SAME actual interval records. The prior projection proof used a private
version; this source does not depend on private generated declaration names. -/
private theorem record_decomposition {T : ℝ≥0} (r : ElementaryInput T) :
    literalPredictableInput r = ∑ i : Fin r.n, recordPart r i := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  apply Lp.ext
  have hi : ∀ᵐ p ∂inputLaw T, ∀ i : Fin r.n,
      (recordPart r i : Lp ℝ 2 (inputLaw T)) p =
        intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p :=
    ae_all_iff.mpr (fun i => intervalInput_coe T _ _ _ _ (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i))
  filter_upwards [(integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
    lp_sum_coe Finset.univ (fun i => (recordPart r i : Lp ℝ 2 (inputLaw T))),hi] with p hp hs hi
  change ((integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).toLp
    (integrand r.clock r.coefficient)) p = (∑ i : Fin r.n, (recordPart r i : Lp ℝ 2 (inputLaw T))) p
  rw [hp,hs]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)

/-- FULL original-input localization law, derived from actual interval
sources and the original proved dense finite span. -/
theorem predictableIntegral_localize (T s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    predictableIntegral T (localize T s t A hA f) =
      sourceIndicator s A hA ((integralAt T t-integralAt T s) f) := by
  let L := (predictableIntegral T).comp (localize T s t A hA)
  let R := (sourceIndicator s A hA).comp (integralAt T t-integralAt T s)
  have hr (r : ElementaryInput T) : L (literalPredictableInput r) = R (literalPredictableInput r) := by
    rw [record_decomposition,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact localize_interval_integral T _ _ s t _ _ hst A hA
      (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)
  have hd : DenseRange (spanInput T) := by
    apply Metric.denseRange_iff.mpr
    intro g ε hε
    obtain ⟨a,ha⟩ := exists_spanInput_dist_lt T g ε hε
    exact ⟨a,by simpa only [dist_comm] using ha⟩
  have he : L = R := by
    apply ContinuousLinearMap.ext
    intro g
    refine hd.induction_on g (isClosed_eq L.continuous R.continuous) ?_
    intro a
    simp only [spanInput,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,hr]
  exact congrArg (fun K : fullPredictableL2 T →L[ℝ] Lp ℝ 2 sourceLaw => K f) he

/-- Concrete returned output of the actual localized input: EXACTLY the past
indicator times the actual continuous integral increment, source-a.e. -/
theorem predictableIntegral_localize_coe (T s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    (predictableIntegral T (localize T s t A hA f) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      A.indicator (fun ω => continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω) := by
  rw [predictableIntegral_localize T s t hst A hA f]
  apply (sourceIndicator_coe s A hA ((integralAt T t-integralAt T s) f)).trans
  filter_upwards [Lp.coeFn_sub (integralAt T t f) (integralAt T s f),
    (continuousIntegralProcess_eq_actual T t f).trans (integralProcess_eq_truncated T t f),
    (continuousIntegralProcess_eq_actual T s f).trans (integralProcess_eq_truncated T s f)] with ω hd ht hs
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω,Set.indicator_of_mem hω]
    simp only [Pi.sub_apply] at hd
    change (integralAt T t f-integralAt T s f : Lp ℝ 2 sourceLaw) ω = _
    rw [hd]
    exact congrArg₂ (fun x y : ℝ => x-y) ht.symm hs.symm
  · rw [Set.indicator_of_notMem hω,Set.indicator_of_notMem hω]

private theorem lp_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : Lp ℝ 2 μ) :
    ‖g‖^2 = ∫ a, g a^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- Actual conditional second-energy source. This follows from the proved
localization law and ORIGINAL integral isometry, not a supplied local-isometry
certificate. A is allowed only in Fs and only the FUTURE input window is used. -/
theorem localized_second_energy (T s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (f : fullPredictableL2 T) :
    (∫ ω in A, (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)^2 ∂sourceLaw) =
      ∫ p in eventWindow T s t A, (f : Lp ℝ 2 (inputLaw T)) p^2 ∂inputLaw T := by
  have hs : (fun ω => predictableIntegral T (localize T s t A hA f) ω ^ 2) =ᵐ[sourceLaw]
      A.indicator (fun ω => (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)^2) := by
    filter_upwards [predictableIntegral_localize_coe T s t hst A hA f] with ω hω
    rw [hω]
    by_cases h : ω ∈ A <;> simp [h]
  have hi : (fun p => (localize T s t A hA f : Lp ℝ 2 (inputLaw T)) p^2) =ᵐ[inputLaw T]
      (eventWindow T s t A).indicator (fun p => (f : Lp ℝ 2 (inputLaw T)) p^2) := by
    filter_upwards [localize_coe T s t A hA f] with p hp
    rw [hp]
    by_cases h : p ∈ eventWindow T s t A <;> simp [h]
  calc
    _ = ∫ ω, predictableIntegral T (localize T s t A hA f) ω ^ 2 ∂sourceLaw := by
      rw [integral_congr_ae hs,integral_indicator (naturalFiltration.le s A hA)]
    _ = ‖predictableIntegral T (localize T s t A hA f)‖^2 := (lp_norm_sq _ _).symm
    _ = ‖localize T s t A hA f‖^2 := by rw [predictableIntegral_norm]
    _ = ∫ p, (localize T s t A hA f : Lp ℝ 2 (inputLaw T)) p^2 ∂inputLaw T := lp_norm_sq _ _
    _ = _ := by rw [integral_congr_ae hi,integral_indicator (eventWindow_measurable T s t hA)]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralPastLocalization
