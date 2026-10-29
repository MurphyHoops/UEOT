import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralClosure
import Mathlib.Probability.Process.Predictable

/-!
Original commitment: the actual stochastic integral domain must be compared with the genuine predictable sigma algebra.
Existing result: the same-source integral is constructed on the elementary native L2 closure.
Premise reduced: identify native predictable permissions and realize its generating interval rectangles as actual inputs.
Model/witness: original natural filtration and SAME Lebesgue|[0,T] times sourceLaw, including T=0.
Consumer: full predictable L2 density; no closure renaming or external density certificate is used.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableInputs
open MeasureTheory ProbabilityTheory Set
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Real-time representation of the original nonnegative-time process. -/
def timeReadout (p : ℝ × (ℝ≥0 → ℝ)) : ℝ≥0 × (ℝ≥0 → ℝ) := (Real.toNNReal p.1,p.2)

private theorem native_predictable_le : naturalFiltration.predictable ≤
    (inferInstance : MeasurableSpace (ℝ≥0 × (ℝ≥0 → ℝ))) := by
  apply MeasurableSpace.generateFrom_le
  rintro _ (⟨A,hA,rfl⟩ | ⟨s,A,hA,rfl⟩)
  · exact (measurableSet_singleton _).prod (naturalFiltration.le 0 A hA)
  · exact measurableSet_Ioi.prod (naturalFiltration.le s A hA)

/-- The GENUINE native predictable sigma algebra, pulled back to the real
time coordinate used by the original timeLaw. -/
@[instance_reducible] def predictableSigma : MeasurableSpace (ℝ × (ℝ≥0 → ℝ)) :=
  MeasurableSpace.comap timeReadout naturalFiltration.predictable

theorem predictableSigma_le : predictableSigma ≤
    (inferInstance : MeasurableSpace (ℝ × (ℝ≥0 → ℝ))) := by
  have hm : Measurable timeReadout := (measurable_fst.real_toNNReal).prodMk measurable_snd
  exact (hm.mono le_rfl native_predictable_le).comap_le

/-- Full predictable L2 is DEFINED by the original native lpMeas subspace,
independently of the elementary closure or any desired density conclusion. -/
def fullPredictableL2 (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (inputLaw T)) :=
  lpMeas ℝ ℝ predictableSigma 2 (inputLaw T)

theorem fullPredictableL2_closed (T : ℝ≥0) : IsClosed (fullPredictableL2 T : Set (Lp ℝ 2 (inputLaw T))) :=
  isClosed_aestronglyMeasurable predictableSigma_le

private theorem nnreal_lt_toNNReal (s : ℝ≥0) (x : ℝ) : s < Real.toNNReal x ↔ (s : ℝ) < x := by
  simpa only [not_le] using (Real.toNNReal_le_iff_le_coe (r := x) (p := s)).not

/-- The original START-time permission is sufficient to make actual
(s,t] times A measurable in the native predictable sigma; no future observation is used. -/
theorem predictable_interval_rectangle (s t : ℝ≥0) {A : Set (ℝ≥0 → ℝ)}
    (hA : MeasurableSet[naturalFiltration s] A) :
    MeasurableSet[predictableSigma] (Ioc (s : ℝ) (t : ℝ) ×ˢ A) := by
  have hm : @Measurable (ℝ × (ℝ≥0 → ℝ)) (ℝ≥0 × (ℝ≥0 → ℝ))
      predictableSigma naturalFiltration.predictable timeReadout :=
    measurable_iff_comap_le.mpr le_rfl
  have h := (measurableSet_predictable_Ioc_prod s t hA).preimage hm
  convert h using 1
  ext p
  simp only [timeReadout,mem_preimage,mem_prod,mem_Ioc,nnreal_lt_toNNReal,
    Real.toNNReal_le_iff_le_coe]

/-- Genuine start-past permission makes the entire literal input block
predictable, even for arbitrary bounded measurable coefficients. -/
theorem intervalIntegrand_predictable {H : (ℝ≥0 → ℝ) → ℝ} (s t : ℝ≥0)
    (hH : StronglyMeasurable[naturalFiltration s] H) :
    StronglyMeasurable[predictableSigma] (intervalIntegrand H s t) := by
  apply Measurable.stronglyMeasurable
  intro B hB
  have hHB := hH.measurable hB
  have hrect := predictable_interval_rectangle s t hHB
  have hwhole := predictable_interval_rectangle s t (MeasurableSet.univ : MeasurableSet[naturalFiltration s] (univ : Set (ℝ≥0 → ℝ)))
  by_cases h0 : (0 : ℝ) ∈ B
  · have he : intervalIntegrand H s t ⁻¹' B =
        (Ioc (s : ℝ) (t : ℝ) ×ˢ (H ⁻¹' B)) ∪ (Ioc (s : ℝ) (t : ℝ) ×ˢ (univ : Set (ℝ≥0 → ℝ)))ᶜ := by
      ext p
      by_cases hp : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [intervalIntegrand,hp,h0]
    rw [he]
    exact hrect.union hwhole.compl
  · have he : intervalIntegrand H s t ⁻¹' B = Ioc (s : ℝ) (t : ℝ) ×ˢ (H ⁻¹' B) := by
      ext p
      by_cases hp : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [intervalIntegrand,hp,h0]
    rw [he]
    exact hrect

set_option maxHeartbeats 800000 in
theorem elementary_input_predictable {T : ℝ≥0} (r : ElementaryInput T) : inputValue r ∈ fullPredictableL2 T := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hm : StronglyMeasurable[predictableSigma] (integrand r.clock r.coefficient) := by
    have h : StronglyMeasurable[predictableSigma]
        (∑ i : Fin r.n, intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)) :=
      Finset.stronglyMeasurable_sum Finset.univ (fun i _ =>
        intervalIntegrand_predictable (r.clock i.castSucc) (r.clock i.succ) (r.coefficient_past i))
    convert! h using 1
    ext p
    simp only [integrand,Finset.sum_apply]
  exact hm.aestronglyMeasurable.congr (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp.symm

/-- One genuine inclusion, with the right-hand side fixed independently by
native predictable measurability. Reverse inclusion still requires density. -/
theorem integralDomain_le_fullPredictableL2 (T : ℝ≥0) : integralDomain T ≤ fullPredictableL2 T := by
  apply (elementarySpan T).topologicalClosure_minimal _ (fullPredictableL2_closed T)
  rw [elementarySpan_eq_span]
  exact Submodule.span_le.mpr (by rintro _ ⟨r,rfl⟩; exact elementary_input_predictable r)

/-- Concrete actual input for coefficient H on (s,T], preceded by zero. -/
def blockInput (T s : ℝ≥0) (hsT : s ≤ T) (H : (ℝ≥0 → ℝ) → ℝ)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) : ElementaryInput T where
  n := 2
  clock := ![0,s,T]
  coefficient := ![fun _ => 0,H]
  clock_mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := by
    intro i
    fin_cases i
    · exact stronglyMeasurable_const
    · exact hHpast
  coefficient_bounded := by intro i; fin_cases i; exact MemLp.zero; exact hH

/-- The record's native input is the actual time block, with no a.e.-chosen
input replacing it. -/
theorem blockInput_class (T s : ℝ≥0) (hsT : s ≤ T) (H : (ℝ≥0 → ℝ) → ℝ)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hH : MemLp H ∞ sourceLaw) :
    inputValue (blockInput T s hsT H hHpast hH) =
      (intervalIntegrand_memLp_two hH T s T).toLp (intervalIntegrand H s T) := by
  apply Lp.ext
  apply (integrand_memLp_two T _ _ (blockInput T s hsT H hHpast hH).coefficient_bounded).coeFn_toLp.trans
  apply Filter.EventuallyEq.trans _ (intervalIntegrand_memLp_two hH T s T).coeFn_toLp.symm
  apply Filter.Eventually.of_forall
  intro p
  change (∑ i : Fin 2, intervalIntegrand (![fun _ => 0,H] i) (![0,s,T] i.castSucc) (![0,s,T] i.succ) p) = _
  rw [Fin.sum_univ_two]
  simp [intervalIntegrand]

/-- One actual full-measure time support event. T=0 is included: then
inputLaw is zero and this a.e. statement has no exceptional positive mass. -/
theorem time_support_ae (T : ℝ≥0) : ∀ᵐ p ∂inputLaw T, p.1 ∈ Ioc (0 : ℝ) (T : ℝ) := by
  have htime : ∀ᵐ x ∂timeLaw T, x ∈ Ioc (0 : ℝ) (T : ℝ) := by
    have hnot : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hnot] with x hx hn
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hn),hx.2⟩
  apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Ioc)).mpr
  exact htime.mono (fun x hx => Filter.Eventually.of_forall (fun _ => hx))

/-- Only a short name for the ORIGINAL native indicatorConstLp under the
actual fixed inputLaw; no new quotient or simple-function framework. -/
def indicatorClass (T : ℝ≥0) (A : Set (ℝ × (ℝ≥0 → ℝ))) (hA : MeasurableSet A) (c : ℝ) :
    Lp ℝ 2 (inputLaw T) := indicatorConstLp 2 hA (measure_ne_top _ _) c

theorem indicatorClass_congr_ae (T : ℝ≥0) (A B : Set (ℝ × (ℝ≥0 → ℝ)))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℝ) (heq : A =ᵐ[inputLaw T] B) :
    indicatorClass T A hA c = indicatorClass T B hB c := by
  classical
  unfold indicatorClass
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top _ _) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top _ _) (c := c),heq] with p ha hb hp
  rw [ha,hb]
  change (if A p then c else 0) = (if B p then c else 0)
  exact congrArg (fun q : Prop => if q then c else (0 : ℝ)) hp

/-- The true generating (s,T] times A class is realized by an ACTUAL bounded
past input and therefore belongs to the already constructed integral domain. -/
theorem interval_rectangle_mem_domain (T s : ℝ≥0) (hsT : s ≤ T) (A : Set (ℝ≥0 → ℝ))
    (hA : MeasurableSet[naturalFiltration s] A) (c : ℝ) :
    indicatorClass T (Ioc (s : ℝ) (T : ℝ) ×ˢ A)
      (measurableSet_Ioc.prod (naturalFiltration.le s A hA)) c ∈ integralDomain T := by
  let H := A.indicator (fun _ : ℝ≥0 → ℝ => c)
  have hpast : StronglyMeasurable[naturalFiltration s] H := stronglyMeasurable_const.indicator hA
  have hbound : MemLp H ∞ sourceLaw :=
    (memLp_top_const c).indicator (naturalFiltration.le s A hA)
  have hx : inputValue (blockInput T s hsT H hpast hbound) ∈ integralDomain T :=
    (representedInput (blockInput T s hsT H hpast hbound)).property
  rw [blockInput_class T s hsT H hpast hbound] at hx
  have he : indicatorClass T (Ioc (s : ℝ) (T : ℝ) ×ˢ A)
      (measurableSet_Ioc.prod (naturalFiltration.le s A hA)) c =
      (intervalIntegrand_memLp_two hbound T s T).toLp (intervalIntegrand H s T) := by
    unfold indicatorClass
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2) (s := Ioc (s : ℝ) (T : ℝ) ×ˢ A)
      (hs := measurableSet_Ioc.prod (naturalFiltration.le s A hA)) (hμs := measure_ne_top _ _) (c := c),
      (intervalIntegrand_memLp_two hbound T s T).coeFn_toLp] with p ha hb
    rw [ha,hb]
    by_cases ht : p.1 ∈ Ioc (s : ℝ) (T : ℝ) <;> by_cases hω : p.2 ∈ A <;>
      simp [intervalIntegrand,H,ht,hω]
  rw [he]
  exact hx

/-- The actual native predictable future rectangle is trimmed by the SAME
horizon measure, and is zero when its start lies beyond T. -/
theorem future_rectangle_mem_domain (T s : ℝ≥0) (A : Set (ℝ≥0 → ℝ))
    (hA : MeasurableSet[naturalFiltration s] A) (c : ℝ) :
    indicatorClass T (Ioi (s : ℝ) ×ˢ A)
      (measurableSet_Ioi.prod (naturalFiltration.le s A hA)) c ∈ integralDomain T := by
  by_cases hsT : s ≤ T
  · have he : Ioi (s : ℝ) ×ˢ A =ᵐ[inputLaw T] Ioc (s : ℝ) (T : ℝ) ×ˢ A := by
      filter_upwards [time_support_ae T] with p hp
      apply propext
      constructor
      · intro h
        exact ⟨⟨h.1,hp.2⟩,h.2⟩
      · intro h
        exact ⟨h.1.1,h.2⟩
    rw [indicatorClass_congr_ae T _ _ _
      (measurableSet_Ioc.prod (naturalFiltration.le s A hA)) c he]
    exact interval_rectangle_mem_domain T s hsT A hA c
  · have hz : indicatorClass T (Ioi (s : ℝ) ×ˢ A)
        (measurableSet_Ioi.prod (naturalFiltration.le s A hA)) c = 0 := by
      unfold indicatorClass
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (s := Ioi (s : ℝ) ×ˢ A)
        (hs := measurableSet_Ioi.prod (naturalFiltration.le s A hA)) (hμs := measure_ne_top _ _) (c := c),
        time_support_ae T,Lp.coeFn_zero ℝ 2 (inputLaw T)] with p hc hp hz
      rw [hc,hz]
      have hTs : (T : ℝ) < (s : ℝ) := by exact_mod_cast lt_of_not_ge hsT
      have hnot : p.1 ∉ Ioi (s : ℝ) := not_lt.mpr (hp.2.trans hTs.le)
      simp [hnot]
    rw [hz]
    exact Submodule.zero_mem _

/-- The native time-zero generator pulls back to nonpositive real time.
Its class is strictly zero under actual dt|[0,T] times P, including T=0. -/
theorem zero_rectangle_class_zero (T : ℝ≥0) (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet A) (c : ℝ) :
    indicatorClass T (Iic (0 : ℝ) ×ˢ A) (measurableSet_Iic.prod hA) c = 0 := by
  unfold indicatorClass
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (s := Iic (0 : ℝ) ×ˢ A) (hs := measurableSet_Iic.prod hA)
    (hμs := measure_ne_top _ _) (c := c),time_support_ae T,Lp.coeFn_zero ℝ 2 (inputLaw T)] with p hc hp hz
  rw [hc,hz]
  have hn : p.1 ∉ Iic (0 : ℝ) := not_le.mpr hp.1
  simp [hn]

/-- Constants are actual predictable block classes up to the strictly null
time-zero boundary, giving the univ case needed by sigma-algebra induction. -/
theorem constant_indicator_mem_domain (T : ℝ≥0) (c : ℝ) :
    indicatorClass T univ MeasurableSet.univ c ∈ integralDomain T := by
  have he : (univ : Set (ℝ × (ℝ≥0 → ℝ))) =ᵐ[inputLaw T] Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ≥0 → ℝ)) := by
    filter_upwards [time_support_ae T] with p hp
    apply propext
    exact ⟨fun _ => ⟨hp.1,mem_univ p.2⟩,fun _ => mem_univ p⟩
  rw [indicatorClass_congr_ae T _ _ _ (measurableSet_Ioi.prod MeasurableSet.univ) c he]
  exact future_rectangle_mem_domain T 0 univ MeasurableSet.univ c

/-- Exact relation between the native predictable generator and the actual
real-time input coordinate. -/
theorem readout_preimage_future (s : ℝ≥0) (A : Set (ℝ≥0 → ℝ)) :
    timeReadout ⁻¹' (Ioi s ×ˢ A) = Ioi (s : ℝ) ×ˢ A := by
  ext p
  simp only [timeReadout,mem_preimage,mem_prod,mem_Ioi,nnreal_lt_toNNReal]

theorem readout_preimage_zero (A : Set (ℝ≥0 → ℝ)) :
    timeReadout ⁻¹' (({0} : Set ℝ≥0) ×ˢ A) = Iic (0 : ℝ) ×ˢ A := by
  ext p
  simp only [timeReadout,mem_preimage,mem_prod,mem_singleton_iff,mem_Iic,Real.toNNReal_eq_zero]

/-- The horizon-zero measure is derived zero, not bypassed by T>0. -/
theorem inputLaw_zero : inputLaw 0 = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have h := time_support_ae 0
  rw [ae_iff] at h
  simpa only [NNReal.coe_zero,Ioc_self,mem_empty_iff_false,not_false_eq_true,Set.ofPred_true] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableInputs
