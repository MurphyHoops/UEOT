import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableInputs

/-!
Original commitment: the SAME finite-vector noise integral must consume every genuine joint-predictable Euclidean L2 input.
Existing result: literal source outputs extend isometrically on elementary closure, which lies in native joint-predictable lpMeas.
Premise reduced: derive the reverse inclusion by actual vector generator blocks and native predictable/Lp induction.
Model/witness: arbitrary finite d, original timeLaw T times productLaw d and whole-joint natural past, including d0/T0.
Consumer: SAME scalar-projection integral on full native Euclidean predictable L2 returns every actual finite literal output.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableDensity
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput
open BrownianVectorIntegralClosure BrownianVectorPredictableInputs
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory symmDiff
noncomputable section
variable (d : ℕ)

private theorem nnreal_lt_toNNReal (s : ℝ≥0) (x : ℝ) : s < Real.toNNReal x ↔ (s : ℝ) < x := by
  simpa only [not_le] using (Real.toNNReal_le_iff_le_coe (r := x) (p := s)).not

/-- One actual full-measure time support event. T=0 is included: then
(inputLaw d) is zero and this a.e. statement has no exceptional positive mass. -/
theorem time_support_ae (T : ℝ≥0) : ∀ᵐ p ∂(inputLaw d) T, p.1 ∈ Ioc (0 : ℝ) (T : ℝ) := by
  have htime : ∀ᵐ x ∂BrownianTimeIntegrand.timeLaw T, x ∈ Ioc (0 : ℝ) (T : ℝ) := by
    have hnot : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hnot] with x hx hn
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hn),hx.2⟩
  apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Ioc)).mpr
  exact htime.mono (fun x hx => Filter.Eventually.of_forall (fun _ => hx))

/-- Only a short name for the ORIGINAL native indicatorConstLp under the
actual fixed vector inputLaw; no new quotient or simple-function framework. -/
def indicatorClass (T : ℝ≥0) (A : Set (ℝ × (Sample d))) (hA : MeasurableSet A) (c : EuclideanSpace ℝ (Fin d)) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T) := indicatorConstLp 2 hA (measure_ne_top _ _) c

theorem indicatorClass_congr_ae (T : ℝ≥0) (A B : Set (ℝ × (Sample d)))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c : EuclideanSpace ℝ (Fin d)) (heq : A =ᵐ[(inputLaw d) T] B) :
    (indicatorClass d) T A hA c = (indicatorClass d) T B hB c := by
  classical
  unfold indicatorClass
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top _ _) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top _ _) (c := c),heq] with p ha hb hp
  rw [ha,hb]
  change (if A p then c else 0) = (if B p then c else 0)
  exact congrArg (fun q : Prop => if q then c else (0 : EuclideanSpace ℝ (Fin d))) hp

/-- The true generating (s,T] times A class is realized by an ACTUAL bounded
past input and therefore belongs to the already constructed integral domain. -/
theorem interval_rectangle_mem_domain (T s : ℝ≥0) (hsT : s ≤ T) (A : Set (Sample d))
    (hA : MeasurableSet[jointNaturalFiltration d s] A) (c : EuclideanSpace ℝ (Fin d)) :
    indicatorClass d T (Ioc (s : ℝ) (T : ℝ) ×ˢ A)
      (measurableSet_Ioc.prod ((jointNaturalFiltration d).le s A hA)) c ∈ integralDomain d T := by
  let H : Fin d → Sample d → ℝ := fun k => A.indicator (fun _ => c k)
  have hpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k) :=
    fun k => stronglyMeasurable_const.indicator hA
  have hbound : ∀ k, MemLp (H k) ∞ (productLaw d) :=
    fun k => (memLp_top_const (c k)).indicator ((jointNaturalFiltration d).le s A hA)
  have hx : inputValue (blockInput d T s hsT H hpast hbound) ∈ integralDomain d T :=
    (representedInput (blockInput d T s hsT H hpast hbound)).property
  rw [blockInput_class d T s hsT H hpast hbound] at hx
  have he : indicatorClass d T (Ioc (s : ℝ) (T : ℝ) ×ˢ A)
      (measurableSet_Ioc.prod ((jointNaturalFiltration d).le s A hA)) c =
      (intervalInput_memLp_two hbound T s T).toLp (intervalInput d H s T) := by
    unfold indicatorClass
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2) (s := Ioc (s : ℝ) (T : ℝ) ×ˢ A)
      (hs := measurableSet_Ioc.prod ((jointNaturalFiltration d).le s A hA)) (hμs := measure_ne_top _ _) (c := c),
      (intervalInput_memLp_two hbound T s T).coeFn_toLp] with p ha hb
    rw [ha,hb]
    apply (EuclideanSpace.equiv (Fin d) ℝ).injective
    funext k
    by_cases ht : p.1 ∈ Ioc (s : ℝ) (T : ℝ) <;> by_cases hω : p.2 ∈ A <;>
      simp [intervalInput_apply,H,ht,hω]
  rw [he]
  exact hx

/-- The actual native predictable future rectangle is trimmed by the SAME
horizon measure, and is zero when its start lies beyond T. -/
theorem future_rectangle_mem_domain (T s : ℝ≥0) (A : Set (Sample d))
    (hA : MeasurableSet[(jointNaturalFiltration d) s] A) (c : EuclideanSpace ℝ (Fin d)) :
    (indicatorClass d) T (Ioi (s : ℝ) ×ˢ A)
      (measurableSet_Ioi.prod ((jointNaturalFiltration d).le s A hA)) c ∈ (integralDomain d) T := by
  by_cases hsT : s ≤ T
  · have he : Ioi (s : ℝ) ×ˢ A =ᵐ[(inputLaw d) T] Ioc (s : ℝ) (T : ℝ) ×ˢ A := by
      filter_upwards [(time_support_ae d) T] with p hp
      apply propext
      constructor
      · intro h
        exact ⟨⟨h.1,hp.2⟩,h.2⟩
      · intro h
        exact ⟨h.1.1,h.2⟩
    rw [(indicatorClass_congr_ae d) T _ _ _
      (measurableSet_Ioc.prod ((jointNaturalFiltration d).le s A hA)) c he]
    exact (interval_rectangle_mem_domain d) T s hsT A hA c
  · have hz : (indicatorClass d) T (Ioi (s : ℝ) ×ˢ A)
        (measurableSet_Ioi.prod ((jointNaturalFiltration d).le s A hA)) c = 0 := by
      unfold indicatorClass
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (s := Ioi (s : ℝ) ×ˢ A)
        (hs := measurableSet_Ioi.prod ((jointNaturalFiltration d).le s A hA)) (hμs := measure_ne_top _ _) (c := c),
        (time_support_ae d) T,Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)] with p hc hp hz
      rw [hc,hz]
      have hTs : (T : ℝ) < (s : ℝ) := by exact_mod_cast lt_of_not_ge hsT
      have hnot : p.1 ∉ Ioi (s : ℝ) := not_lt.mpr (hp.2.trans hTs.le)
      simp [hnot]
    rw [hz]
    exact Submodule.zero_mem _

/-- The native time-zero generator pulls back to nonpositive real time.
Its class is strictly zero under actual dt|[0,T] times P, including T=0. -/
theorem zero_rectangle_class_zero (T : ℝ≥0) (A : Set (Sample d)) (hA : MeasurableSet A) (c : EuclideanSpace ℝ (Fin d)) :
    (indicatorClass d) T (Iic (0 : ℝ) ×ˢ A) (measurableSet_Iic.prod hA) c = 0 := by
  unfold indicatorClass
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (s := Iic (0 : ℝ) ×ˢ A) (hs := measurableSet_Iic.prod hA)
    (hμs := measure_ne_top _ _) (c := c),(time_support_ae d) T,Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)] with p hc hp hz
  rw [hc,hz]
  have hn : p.1 ∉ Iic (0 : ℝ) := not_le.mpr hp.1
  simp [hn]

/-- Constants are actual predictable block classes up to the strictly null
time-zero boundary, giving the univ case needed by sigma-algebra induction. -/
theorem constant_indicator_mem_domain (T : ℝ≥0) (c : EuclideanSpace ℝ (Fin d)) :
    (indicatorClass d) T univ MeasurableSet.univ c ∈ (integralDomain d) T := by
  have he : (univ : Set (ℝ × (Sample d))) =ᵐ[(inputLaw d) T] Ioi (0 : ℝ) ×ˢ (univ : Set (Sample d)) := by
    filter_upwards [(time_support_ae d) T] with p hp
    apply propext
    exact ⟨fun _ => ⟨hp.1,mem_univ p.2⟩,fun _ => mem_univ p⟩
  rw [(indicatorClass_congr_ae d) T _ _ _ (measurableSet_Ioi.prod MeasurableSet.univ) c he]
  exact (future_rectangle_mem_domain d) T 0 univ MeasurableSet.univ c

/-- Exact relation between the native predictable generator and the actual
real-time input coordinate. -/
theorem readout_preimage_future (s : ℝ≥0) (A : Set (Sample d)) :
    (timeReadout d) ⁻¹' (Ioi s ×ˢ A) = Ioi (s : ℝ) ×ˢ A := by
  ext p
  simp only [timeReadout,mem_preimage,mem_prod,mem_Ioi,nnreal_lt_toNNReal]

theorem readout_preimage_zero (A : Set (Sample d)) :
    (timeReadout d) ⁻¹' (({0} : Set ℝ≥0) ×ˢ A) = Iic (0 : ℝ) ×ˢ A := by
  ext p
  simp only [timeReadout,mem_preimage,mem_prod,mem_singleton_iff,mem_Iic,Real.toNNReal_eq_zero]

/-- The horizon-zero measure is derived zero, not bypassed by T>0. -/
theorem inputLaw_zero : (inputLaw d) 0 = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have h := (time_support_ae d) 0
  rw [ae_iff] at h
  simpa only [NNReal.coe_zero,Ioc_self,mem_empty_iff_false,not_false_eq_true,Set.ofPred_true] using h

/- The remaining sigma/Lp arguments reuse the existing scalar density proof
only at its native measure/codomain level. Every generator below uses THIS
productLaw and jointNaturalFiltration; no scalar-source integral is called. -/
private abbrev nativeGenerators : Set (Set (ℝ≥0 × (Sample d))) :=
  {S | ∃ A, MeasurableSet[(jointNaturalFiltration d) 0] A ∧ S = {0} ×ˢ A} ∪
  {S | ∃ s A, MeasurableSet[(jointNaturalFiltration d) s] A ∧ S = Ioi s ×ˢ A}

private theorem nativeGenerators_pi : IsPiSystem (nativeGenerators d) := by
  rintro S (⟨A,hA,rfl⟩ | ⟨s,A,hA,rfl⟩) U (⟨B,hB,rfl⟩ | ⟨t,B,hB,rfl⟩) hne
  · exact Or.inl ⟨A ∩ B,hA.inter hB,by ext p; simp [and_assoc,and_left_comm]⟩
  · exfalso
    obtain ⟨p,hp,hq⟩ := hne
    have hz : p.1 = 0 := hp.1
    have ht : t < 0 := hz ▸ hq.1
    exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ t from bot_le)) ht
  · exfalso
    obtain ⟨p,hp,hq⟩ := hne
    have hz : p.1 = 0 := hq.1
    have hs : s < 0 := hz ▸ hp.1
    exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ s from bot_le)) hs
  · exact Or.inr ⟨max s t,A ∩ B,
      (((jointNaturalFiltration d).mono (le_max_left s t)) _ hA).inter
        (((jointNaturalFiltration d).mono (le_max_right s t)) _ hB),
      by ext p; simp [and_assoc,and_left_comm]⟩

private theorem readout_measurable : @Measurable (ℝ × (Sample d)) (ℝ≥0 × (Sample d))
    (inferInstance : MeasurableSpace (ℝ × (Sample d))) (jointNaturalFiltration d).predictable (timeReadout d) :=
  measurable_iff_comap_le.mpr (predictableSigma_le d)

private theorem readout_set_measurable (A : Set (ℝ≥0 × (Sample d)))
    (hA : MeasurableSet[(jointNaturalFiltration d).predictable] A) : MeasurableSet ((timeReadout d) ⁻¹' A) :=
  (readout_measurable d) hA

private def finiteUnion {α : Type*} (A : ℕ → Set α) : ℕ → Set α
  | 0 => ∅
  | n+1 => finiteUnion A n ∪ A n

private theorem mem_finiteUnion {α : Type*} (A : ℕ → Set α) (n : ℕ) (a : α) :
    a ∈ finiteUnion A n ↔ ∃ k < n, a ∈ A k := by
  induction n with
  | zero => simp [finiteUnion]
  | succ n ih =>
    simp only [finiteUnion,mem_union,ih]
    constructor
    · rintro (⟨k,hk,ha⟩ | ha)
      · exact ⟨k,by omega,ha⟩
      · exact ⟨n,by omega,ha⟩
    · rintro ⟨k,hk,ha⟩
      by_cases he : k = n
      · exact Or.inr (he ▸ ha)
      · exact Or.inl ⟨k,by omega,ha⟩

private theorem finiteUnion_measurable {α : Type*} [MeasurableSpace α] (A : ℕ → Set α)
    (hA : ∀ n, MeasurableSet (A n)) : ∀ n, MeasurableSet (finiteUnion A n)
  | 0 => MeasurableSet.empty
  | n+1 => (finiteUnion_measurable A hA n).union (hA n)

private theorem indicator_empty (T : ℝ≥0) (c : EuclideanSpace ℝ (Fin d)) : (indicatorClass d) T ∅ MeasurableSet.empty c = 0 := by
  unfold indicatorClass
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (s := (∅ : Set (ℝ × (Sample d))))
    (hs := MeasurableSet.empty) (hμs := measure_ne_top _ _) (c := c),Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)] with p hp hz
  rw [hp,hz]
  simp

private theorem indicator_compl (T : ℝ≥0) (A : Set (ℝ × (Sample d))) (hA : MeasurableSet A) (c : EuclideanSpace ℝ (Fin d)) :
    (indicatorClass d) T Aᶜ hA.compl c =
      (indicatorClass d) T univ MeasurableSet.univ c-(indicatorClass d) T A hA c := by
  unfold indicatorClass
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA.compl) (hμs := measure_ne_top _ _) (c := c),
    Lp.coeFn_sub (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) c)
      (indicatorConstLp 2 hA (measure_ne_top _ _) c),
    indicatorConstLp_coeFn (p := 2) (s := (univ : Set (ℝ × (Sample d))))
      (hs := MeasurableSet.univ) (hμs := measure_ne_top _ _) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top _ _) (c := c)] with p hc hsub hu ha
  rw [hc,hsub]
  simp only [Pi.sub_apply]
  rw [hu,ha]
  by_cases hp : p ∈ A <;> simp [hp]

private theorem indicator_union_mem (T : ℝ≥0) (A : ℕ → Set (ℝ × (Sample d)))
    (hA : ∀ n, MeasurableSet (A n)) (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (c : EuclideanSpace ℝ (Fin d))
    (hmem : ∀ n, (indicatorClass d) T (A n) (hA n) c ∈ (integralDomain d) T) :
    (indicatorClass d) T (⋃ n, A n) (MeasurableSet.iUnion hA) c ∈ (integralDomain d) T := by
  classical
  have hp : ∀ n, (indicatorClass d) T (finiteUnion A n) (finiteUnion_measurable A hA n) c ∈ (integralDomain d) T := by
    intro n
    induction n with
    | zero => simpa only [finiteUnion,(indicator_empty d)] using (Submodule.zero_mem ((integralDomain d) T))
    | succ n ih =>
      have hdis : Disjoint (finiteUnion A n) (A n) := by
        apply Set.disjoint_left.mpr
        intro p hp hn
        obtain ⟨k,hkn,hpk⟩ := (mem_finiteUnion A n p).mp hp
        exact (Set.disjoint_left.mp (hd (by omega : k ≠ n))) hpk hn
      have he : (indicatorClass d) T (finiteUnion A (n+1)) (finiteUnion_measurable A hA (n+1)) c =
          (indicatorClass d) T (finiteUnion A n) (finiteUnion_measurable A hA n) c + (indicatorClass d) T (A n) (hA n) c :=
        indicatorConstLp_disjoint_union (finiteUnion_measurable A hA n) (hA n)
          (measure_ne_top _ _) (measure_ne_top _ _) hdis c
      rw [he]
      exact Submodule.add_mem _ ih (hmem n)
  have hmono : Monotone (finiteUnion A) := monotone_nat_of_le_succ (fun n => subset_union_left)
  have hsubset n : finiteUnion A n ⊆ ⋃ k, A k := by
    intro p hp
    obtain ⟨k,_,hk⟩ := (mem_finiteUnion A n p).mp hp
    exact mem_iUnion.mpr ⟨k,hk⟩
  let D n := (⋃ k, A k) \ finiteUnion A n
  have hD n : MeasurableSet (D n) := (MeasurableSet.iUnion hA).diff (finiteUnion_measurable A hA n)
  have hanti : Antitone D := fun i j hij => Set.sdiff_subset_sdiff_right (hmono hij)
  have hlim := tendsto_measure_iInter_atTop (μ := (inputLaw d) T) (fun n => (hD n).nullMeasurableSet)
    hanti ⟨0,measure_ne_top _ _⟩
  have hempty : (⋂ n, D n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hall := mem_iInter.mp hp
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hall 0).1
    exact (hall (k+1)).2 ((mem_finiteUnion A (k+1) p).mpr ⟨k,by omega,hk⟩)
  rw [hempty,measure_empty] at hlim
  have hs : Tendsto (fun n => (inputLaw d) T (finiteUnion A n ∆ (⋃ k, A k))) atTop (𝓝 0) := by
    dsimp only [Function.comp_def,D] at hlim
    simpa only [symmDiff_of_le (hsubset _)] using hlim
  have hc := tendsto_indicatorConstLp_set (p := 2) (μ := (inputLaw d) T) (hs := MeasurableSet.iUnion hA)
    (hμs := measure_ne_top _ _) (c := c) (ht := finiteUnion_measurable A hA)
    (hμt := fun _ => measure_ne_top _ _) (by norm_num) hs
  exact ((elementarySpan d) T).isClosed_topologicalClosure.mem_of_tendsto hc (Eventually.of_forall hp)

/-- Native predictable generator induction, with actual generating classes
already realized by original finite input records. -/
theorem predictable_indicator_mem_domain (T : ℝ≥0) (A : Set (ℝ × (Sample d)))
    (hA : MeasurableSet[(predictableSigma d)] A) (c : EuclideanSpace ℝ (Fin d)) :
    (indicatorClass d) T A (predictableSigma_le d A hA) c ∈ (integralDomain d) T := by
  change ∃ B, MeasurableSet[(jointNaturalFiltration d).predictable] B ∧ (timeReadout d) ⁻¹' B = A at hA
  obtain ⟨B,hB,rfl⟩ := hA
  have hall : ∀ B (hB : MeasurableSet[(jointNaturalFiltration d).predictable] B),
      (indicatorClass d) T ((timeReadout d) ⁻¹' B) ((readout_set_measurable d) B hB) c ∈ (integralDomain d) T := by
    apply MeasurableSpace.induction_on_inter (m := (jointNaturalFiltration d).predictable)
      (C := fun B hB => (indicatorClass d) T ((timeReadout d) ⁻¹' B) ((readout_set_measurable d) B hB) c ∈ (integralDomain d) T)
      (show (jointNaturalFiltration d).predictable = MeasurableSpace.generateFrom (nativeGenerators d) from rfl) (nativeGenerators_pi d)
    · simpa only [preimage_empty,(indicator_empty d)] using (Submodule.zero_mem ((integralDomain d) T))
    · rintro _ (⟨A,hA,rfl⟩ | ⟨s,A,hA,rfl⟩)
      · have hz : (indicatorClass d) T (Iic (0 : ℝ) ×ˢ A)
            (measurableSet_Iic.prod ((jointNaturalFiltration d).le 0 A hA)) c ∈ (integralDomain d) T := by
          rw [(zero_rectangle_class_zero d) T A ((jointNaturalFiltration d).le 0 A hA) c]
          exact Submodule.zero_mem _
        simpa only [(readout_preimage_zero d)] using hz
      · simpa only [(readout_preimage_future d)] using (future_rectangle_mem_domain d) T s A hA c
    · intro B hB ih
      have hc : (indicatorClass d) T ((timeReadout d) ⁻¹' B)ᶜ
          ((readout_set_measurable d) B hB).compl c ∈ (integralDomain d) T := by
        rw [(indicator_compl d) T ((timeReadout d) ⁻¹' B) ((readout_set_measurable d) B hB) c]
        exact Submodule.sub_mem ((integralDomain d) T) ((constant_indicator_mem_domain d) T c) ih
      simpa only [preimage_compl] using hc
    · intro f hd hm ih
      simpa only [preimage_iUnion] using (indicator_union_mem d) T (fun n => (timeReadout d) ⁻¹' f n)
        (fun n => (readout_set_measurable d) _ (hm n)) (fun i j hij => (hd hij).preimage (timeReadout d)) c ih
  exact hall B hB

/-- The missing reverse inclusion is PROVED using original Lp induction, not
inserted as a field or obtained by renaming the closed elementary space. -/
theorem fullPredictableL2_le_integralDomain (T : ℝ≥0) : (fullPredictableL2 d) T ≤ (integralDomain d) T := by
  intro f hf
  apply Lp.induction_stronglyMeasurable (predictableSigma_le d) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T) => f ∈ (integralDomain d) T) ?_ ?_ ?_ f
    (mem_lpMeas_iff_aestronglyMeasurable.mp hf)
  · intro c A hA hμA
    simpa only [Lp.simpleFunc.coe_indicatorConst,indicatorClass] using (predictable_indicator_mem_domain d) T A hA c
  · intro f g hf hg _ _ _ hfm hgm
    exact Submodule.add_mem _ hfm hgm
  · exact ((elementarySpan d) T).isClosed_topologicalClosure.preimage continuous_subtype_val

/-- Genuine full predictable density for the ORIGINAL actual product measure
and natural filtration, with horizon zero included. -/
theorem integralDomain_eq_fullPredictableL2 (T : ℝ≥0) : (integralDomain d) T = (fullPredictableL2 d) T :=
  le_antisymm ((integralDomain_le_fullPredictableL2 d) T) ((fullPredictableL2_le_integralDomain d) T)

/-- The proved inclusion embeds the independently defined FULL predictable
L2 space into the existing constructed integral domain without changing its class. -/
def predictableInclusion (T : ℝ≥0) : (fullPredictableL2 d) T →ₗᵢ[ℝ] (integralDomain d) T :=
  { Submodule.inclusion ((fullPredictableL2_le_integralDomain d) T) with norm_map' := fun _ => rfl }

/-- Actual native continuous LINEAR stochastic integral on the full genuine
predictable L2 space, derived from the same source and finite literal outputs. -/
def predictableIntegral (T : ℝ≥0) : (fullPredictableL2 d) T →L[ℝ] Lp ℝ 2 (productLaw d) :=
  (BrownianVectorIntegralClosure.integral d T).comp ((predictableInclusion d) T).toContinuousLinearMap

theorem predictableIntegral_norm (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    ‖(predictableIntegral d) T f‖ = ‖f‖ := by
  change ‖BrownianVectorIntegralClosure.integral d T ((predictableInclusion d) T f)‖ = ‖f‖
  rw [(integral_norm d)]
  rfl

def predictableIntegralIsometry (T : ℝ≥0) : (fullPredictableL2 d) T →ₗᵢ[ℝ] Lp ℝ 2 (productLaw d) :=
  { ((predictableIntegral d) T).toLinearMap with norm_map' := (predictableIntegral_norm d) T }

/-- The caller's original finite data is retained as an actual full
predictable L2 input, with no new output or strategy chosen for it. -/
def literalPredictableInput {T : ℝ≥0} (r : ElementaryInput d T) : (fullPredictableL2 d) T :=
  ⟨inputValue r,elementary_input_predictable r⟩

theorem predictableIntegral_returns_literal {T : ℝ≥0} (r : ElementaryInput d T) :
    (predictableIntegral d) T (literalPredictableInput d r) = outputValue r := by
  change BrownianVectorIntegralClosure.integral d T ((predictableInclusion d) T (literalPredictableInput d r)) = outputValue r
  have he : (predictableInclusion d) T (literalPredictableInput d r) = representedInput r := Subtype.ext rfl
  rw [he,integral_returns_literal]


end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableDensity
