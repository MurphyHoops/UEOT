import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableInputs

/-!
Original commitment: the actual integral source must consume the genuine full predictable L2 class.
Existing result: elementary closure lies in independently defined native predictable L2 and contains every generating rectangle.
Premise reduced: prove the reverse inclusion by native generator induction and Lp indicator convergence.
Model/witness: SAME timeLaw times sourceLaw, true natural-filtration predictable sigma, all T including zero.
Consumer: actual isometric stochastic integral on full predictable L2; general Ito/Girsanov remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableDensity
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory symmDiff
noncomputable section

private abbrev nativeGenerators : Set (Set (ℝ≥0 × (ℝ≥0 → ℝ))) :=
  {S | ∃ A, MeasurableSet[naturalFiltration 0] A ∧ S = {0} ×ˢ A} ∪
  {S | ∃ s A, MeasurableSet[naturalFiltration s] A ∧ S = Ioi s ×ˢ A}

private theorem nativeGenerators_pi : IsPiSystem nativeGenerators := by
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
      ((naturalFiltration.mono (le_max_left s t)) _ hA).inter
        ((naturalFiltration.mono (le_max_right s t)) _ hB),
      by ext p; simp [and_assoc,and_left_comm]⟩

private theorem readout_measurable : @Measurable (ℝ × (ℝ≥0 → ℝ)) (ℝ≥0 × (ℝ≥0 → ℝ))
    (inferInstance : MeasurableSpace (ℝ × (ℝ≥0 → ℝ))) naturalFiltration.predictable timeReadout :=
  measurable_iff_comap_le.mpr predictableSigma_le

private theorem readout_set_measurable (A : Set (ℝ≥0 × (ℝ≥0 → ℝ)))
    (hA : MeasurableSet[naturalFiltration.predictable] A) : MeasurableSet (timeReadout ⁻¹' A) :=
  readout_measurable hA

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

private theorem indicator_empty (T : ℝ≥0) (c : ℝ) : indicatorClass T ∅ MeasurableSet.empty c = 0 := by
  unfold indicatorClass
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (s := (∅ : Set (ℝ × (ℝ≥0 → ℝ))))
    (hs := MeasurableSet.empty) (hμs := measure_ne_top _ _) (c := c),Lp.coeFn_zero ℝ 2 (inputLaw T)] with p hp hz
  rw [hp,hz]
  simp

private theorem indicator_compl (T : ℝ≥0) (A : Set (ℝ × (ℝ≥0 → ℝ))) (hA : MeasurableSet A) (c : ℝ) :
    indicatorClass T Aᶜ hA.compl c =
      indicatorClass T univ MeasurableSet.univ c-indicatorClass T A hA c := by
  unfold indicatorClass
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA.compl) (hμs := measure_ne_top _ _) (c := c),
    Lp.coeFn_sub (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) c)
      (indicatorConstLp 2 hA (measure_ne_top _ _) c),
    indicatorConstLp_coeFn (p := 2) (s := (univ : Set (ℝ × (ℝ≥0 → ℝ))))
      (hs := MeasurableSet.univ) (hμs := measure_ne_top _ _) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top _ _) (c := c)] with p hc hsub hu ha
  rw [hc,hsub]
  simp only [Pi.sub_apply]
  rw [hu,ha]
  by_cases hp : p ∈ A <;> simp [hp]

private theorem indicator_union_mem (T : ℝ≥0) (A : ℕ → Set (ℝ × (ℝ≥0 → ℝ)))
    (hA : ∀ n, MeasurableSet (A n)) (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (c : ℝ)
    (hmem : ∀ n, indicatorClass T (A n) (hA n) c ∈ integralDomain T) :
    indicatorClass T (⋃ n, A n) (MeasurableSet.iUnion hA) c ∈ integralDomain T := by
  classical
  have hp : ∀ n, indicatorClass T (finiteUnion A n) (finiteUnion_measurable A hA n) c ∈ integralDomain T := by
    intro n
    induction n with
    | zero => simpa only [finiteUnion,indicator_empty] using (Submodule.zero_mem (integralDomain T))
    | succ n ih =>
      have hdis : Disjoint (finiteUnion A n) (A n) := by
        apply Set.disjoint_left.mpr
        intro p hp hn
        obtain ⟨k,hkn,hpk⟩ := (mem_finiteUnion A n p).mp hp
        exact (Set.disjoint_left.mp (hd (by omega : k ≠ n))) hpk hn
      have he : indicatorClass T (finiteUnion A (n+1)) (finiteUnion_measurable A hA (n+1)) c =
          indicatorClass T (finiteUnion A n) (finiteUnion_measurable A hA n) c + indicatorClass T (A n) (hA n) c :=
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
  have hlim := tendsto_measure_iInter_atTop (μ := inputLaw T) (fun n => (hD n).nullMeasurableSet)
    hanti ⟨0,measure_ne_top _ _⟩
  have hempty : (⋂ n, D n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hall := mem_iInter.mp hp
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hall 0).1
    exact (hall (k+1)).2 ((mem_finiteUnion A (k+1) p).mpr ⟨k,by omega,hk⟩)
  rw [hempty,measure_empty] at hlim
  have hs : Tendsto (fun n => inputLaw T (finiteUnion A n ∆ (⋃ k, A k))) atTop (𝓝 0) := by
    dsimp only [Function.comp_def,D] at hlim
    simpa only [symmDiff_of_le (hsubset _)] using hlim
  have hc := tendsto_indicatorConstLp_set (p := 2) (μ := inputLaw T) (hs := MeasurableSet.iUnion hA)
    (hμs := measure_ne_top _ _) (c := c) (ht := finiteUnion_measurable A hA)
    (hμt := fun _ => measure_ne_top _ _) (by norm_num) hs
  exact (elementarySpan T).isClosed_topologicalClosure.mem_of_tendsto hc (Eventually.of_forall hp)

/-- Native predictable generator induction, with actual generating classes
already realized by original finite input records. -/
theorem predictable_indicator_mem_domain (T : ℝ≥0) (A : Set (ℝ × (ℝ≥0 → ℝ)))
    (hA : MeasurableSet[predictableSigma] A) (c : ℝ) :
    indicatorClass T A (predictableSigma_le A hA) c ∈ integralDomain T := by
  change ∃ B, MeasurableSet[naturalFiltration.predictable] B ∧ timeReadout ⁻¹' B = A at hA
  obtain ⟨B,hB,rfl⟩ := hA
  have hall : ∀ B (hB : MeasurableSet[naturalFiltration.predictable] B),
      indicatorClass T (timeReadout ⁻¹' B) (readout_set_measurable B hB) c ∈ integralDomain T := by
    apply MeasurableSpace.induction_on_inter (m := naturalFiltration.predictable)
      (C := fun B hB => indicatorClass T (timeReadout ⁻¹' B) (readout_set_measurable B hB) c ∈ integralDomain T)
      (show naturalFiltration.predictable = MeasurableSpace.generateFrom nativeGenerators from rfl) nativeGenerators_pi
    · simpa only [preimage_empty,indicator_empty] using (Submodule.zero_mem (integralDomain T))
    · rintro _ (⟨A,hA,rfl⟩ | ⟨s,A,hA,rfl⟩)
      · have hz : indicatorClass T (Iic (0 : ℝ) ×ˢ A)
            (measurableSet_Iic.prod (naturalFiltration.le 0 A hA)) c ∈ integralDomain T := by
          rw [zero_rectangle_class_zero T A (naturalFiltration.le 0 A hA) c]
          exact Submodule.zero_mem _
        simpa only [readout_preimage_zero] using hz
      · simpa only [readout_preimage_future] using future_rectangle_mem_domain T s A hA c
    · intro B hB ih
      have hc : indicatorClass T (timeReadout ⁻¹' B)ᶜ
          (readout_set_measurable B hB).compl c ∈ integralDomain T := by
        rw [indicator_compl T (timeReadout ⁻¹' B) (readout_set_measurable B hB) c]
        exact Submodule.sub_mem (integralDomain T) (constant_indicator_mem_domain T c) ih
      simpa only [preimage_compl] using hc
    · intro f hd hm ih
      simpa only [preimage_iUnion] using indicator_union_mem T (fun n => timeReadout ⁻¹' f n)
        (fun n => readout_set_measurable _ (hm n)) (fun i j hij => (hd hij).preimage timeReadout) c ih
  exact hall B hB

/-- The missing reverse inclusion is PROVED using original Lp induction, not
inserted as a field or obtained by renaming the closed elementary space. -/
theorem fullPredictableL2_le_integralDomain (T : ℝ≥0) : fullPredictableL2 T ≤ integralDomain T := by
  intro f hf
  apply Lp.induction_stronglyMeasurable predictableSigma_le (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun f : Lp ℝ 2 (inputLaw T) => f ∈ integralDomain T) ?_ ?_ ?_ f
    (mem_lpMeas_iff_aestronglyMeasurable.mp hf)
  · intro c A hA hμA
    simpa only [Lp.simpleFunc.coe_indicatorConst,indicatorClass] using predictable_indicator_mem_domain T A hA c
  · intro f g hf hg _ _ _ hfm hgm
    exact Submodule.add_mem _ hfm hgm
  · exact (elementarySpan T).isClosed_topologicalClosure.preimage continuous_subtype_val

/-- Genuine full predictable density for the ORIGINAL actual product measure
and natural filtration, with horizon zero included. -/
theorem integralDomain_eq_fullPredictableL2 (T : ℝ≥0) : integralDomain T = fullPredictableL2 T :=
  le_antisymm (integralDomain_le_fullPredictableL2 T) (fullPredictableL2_le_integralDomain T)

/-- The proved inclusion embeds the independently defined FULL predictable
L2 space into the existing constructed integral domain without changing its class. -/
def predictableInclusion (T : ℝ≥0) : fullPredictableL2 T →ₗᵢ[ℝ] integralDomain T :=
  { Submodule.inclusion (fullPredictableL2_le_integralDomain T) with norm_map' := fun _ => rfl }

/-- Actual native continuous LINEAR stochastic integral on the full genuine
predictable L2 space, derived from the same source and finite literal outputs. -/
def predictableIntegral (T : ℝ≥0) : fullPredictableL2 T →L[ℝ] Lp ℝ 2 sourceLaw :=
  (BrownianIntegralClosure.integral T).comp (predictableInclusion T).toContinuousLinearMap

theorem predictableIntegral_norm (T : ℝ≥0) (f : fullPredictableL2 T) :
    ‖predictableIntegral T f‖ = ‖f‖ := by
  change ‖BrownianIntegralClosure.integral T (predictableInclusion T f)‖ = ‖f‖
  rw [integral_norm]
  rfl

def predictableIntegralIsometry (T : ℝ≥0) : fullPredictableL2 T →ₗᵢ[ℝ] Lp ℝ 2 sourceLaw :=
  { (predictableIntegral T).toLinearMap with norm_map' := predictableIntegral_norm T }

/-- The caller's original finite data is retained as an actual full
predictable L2 input, with no new output or strategy chosen for it. -/
def literalPredictableInput {T : ℝ≥0} (r : ElementaryInput T) : fullPredictableL2 T :=
  ⟨inputValue r,elementary_input_predictable r⟩

theorem predictableIntegral_returns_literal {T : ℝ≥0} (r : ElementaryInput T) :
    predictableIntegral T (literalPredictableInput r) = outputValue r := by
  change BrownianIntegralClosure.integral T (predictableInclusion T (literalPredictableInput r)) = outputValue r
  have he : predictableInclusion T (literalPredictableInput r) = representedInput r := Subtype.ext rfl
  rw [he,integral_returns_literal]

/-- The actual nonzero-noise unit input survives identification with full
predictable L2; zero horizon is included by the SAME exact energy identity. -/
theorem predictableIntegral_unit_energy (T : ℝ≥0) :
    ‖predictableIntegral T (literalPredictableInput (unitInput T))‖ ^ 2 = (T : ℝ) := by
  rw [predictableIntegral_returns_literal]
  have h := integral_unit_energy T
  rwa [integral_returns_literal] at h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableDensity
