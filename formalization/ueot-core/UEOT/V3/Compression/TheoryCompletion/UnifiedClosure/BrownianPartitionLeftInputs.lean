import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteSpanLeftInputs

/-!
Original commitment: integral QV requires correct quantifiers for actual caller partitions, not uniform-only transport.
Existing result: same-source original finite-span left traces/clipping and actual native input/time/output interfaces.
Premise reduced: construct original START-causal samples on ANY finite monotone 0/T clock and prove their actual L2 convergence from computed mesh.
Model/witness: SAME sourceLaw/inputLaw T/naturalFiltration; caller clocks may vary and repeat times, mesh is computed from them.
Consumer: arbitrary deterministic vanishing-mesh full-input QV; no output/QV certificate or regularity of original L2 input is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPartitionLeftInputs
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianFiniteSpanLeftInputs
open BrownianQuadraticVariation
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralFinitePaths BrownianContinuousAdaptedInputs
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual caller-clock record; coefficients read exactly the allowed START. -/
def sampleRecord (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0 = 0) (hend : τ (Fin.last n) = T)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hadapt : StronglyAdapted naturalFiltration H)
    (K : ℝ) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) : ElementaryInput T where
  n := n
  clock := τ
  coefficient := fun i => H (τ i.castSucc)
  clock_mono := hmono
  clock_zero := hzero
  clock_end := hend
  coefficient_past := fun i => hadapt (τ i.castSucc)
  coefficient_bounded := fun i => memLp_top_of_bound
    ((hadapt (τ i.castSucc)).mono (naturalFiltration.le _)).aestronglyMeasurable K
    (Eventually.of_forall (fun ω => hbound (τ i.castSucc) ω))

variable (T : ℝ≥0) (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
  (hmono : ∀ m, Monotone (τ m)) (hzero : ∀ m, τ m 0 = 0)
  (hend : ∀ m, τ m (Fin.last (N m)) = T)
  (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))

private theorem exists_clock_cell {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (x : ℝ)
    (hx0 : (τ 0 : ℝ) < x) (hxT : x ≤ (τ (Fin.last n) : ℝ)) :
    ∃ i : Fin n, x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) := by
  classical
  let q : Fin (n+1) → Prop := fun j => x ≤ (τ j : ℝ)
  have hex : ∃ j, q j := ⟨Fin.last n,hxT⟩
  let j := Fin.find q hex
  have hpos : 0 < (j : ℕ) := by
    by_contra hn
    have hj : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have hq : q j := Fin.find_spec hex
    change x ≤ (τ j : ℝ) at hq
    rw [hj] at hq
    exact (not_le_of_gt hx0) hq
  let i : Fin n := ⟨(j : ℕ)-1,by have := j.is_lt; omega⟩
  have his : i.succ = j := Fin.ext (by simp only [i,Fin.val_succ]; omega)
  have hij : i.castSucc < j := by
    change (i : ℕ) < (j : ℕ)
    simp only [i]
    omega
  refine ⟨i,lt_of_not_ge (Fin.find_min hex hij),?_⟩
  rw [his]
  exact Fin.find_spec hex

private theorem integrand_eq_cell {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) (i : Fin n)
    (hi : p.1 ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) :
    integrand τ H p = H i p.2 := by
  rw [integrand,Finset.sum_eq_single i]
  · simp only [intervalIntegrand,Set.indicator_of_mem hi,one_mul]
  · intro j _ hji
    have hj : p.1 ∉ Ioc (τ j.castSucc : ℝ) (τ j.succ : ℝ) := by
      intro hj
      rcases lt_or_gt_of_ne hji with h | h
      · have hc : (τ j.succ : ℝ) ≤ (τ i.castSucc : ℝ) := by
          exact_mod_cast hτ (show j.succ ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hj.2.trans hc)) hi.1
      · have hc : (τ i.succ : ℝ) ≤ (τ j.castSucc : ℝ) := by
          exact_mod_cast hτ (show i.succ ≤ j.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hi.2.trans hc)) hj.1
    simp only [intervalIntegrand,Set.indicator_of_notMem hj,zero_mul]
  · simp

include hmesh

theorem partition_integrands_tendsto_ae (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, ∀ u, ContinuousWithinAt (fun v => H v ω) (Iic u) u)
    (K : ℝ) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    ∀ᵐ p ∂inputLaw T, Tendsto (fun n => integrand (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).clock
      (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient p) atTop (𝓝 (inputFunction H p)) := by
  have hc : ∀ᵐ p ∂inputLaw T, ∀ u, ContinuousWithinAt (fun v => H v p.2) (Iic u) u :=
    Measure.quasiMeasurePreserving_snd.ae hcont
  filter_upwards [time_support_ae T,hc] with p hp hc
  have he (n : ℕ) : ∃ i : Fin (N n), p.1 ∈ Ioc (τ n i.castSucc : ℝ) (τ n i.succ : ℝ) := by
    apply exists_clock_cell
    · simpa only [hzero n,NNReal.coe_zero] using hp.1
    · simpa only [hend n] using hp.2
  choose i hi using he
  have happrox : Tendsto (fun n => τ n (i n).castSucc) atTop (𝓝 (Real.toNNReal p.1)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hp0 : 0 ≤ p.1 := hp.1.le
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => ?_) (hmesh)
    have hgap : (τ n (i n).succ : ℝ)-(τ n (i n).castSucc : ℝ) ≤
        (mesh (τ n) : ℝ) := by
      have hm := Finset.le_sup (f := fun j : Fin (N n) => τ n j.succ-τ n j.castSucc) (Finset.mem_univ (i n))
      have hco := NNReal.coe_le_coe.mpr hm
      rw [NNReal.coe_sub ((hmono n) (show (i n).castSucc ≤ (i n).succ by exact_mod_cast Nat.le_succ (i n : ℕ)))] at hco
      exact hco
    rw [NNReal.dist_eq,Real.coe_toNNReal _ hp0,abs_of_nonpos (sub_nonpos.mpr (hi n).1.le)]
    linarith [(hi n).2]
  have heq (n : ℕ) : integrand (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).clock
      (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient p = H (τ n (i n).castSucc) p.2 :=
    integrand_eq_cell _ (hmono n) _ p (i n) (hi n)
  have hwithin : Tendsto (fun n => τ n (i n).castSucc) atTop
      (𝓝[Iic (Real.toNNReal p.1)] (Real.toNNReal p.1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨happrox,Eventually.of_forall (fun n => ?_)⟩
    change τ n (i n).castSucc ≤ Real.toNNReal p.1
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hp.1.le]
    exact (hi n).1.le
  exact (tendsto_congr' (Eventually.of_forall heq)).mpr ((hc _).tendsto.comp hwithin)

theorem partition_integrands_meanSquare_tendsto (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, ∀ u, ContinuousWithinAt (fun v => H v ω) (Iic u) u)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Tendsto (fun n => ∫ p, (integrand (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).clock
      (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient p-inputFunction H p)^2 ∂inputLaw T) atTop (𝓝 0) := by
  let F (n : ℕ) := integrand (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).clock (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient
  have hFm (n : ℕ) : MemLp (F n) 2 (inputLaw T) :=
    integrand_memLp_two T _ _ (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient_bounded
  have hHm := inputFunction_memLp_two T H hjoint K hbound
  have hm (n : ℕ) : AEStronglyMeasurable (fun p => (F n p-inputFunction H p)^2) (inputLaw T) :=
    ((hFm n).aestronglyMeasurable.sub hHm.aestronglyMeasurable).pow 2
  have hb (n : ℕ) : ∀ᵐ p ∂inputLaw T, ‖(F n p-inputFunction H p)^2‖ ≤ (2*K)^2 := by
    filter_upwards [time_support_ae T] with p hp
    obtain ⟨i,hi⟩ : ∃ i : Fin (N n), p.1 ∈ Ioc (τ n i.castSucc : ℝ) (τ n i.succ : ℝ) := by
      apply exists_clock_cell
      · simpa only [hzero n,NNReal.coe_zero] using hp.1
      · simpa only [hend n] using hp.2
    have he : F n p = H (τ n i.castSucc) p.2 :=
      integrand_eq_cell _ (hmono n) _ p i hi
    have hd : ‖F n p-inputFunction H p‖ ≤ 2*K := by
      rw [he]
      have hbTarget : ‖inputFunction H p‖ ≤ K := hbound (Real.toNNReal p.1) p.2
      exact (norm_sub_le _ _).trans (by linarith [hbound (τ n i.castSucc) p.2,hbTarget])
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
  have hl : ∀ᵐ p ∂inputLaw T, Tendsto (fun n => (F n p-inputFunction H p)^2) atTop (𝓝 0) := by
    filter_upwards [partition_integrands_tendsto_ae T N τ hmono hzero hend hmesh H hadapt hcont K hbound] with p hp
    have h : Tendsto (fun n => F n p-inputFunction H p) atTop (𝓝 0) := by
      simpa only [sub_self] using hp.sub (tendsto_const_nhds (x := inputFunction H p))
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using h.pow 2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence (fun _ => (2*K)^2)
    hm (integrable_const _) hb hl

theorem partition_inputClass_tendsto (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, ∀ u, ContinuousWithinAt (fun v => H v ω) (Iic u) u)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Tendsto (fun n => inputValue (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound)) atTop
      (𝓝 (continuousInputClass T H hjoint K hbound)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (n : ℕ) : ‖inputValue (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound)-continuousInputClass T H hjoint K hbound‖^2 =
      ∫ p, (integrand (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).clock
        (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient p-inputFunction H p)^2 ∂inputLaw T := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (inputValue (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound)) (continuousInputClass T H hjoint K hbound),
      (integrand_memLp_two T _ _ (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient_bounded).coeFn_toLp,
      (inputFunction_memLp_two T H hjoint K hbound).coeFn_toLp] with p hs hr hf
    simp only [Pi.sub_apply] at hs
    rw [hs]
    change (((integrand_memLp_two T _ _ (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient_bounded).toLp
      (integrand (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).clock (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound).coefficient)) p-
      ((inputFunction_memLp_two T H hjoint K hbound).toLp (inputFunction H)) p)^2 = _
    rw [hr,hf]
  have hs : Tendsto (fun n => ‖inputValue (sampleRecord T (τ n) (hmono n) (hzero n) (hend n) H hadapt K hbound)-continuousInputClass T H hjoint K hbound‖^2)
      atTop (𝓝 0) := (tendsto_congr' (Eventually.of_forall he)).mpr
    (partition_integrands_meanSquare_tendsto T N τ hmono hzero hend hmesh H hjoint hadapt hcont K hK hbound)
  have hr := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hr


/-- Original finite span, exact original input class, actual caller records. -/
theorem finiteSpan_partition_inputClass_tendsto (a : ElementaryInput T →₀ ℝ) :
    Tendsto (fun n => inputValue (sampleRecord T (τ n) (hmono n) (hzero n) (hend n)
      (clippedTrace T a) (clippedTrace_adapted T a) (spanBound T a) (clippedTrace_bound T a))) atTop
      (𝓝 (spanInput T a : Lp ℝ 2 (inputLaw T))) := by
  rw [← clippedTrace_inputClass T a]
  exact partition_inputClass_tendsto T N τ hmono hzero hend hmesh (clippedTrace T a)
    (clippedTrace_measurable T a) (clippedTrace_adapted T a)
    (Eventually.of_forall (fun ω u => clippedTrace_left T a u ω))
    (spanBound T a) (spanBound_nonneg T a) (clippedTrace_bound T a)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPartitionLeftInputs
