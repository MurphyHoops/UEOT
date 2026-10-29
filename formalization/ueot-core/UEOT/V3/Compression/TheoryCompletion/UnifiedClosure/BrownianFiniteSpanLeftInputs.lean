import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousAdaptedInputs

/-!
Original commitment: full predictable-input QV needs actual bounded left-input approximants of the ORIGINAL finite source span.
Existing result: original allowed interval data/Finsupp span, native leftRecord, and source-measure L-infinity bounds.
Premise reduced: construct actual start-causal left-continuous finite-span traces and same-AE bounded clipping before left sampling.
Model/witness: SAME original sourceLaw/inputLaw T/naturalFiltration and original finite record coefficients, only AE bounded initially.
Consumer: actual uniform full-input QV density extension; no raw global bound, QV certificate or extra observation is supplied.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteSpanLeftInputs
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianQuadraticVariation
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralFinitePaths BrownianContinuousAdaptedInputs
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Original Ioc trace: at a clock boundary it retains the predictable LEFT
value. Its START permission is applied only where the row is active. -/
def rowTrace (H : (ℝ≥0 → ℝ) → ℝ) (a b u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  (Ioc a b).indicator (fun _ => H ω) u

/-- Original literal rows are left-continuous even though they need not be
continuous paths; no ramp or extra temporal regularity is assumed. -/
theorem rowTrace_left (H : (ℝ≥0 → ℝ) → ℝ) (a b u : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    ContinuousWithinAt (fun v => rowTrace H a b v ω) (Iic u) u := by
  by_cases hua : u ≤ a
  · have hz : rowTrace H a b u ω = 0 := Set.indicator_of_notMem (fun h => (not_lt_of_ge hua) h.1) _
    have he : ∀ᶠ v in 𝓝[Iic u] u, rowTrace H a b v ω = 0 := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact Set.indicator_of_notMem (fun h => (not_lt_of_ge (hv.trans hua)) h.1) _
    change Tendsto (fun v => rowTrace H a b v ω) (𝓝[Iic u] u) (𝓝 (rowTrace H a b u ω))
    rw [hz]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  · have hau : a < u := lt_of_not_ge hua
    by_cases hub : u ≤ b
    · have hu : rowTrace H a b u ω = H ω := Set.indicator_of_mem (show u ∈ Ioc a b from ⟨hau,hub⟩) _
      have he : ∀ᶠ v in 𝓝[Iic u] u, rowTrace H a b v ω = H ω := by
        filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds hau)] with v hv hva
        exact Set.indicator_of_mem (show v ∈ Ioc a b from ⟨hva,hv.trans hub⟩) _
      change Tendsto (fun v => rowTrace H a b v ω) (𝓝[Iic u] u) (𝓝 (rowTrace H a b u ω))
      rw [hu]
      exact (tendsto_congr' he).mpr tendsto_const_nhds
    · have hbu : b < u := lt_of_not_ge hub
      have hz : rowTrace H a b u ω = 0 := Set.indicator_of_notMem (fun h => (not_le_of_gt hbu) h.2) _
      have he : ∀ᶠ v in 𝓝[Iic u] u, rowTrace H a b v ω = 0 := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hbu)] with v hv
        exact Set.indicator_of_notMem (fun h => (not_le_of_gt hv) h.2) _
      change Tendsto (fun v => rowTrace H a b v ω) (𝓝[Iic u] u) (𝓝 (rowTrace H a b u ω))
      rw [hz]
      exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem rowTrace_adapted (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0)
    (hH : StronglyMeasurable[naturalFiltration a] H) : StronglyAdapted naturalFiltration (rowTrace H a b) := by
  intro u
  by_cases hu : u ∈ Ioc a b
  · have he : rowTrace H a b u = H := by ext ω; exact Set.indicator_of_mem hu _
    rw [he]
    exact hH.mono (naturalFiltration.mono hu.1.le)
  · have he : rowTrace H a b u = 0 := by ext ω; exact Set.indicator_of_notMem hu _
    rw [he]
    exact stronglyMeasurable_zero

theorem rowTrace_measurable (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hH : Measurable H) :
    Measurable (Function.uncurry (rowTrace H a b)) := by
  have he : Function.uncurry (rowTrace H a b) = (Ioc a b ×ˢ (univ : Set (ℝ≥0 → ℝ))).indicator (fun p => H p.2) := by
    ext p
    by_cases h : p.1 ∈ Ioc a b <;> simp [Function.uncurry,rowTrace,h]
  rw [he]
  exact (hH.comp measurable_snd).indicator (measurableSet_Ioc.prod MeasurableSet.univ)

theorem rowTrace_norm_le (H : (ℝ≥0 → ℝ) → ℝ) (a b u : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    ‖rowTrace H a b u ω‖ ≤ ‖H ω‖ := by
  by_cases hu : u ∈ Ioc a b <;> simp [rowTrace,hu]

/-- Original record's actual predictable LEFT trace, with no coefficient version chosen yet. -/
def recordTrace {T : ℝ≥0} (r : ElementaryInput T) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin r.n, rowTrace (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) u ω

def spanTrace (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  a.sum (fun r c => c*recordTrace r u ω)

theorem recordTrace_left {T : ℝ≥0} (r : ElementaryInput T) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    ContinuousWithinAt (fun v => recordTrace r v ω) (Iic u) u := by
  exact tendsto_finsetSum Finset.univ (fun i _ => rowTrace_left _ _ _ _ _)

theorem recordTrace_adapted {T : ℝ≥0} (r : ElementaryInput T) : StronglyAdapted naturalFiltration (recordTrace r) := by
  intro u
  have hm := Finset.stronglyMeasurable_sum Finset.univ (fun i _ => rowTrace_adapted
    (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) (r.coefficient_past i) u)
  convert hm using 1
  ext ω
  simp only [recordTrace,Finset.sum_apply]

theorem recordTrace_measurable {T : ℝ≥0} (r : ElementaryInput T) : Measurable (Function.uncurry (recordTrace r)) := by
  have hm := Finset.measurable_sum Finset.univ (fun i _ => rowTrace_measurable (r.coefficient i)
    (r.clock i.castSucc) (r.clock i.succ) ((r.coefficient_past i).mono (naturalFiltration.le _)).measurable)
  convert hm using 1
  ext p
  simp only [recordTrace,Function.uncurry]

theorem spanTrace_left (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    ContinuousWithinAt (fun v => spanTrace T a v ω) (Iic u) u := by
  classical
  exact tendsto_finsetSum a.support (fun r _ =>
    (continuousWithinAt_const.mul (recordTrace_left r u ω)))

theorem spanTrace_adapted (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) : StronglyAdapted naturalFiltration (spanTrace T a) := by
  intro u
  have hm := Finset.stronglyMeasurable_sum a.support (fun r _ => (stronglyMeasurable_const (b := a r)).mul (recordTrace_adapted r u))
  convert hm using 1
  ext ω
  simp only [spanTrace,Finsupp.sum,Finset.sum_apply,Pi.mul_apply]

theorem spanTrace_measurable (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) : Measurable (Function.uncurry (spanTrace T a)) := by
  have hm := Finset.measurable_sum a.support (fun r _ => (measurable_const (a := a r)).mul (recordTrace_measurable r))
  convert hm using 1
  ext p
  simp only [spanTrace,Finsupp.sum,Function.uncurry,Pi.mul_apply]

private theorem coeff_bound {H : (ℝ≥0 → ℝ) → ℝ} (hH : MemLp H ∞ sourceLaw) :
    ∃ C : ℝ≥0, ∀ᵐ ω ∂sourceLaw, ‖H ω‖ ≤ (C : ℝ) := by
  refine ⟨(eLpNormEssSup H sourceLaw).toNNReal, ?_⟩
  have hs : eLpNormEssSup H sourceLaw < ∞ := by simpa only [eLpNorm_exponent_top] using hH.2
  have hb : ∀ᵐ ω ∂sourceLaw, ‖H ω‖₊ ≤ (eLpNormEssSup H sourceLaw).toNNReal :=
    by
      have h := ae_le_eLpNormEssSup (f := H) (μ := sourceLaw)
      filter_upwards [h] with ω hω
      exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hs.ne, enorm_eq_nnnorm] using hω)
  exact hb.mono (fun _ h => NNReal.coe_le_coe.mpr h)

private def coeffBound {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : ℝ≥0 :=
  Classical.choose (coeff_bound (r.coefficient_bounded i))

private theorem coeffBound_ae {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    ∀ᵐ ω ∂sourceLaw, ‖r.coefficient i ω‖ ≤ (coeffBound r i : ℝ) :=
  Classical.choose_spec (coeff_bound (r.coefficient_bounded i))

/-- Actual finite deterministic bound assembled from original finite
L-infinity SOURCE-AE coefficient bounds; it is not a raw global bound. -/
def spanBound (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) : ℝ :=
  ∑ r ∈ a.support, ‖a r‖*(∑ i : Fin r.n, (coeffBound r i : ℝ))

theorem spanBound_nonneg (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) : 0 ≤ spanBound T a := by
  unfold spanBound
  positivity

theorem spanTrace_ae_bound (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    ∀ᵐ ω ∂sourceLaw, ∀ u, ‖spanTrace T a u ω‖ ≤ spanBound T a := by
  have hb : ∀ᵐ ω ∂sourceLaw, ∀ r ∈ a.support, ∀ i : Fin r.n, ‖r.coefficient i ω‖ ≤ (coeffBound r i : ℝ) :=
    (eventually_all_finset a.support).mpr (fun r _ => ae_all_iff.mpr (fun i => coeffBound_ae r i))
  filter_upwards [hb] with ω hb
  intro u
  change ‖∑ r ∈ a.support, a r * recordTrace r u ω‖ ≤ _
  apply (norm_sum_le a.support _).trans
  apply Finset.sum_le_sum
  intro r hr
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  change ‖∑ i : Fin r.n, rowTrace _ _ _ u ω‖ ≤ _
  apply (norm_sum_le Finset.univ _).trans
  exact Finset.sum_le_sum (fun i _ => (rowTrace_norm_le _ _ _ _ _).trans (hb r hr i))

private theorem rowTrace_input (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (p : ℝ × (ℝ≥0 → ℝ)) :
    inputFunction (rowTrace H a b) p = intervalIntegrand H a b p := by
  have hlow : a < Real.toNNReal p.1 ↔ (a : ℝ) < p.1 := by
    simpa only [not_le] using (Real.toNNReal_le_iff_le_coe (r := p.1) (p := a)).not
  have hhi : Real.toNNReal p.1 ≤ b ↔ p.1 ≤ (b : ℝ) := Real.toNNReal_le_iff_le_coe
  by_cases h : p.1 ∈ Ioc (a : ℝ) (b : ℝ)
  · have h' : Real.toNNReal p.1 ∈ Ioc a b := ⟨hlow.mpr h.1,hhi.mpr h.2⟩
    simp [inputFunction,rowTrace,intervalIntegrand,h,h']
  · have h' : Real.toNNReal p.1 ∉ Ioc a b := fun hh => h ⟨hlow.mp hh.1,hhi.mp hh.2⟩
    simp [inputFunction,rowTrace,intervalIntegrand,h,h']

theorem recordTrace_input {T : ℝ≥0} (r : ElementaryInput T) (p : ℝ × (ℝ≥0 → ℝ)) :
    inputFunction (recordTrace r) p = integrand r.clock r.coefficient p := by
  unfold inputFunction recordTrace integrand
  exact Finset.sum_congr rfl (fun i _ => rowTrace_input _ _ _ p)

private theorem lp_sum_coe {T : ℝ≥0} {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ 2 (inputLaw T)) :
    ⇑(∑ i ∈ s, f i) =ᵐ[inputLaw T] fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 (inputLaw T)] with p hp
    simp only [Finset.sum_empty]
    exact hp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j),ih] with p hp hq
    simp only [Pi.add_apply] at hp
    rw [hp,hq]

theorem spanInput_coe_trace (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    ⇑(spanInput T a : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T] inputFunction (spanTrace T a) := by
  have he : (spanInput T a : Lp ℝ 2 (inputLaw T)) = ∑ r ∈ a.support, a r • inputValue r := by
    simp only [spanInput,Finsupp.linearCombination_apply,Finsupp.sum,Submodule.coe_sum,Submodule.coe_smul]
    rfl
  rw [he]
  have hr : ∀ᵐ p ∂inputLaw T, ∀ r ∈ a.support, (a r • inputValue r) p = a r * inputFunction (recordTrace r) p := by
    apply (eventually_all_finset a.support).mpr
    intro r _
    filter_upwards [Lp.coeFn_smul (a r) (inputValue r),
      (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp] with p hsm hr
    simp only [Pi.smul_apply,smul_eq_mul] at hsm
    rw [hsm]
    congr 1
    exact hr.trans (recordTrace_input r p).symm
  filter_upwards [lp_sum_coe a.support (fun r => a r • inputValue r),hr] with p hp hq
  rw [hp]
  exact Finset.sum_congr rfl (fun r hr => hq r hr)

/-- Clipping reads ONLY the current original Fs past. Its common bound was
assembled from finitely many original source-AE coefficient events. -/
def clippedTrace (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  clip (spanBound T a) (spanTrace T a u ω)

private theorem clip_continuous (K : ℝ) : Continuous (clip K) :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem clip_norm_le (K : ℝ) (hK : 0 ≤ K) (x : ℝ) : ‖clip K x‖ ≤ K := by
  rw [Real.norm_eq_abs,abs_le]
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

theorem clippedTrace_bound (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    ∀ u ω, ‖clippedTrace T a u ω‖ ≤ spanBound T a :=
  fun _ _ => clip_norm_le _ (spanBound_nonneg T a) _

theorem clippedTrace_left (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    ContinuousWithinAt (fun v => clippedTrace T a v ω) (Iic u) u :=
  (clip_continuous _).continuousAt.comp_continuousWithinAt (spanTrace_left T a u ω)

theorem clippedTrace_adapted (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    StronglyAdapted naturalFiltration (clippedTrace T a) :=
  fun u => (clip_continuous _).comp_stronglyMeasurable (spanTrace_adapted T a u)

theorem clippedTrace_measurable (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    Measurable (Function.uncurry (clippedTrace T a)) :=
  (clip_continuous _).measurable.comp (spanTrace_measurable T a)

theorem clippedTrace_eq_ae (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    ∀ᵐ ω ∂sourceLaw, ∀ u, clippedTrace T a u ω = spanTrace T a u ω := by
  filter_upwards [spanTrace_ae_bound T a] with ω hω
  intro u
  have hb := abs_le.mp (show |spanTrace T a u ω| ≤ spanBound T a from hω u)
  simp only [clippedTrace,clip,min_eq_right hb.2,max_eq_right hb.1]

theorem clippedTrace_inputClass (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    continuousInputClass T (clippedTrace T a) (clippedTrace_measurable T a) (spanBound T a)
      (clippedTrace_bound T a) = (spanInput T a : Lp ℝ 2 (inputLaw T)) := by
  apply Lp.ext
  have he : ∀ᵐ p ∂inputLaw T, ∀ u, clippedTrace T a u p.2 = spanTrace T a u p.2 :=
    Measure.quasiMeasurePreserving_snd.ae (clippedTrace_eq_ae T a)
  filter_upwards [(inputFunction_memLp_two T (clippedTrace T a) (clippedTrace_measurable T a)
    (spanBound T a) (clippedTrace_bound T a)).coeFn_toLp,spanInput_coe_trace T a,
    he] with p hp hq hr
  exact hp.trans ((hr (Real.toNNReal p.1)).trans hq.symm)

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

theorem leftRegular_integrands_tendsto_ae (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, ∀ u, ContinuousWithinAt (fun v => H v ω) (Iic u) u)
    (K : ℝ) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    ∀ᵐ p ∂inputLaw T, Tendsto (fun n => integrand (leftRecord T H hadapt K hbound n).clock
      (leftRecord T H hadapt K hbound n).coefficient p) atTop (𝓝 (inputFunction H p)) := by
  have hc : ∀ᵐ p ∂inputLaw T, ∀ u, ContinuousWithinAt (fun v => H v p.2) (Iic u) u :=
    Measure.quasiMeasurePreserving_snd.ae hcont
  filter_upwards [time_support_ae T,hc] with p hp hc
  have he (n : ℕ) : ∃ i : Fin (n+1), p.1 ∈ Ioc (uniformClock T n i.castSucc : ℝ) (uniformClock T n i.succ : ℝ) := by
    apply exists_clock_cell
    · simpa only [uniformClock_zero,NNReal.coe_zero] using hp.1
    · simpa only [uniformClock_end] using hp.2
  choose i hi using he
  have happrox : Tendsto (fun n => uniformClock T n (i n).castSucc) atTop (𝓝 (Real.toNNReal p.1)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hp0 : 0 ≤ p.1 := hp.1.le
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => ?_) (uniformClock_mesh_tendsto T)
    have hgap : (uniformClock T n (i n).succ : ℝ)-(uniformClock T n (i n).castSucc : ℝ) ≤
        (mesh (uniformClock T n) : ℝ) := by
      have hm := Finset.le_sup (f := fun j : Fin (n+1) => uniformClock T n j.succ-uniformClock T n j.castSucc) (Finset.mem_univ (i n))
      have hco := NNReal.coe_le_coe.mpr hm
      rw [NNReal.coe_sub ((uniformClock_mono T n) (show (i n).castSucc ≤ (i n).succ by exact_mod_cast Nat.le_succ (i n : ℕ)))] at hco
      exact hco
    rw [NNReal.dist_eq,Real.coe_toNNReal _ hp0,abs_of_nonpos (sub_nonpos.mpr (hi n).1.le)]
    linarith [(hi n).2]
  have heq (n : ℕ) : integrand (leftRecord T H hadapt K hbound n).clock
      (leftRecord T H hadapt K hbound n).coefficient p = H (uniformClock T n (i n).castSucc) p.2 :=
    integrand_eq_cell _ (uniformClock_mono T n) _ p (i n) (hi n)
  have hwithin : Tendsto (fun n => uniformClock T n (i n).castSucc) atTop
      (𝓝[Iic (Real.toNNReal p.1)] (Real.toNNReal p.1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨happrox,Eventually.of_forall (fun n => ?_)⟩
    change uniformClock T n (i n).castSucc ≤ Real.toNNReal p.1
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hp.1.le]
    exact (hi n).1.le
  exact (tendsto_congr' (Eventually.of_forall heq)).mpr ((hc _).tendsto.comp hwithin)

theorem leftRegular_integrands_meanSquare_tendsto (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, ∀ u, ContinuousWithinAt (fun v => H v ω) (Iic u) u)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Tendsto (fun n => ∫ p, (integrand (leftRecord T H hadapt K hbound n).clock
      (leftRecord T H hadapt K hbound n).coefficient p-inputFunction H p)^2 ∂inputLaw T) atTop (𝓝 0) := by
  let F (n : ℕ) := integrand (leftRecord T H hadapt K hbound n).clock (leftRecord T H hadapt K hbound n).coefficient
  have hFm (n : ℕ) : MemLp (F n) 2 (inputLaw T) :=
    integrand_memLp_two T _ _ (leftRecord T H hadapt K hbound n).coefficient_bounded
  have hHm := inputFunction_memLp_two T H hjoint K hbound
  have hm (n : ℕ) : AEStronglyMeasurable (fun p => (F n p-inputFunction H p)^2) (inputLaw T) :=
    ((hFm n).aestronglyMeasurable.sub hHm.aestronglyMeasurable).pow 2
  have hb (n : ℕ) : ∀ᵐ p ∂inputLaw T, ‖(F n p-inputFunction H p)^2‖ ≤ (2*K)^2 := by
    filter_upwards [time_support_ae T] with p hp
    obtain ⟨i,hi⟩ : ∃ i : Fin (n+1), p.1 ∈ Ioc (uniformClock T n i.castSucc : ℝ) (uniformClock T n i.succ : ℝ) := by
      apply exists_clock_cell
      · simpa only [uniformClock_zero,NNReal.coe_zero] using hp.1
      · simpa only [uniformClock_end] using hp.2
    have he : F n p = H (uniformClock T n i.castSucc) p.2 :=
      integrand_eq_cell _ (uniformClock_mono T n) _ p i hi
    have hd : ‖F n p-inputFunction H p‖ ≤ 2*K := by
      rw [he]
      have hbTarget : ‖inputFunction H p‖ ≤ K := hbound (Real.toNNReal p.1) p.2
      exact (norm_sub_le _ _).trans (by linarith [hbound (uniformClock T n i.castSucc) p.2,hbTarget])
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
  have hl : ∀ᵐ p ∂inputLaw T, Tendsto (fun n => (F n p-inputFunction H p)^2) atTop (𝓝 0) := by
    filter_upwards [leftRegular_integrands_tendsto_ae T H hadapt hcont K hbound] with p hp
    have h : Tendsto (fun n => F n p-inputFunction H p) atTop (𝓝 0) := by
      simpa only [sub_self] using hp.sub (tendsto_const_nhds (x := inputFunction H p))
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using h.pow 2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence (fun _ => (2*K)^2)
    hm (integrable_const _) hb hl

theorem leftRegular_inputClass_tendsto (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, ∀ u, ContinuousWithinAt (fun v => H v ω) (Iic u) u)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Tendsto (fun n => inputValue (leftRecord T H hadapt K hbound n)) atTop
      (𝓝 (continuousInputClass T H hjoint K hbound)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (n : ℕ) : ‖inputValue (leftRecord T H hadapt K hbound n)-continuousInputClass T H hjoint K hbound‖^2 =
      ∫ p, (integrand (leftRecord T H hadapt K hbound n).clock
        (leftRecord T H hadapt K hbound n).coefficient p-inputFunction H p)^2 ∂inputLaw T := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (inputValue (leftRecord T H hadapt K hbound n)) (continuousInputClass T H hjoint K hbound),
      (integrand_memLp_two T _ _ (leftRecord T H hadapt K hbound n).coefficient_bounded).coeFn_toLp,
      (inputFunction_memLp_two T H hjoint K hbound).coeFn_toLp] with p hs hr hf
    simp only [Pi.sub_apply] at hs
    rw [hs]
    change (((integrand_memLp_two T _ _ (leftRecord T H hadapt K hbound n).coefficient_bounded).toLp
      (integrand (leftRecord T H hadapt K hbound n).clock (leftRecord T H hadapt K hbound n).coefficient)) p-
      ((inputFunction_memLp_two T H hjoint K hbound).toLp (inputFunction H)) p)^2 = _
    rw [hr,hf]
  have hs : Tendsto (fun n => ‖inputValue (leftRecord T H hadapt K hbound n)-continuousInputClass T H hjoint K hbound‖^2)
      atTop (𝓝 0) := (tendsto_congr' (Eventually.of_forall he)).mpr
    (leftRegular_integrands_meanSquare_tendsto T H hjoint hadapt hcont K hK hbound)
  have hr := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hr


/-- Actual original finite span is approximated by the original leftRecord on
uniform clocks; no whole-path continuity or raw global row bound is assumed. -/
theorem finiteSpan_left_inputClass_tendsto (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    Tendsto (fun n => inputValue (leftRecord T (clippedTrace T a) (clippedTrace_adapted T a)
      (spanBound T a) (clippedTrace_bound T a) n)) atTop (𝓝 (spanInput T a : Lp ℝ 2 (inputLaw T))) := by
  rw [← clippedTrace_inputClass T a]
  exact leftRegular_inputClass_tendsto T (clippedTrace T a) (clippedTrace_measurable T a)
    (clippedTrace_adapted T a) (Eventually.of_forall (fun ω u => clippedTrace_left T a u ω))
    (spanBound T a) (spanBound_nonneg T a) (clippedTrace_bound T a)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteSpanLeftInputs
