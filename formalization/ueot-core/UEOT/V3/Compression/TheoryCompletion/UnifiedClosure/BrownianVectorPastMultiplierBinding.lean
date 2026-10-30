import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableMultiplier

/-!
Original commitment: real START-weighted increments must be the integral of the SAME actual multiplied input.
Existing result: native joint-source full L2 integral, literal interval returns, same-source bounded multipliers and genuine finite density.
Premise reduced: derive I(H 1_(s,t] f)=H(M_f(t)-M_f(s)) from literal overlap and native continuity, not a supplied module identity.
Model/witness: original productLaw d/joint Fs/inputLaw d T, H strongly measurable at s and MemLp infinity on the SAME source; no L4.
Consumer: actual caller-clock START sums on original observed M_f; state-dependent weighted QV/Itô remains separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPastMultiplierBinding
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianVectorIntegralConditionalSource BrownianVectorIntegralFinitePaths BrownianVectorIntegralContinuousVersion
open BrownianVectorIntegralGridL1 BrownianVectorPredictableMultiplier
open BrownianCommonRefinement (clamp clamp_bounds)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- H is only a SAME-source L-infinity class, not globally pointwise bounded. -/
theorem scalarBlock_memLp (T s t : ℝ≥0) (H : Sample d → ℝ) (hH : MemLp H ∞ (productLaw d)) :
    MemLp (scalarBlock d s t H) ∞ (inputLaw d T) := by
  have hi := (hH.comp_snd (BrownianTimeIntegrand.timeLaw T)).indicator
    (measurableSet_Ioc.prod MeasurableSet.univ : MeasurableSet (Ioc (s : ℝ) (t : ℝ) ×ˢ (univ : Set (Sample d))))
  convert hi using 1
  · ext p
    by_cases h : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [scalarBlock,h]
  · rfl

def windowMultiplier (T s t : ℝ≥0) (H : Sample d → ℝ)
    (hp : StronglyMeasurable[jointNaturalFiltration d s] H) (hH : MemLp H ∞ (productLaw d)) :
    fullPredictableL2 d T →L[ℝ] fullPredictableL2 d T :=
  inputMultiplier d T (scalarBlock d s t H) (scalarBlock_memLp d T s t H hH)
    (scalarBlock_predictable d s t H hp).aestronglyMeasurable

theorem windowMultiplier_coe (T s t : ℝ≥0) (H : Sample d → ℝ)
    (hp : StronglyMeasurable[jointNaturalFiltration d s] H) (hH : MemLp H ∞ (productLaw d))
    (f : fullPredictableL2 d T) :
    (windowMultiplier d T s t H hp hH f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      fun p => scalarBlock d s t H p • (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p :=
  inputMultiplier_coe d T _ _ _ f

/-- Native bounded multiplication on the original source output L2. -/
def sourceMultiplier (H : Sample d → ℝ) (hH : MemLp H ∞ (productLaw d)) :
    Lp ℝ 2 (productLaw d) →L[ℝ] Lp ℝ 2 (productLaw d) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (productLaw d) ∞ 2 2 (hH.toLp H)

theorem sourceMultiplier_coe (H : Sample d → ℝ) (hH : MemLp H ∞ (productLaw d))
    (g : Lp ℝ 2 (productLaw d)) : sourceMultiplier d H hH g =ᵐ[productLaw d] fun ω => H ω*g ω := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hH.toLp H) g,hH.coeFn_toLp]
    with ω hh hH
  exact hh.trans (congrArg (fun c : ℝ => c*g ω) hH)

private theorem coefficient_mul (H : Sample d → ℝ) (K : Fin d → Sample d → ℝ) (ω : Sample d) :
    coefficient d (fun k x => H x*K k x) ω = H ω • coefficient d K ω := by ext k; rfl

private theorem window_interval_function (a b s t : ℝ≥0) (H : Sample d → ℝ)
    (K : Fin d → Sample d → ℝ) (p : ℝ × Sample d) :
    scalarBlock d s t H p • BrownianVectorTimeInput.intervalInput d K a b p =
      BrownianVectorTimeInput.intervalInput d (fun k x => H x*K k x) (max a s) (min b t) p := by
  have he : p.1 ∈ Ioc ((max a s : ℝ≥0) : ℝ) ((min b t : ℝ≥0) : ℝ) ↔
      p.1 ∈ Ioc (a : ℝ) (b : ℝ) ∧ p.1 ∈ Ioc (s : ℝ) (t : ℝ) := by
    simp only [mem_Ioc,NNReal.coe_max,NNReal.coe_min,max_lt_iff,le_min_iff]
    tauto
  by_cases hs : p.1 ∈ Ioc (s : ℝ) (t : ℝ)
  · by_cases ha : p.1 ∈ Ioc (a : ℝ) (b : ℝ)
    · simp only [scalarBlock,BrownianVectorTimeInput.intervalInput,Set.indicator_of_mem hs,Set.indicator_of_mem ha,Set.indicator_of_mem (he.mpr ⟨ha,hs⟩),one_smul,coefficient_mul]
    · have hc : p.1 ∉ Ioc ((max a s : ℝ≥0) : ℝ) ((min b t : ℝ≥0) : ℝ) := fun h => ha (he.mp h).1
      simp only [scalarBlock,BrownianVectorTimeInput.intervalInput,Set.indicator_of_mem hs,Set.indicator_of_notMem ha,Set.indicator_of_notMem hc,zero_smul,smul_zero]
  · have hc : p.1 ∉ Ioc ((max a s : ℝ≥0) : ℝ) ((min b t : ℝ≥0) : ℝ) := fun h => hs (he.mp h).2
    simp only [scalarBlock,BrownianVectorTimeInput.intervalInput,Set.indicator_of_notMem hs,Set.indicator_of_notMem hc,zero_smul]

private theorem oneStep_mul (H : Sample d → ℝ) (K : Fin d → Sample d → ℝ) (a b : ℝ≥0) (ω : Sample d) :
    oneStep d (fun k x => H x*K k x) a b ω = H ω*oneStep d K a b ω := by
  simp only [oneStep,component,Pi.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem oneStep_prefix_difference (K : Fin d → Sample d → ℝ) (a b s t : ℝ≥0) (ω : Sample d) :
    oneStep d K a (clamp a b t) ω-oneStep d K a (clamp a b s) ω =
      oneStep d K (clamp a b s) (clamp a b t) ω := by
  simp only [oneStep,component,Pi.mul_apply,coordinateIncrement,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem clamp_overlap (a b s t : ℝ≥0) (hab : a ≤ b) (_hst : s ≤ t)
    (hc : max a s ≤ min b t) : clamp a b s = max a s ∧ clamp a b t = min b t := by
  constructor
  · simp only [clamp,min_eq_right ((le_max_right a s).trans (hc.trans (min_le_left b t))) ]
  · exact max_eq_right (le_min hab ((le_max_left a s).trans (hc.trans (min_le_right b t))))

private theorem clamp_no_overlap (a b s t : ℝ≥0) (hab : a ≤ b) (hst : s ≤ t)
    (hc : min b t ≤ max a s) : clamp a b s = clamp a b t := by
  simp only [clamp,max_def,min_def] at *
  split_ifs at * <;> order

private theorem window_interval_overlap (T a b s t : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (hc : max a s ≤ min b t) (H : Sample d → ℝ)
    (hp : StronglyMeasurable[jointNaturalFiltration d s] H) (hH : MemLp H ∞ (productLaw d))
    (K : Fin d → Sample d → ℝ) (hKp : ∀ k,StronglyMeasurable[jointNaturalFiltration d a] (K k))
    (hK : ∀ k,MemLp (K k) ∞ (productLaw d)) :
    windowMultiplier d T s t H hp hH (intervalInput d T a b hab hbT K hKp hK) =
      intervalInput d T (max a s) (min b t) hc ((min_le_left b t).trans hbT) (fun k x => H x*K k x)
        (fun k => (hp.mono ((jointNaturalFiltration d).mono (le_max_right a s))).mul
          ((hKp k).mono ((jointNaturalFiltration d).mono (le_max_left a s))))
        (fun k => (hK k).mul hH) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [windowMultiplier_coe d T s t H hp hH (intervalInput d T a b hab hbT K hKp hK),
    intervalInput_coe d T a b hab hbT K hKp hK,
    intervalInput_coe d T (max a s) (min b t) hc ((min_le_left b t).trans hbT) (fun k x => H x*K k x)
      (fun k => (hp.mono ((jointNaturalFiltration d).mono (le_max_right a s))).mul
        ((hKp k).mono ((jointNaturalFiltration d).mono (le_max_left a s))))
      (fun k => (hK k).mul hH)] with p hw hi hj
  rw [hw,hi,hj]
  exact window_interval_function d a b s t H K p

private theorem interval_prefix_class (T a b u : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (K : Fin d → Sample d → ℝ) (hKp : ∀ k,StronglyMeasurable[jointNaturalFiltration d a] (K k))
    (hK : ∀ k,MemLp (K k) ∞ (productLaw d)) :
    integralAt d T u (intervalInput d T a b hab hbT K hKp hK) =
      (oneStep_memLp_two hK a (clamp a b u)).toLp (oneStep d K a (clamp a b u)) := by
  change predictableIntegral d T (truncate d T u (intervalInput d T a b hab hbT K hKp hK)) = _
  rw [truncate_intervalInput,integral_interval_literal]

private theorem interval_process_coe (T a b u : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (K : Fin d → Sample d → ℝ) (hKp : ∀ k,StronglyMeasurable[jointNaturalFiltration d a] (K k))
    (hK : ∀ k,MemLp (K k) ∞ (productLaw d)) :
    continuousIntegralProcess d T (intervalInput d T a b hab hbT K hKp hK) u =ᵐ[productLaw d]
      oneStep d K a (clamp a b u) := by
  apply (continuousIntegralProcess_eq_actual d T u _).trans
  apply (integralProcess_eq_truncated d T u _).trans
  change (integralAt d T u (intervalInput d T a b hab hbT K hKp hK) : Sample d → ℝ) =ᵐ[productLaw d] _
  rw [interval_prefix_class]
  exact (oneStep_memLp_two hK a (clamp a b u)).coeFn_toLp

private theorem window_interval_class (T a b s t : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) (hst : s ≤ t)
    (H : Sample d → ℝ) (hp : StronglyMeasurable[jointNaturalFiltration d s] H) (hH : MemLp H ∞ (productLaw d))
    (K : Fin d → Sample d → ℝ) (hKp : ∀ k,StronglyMeasurable[jointNaturalFiltration d a] (K k))
    (hK : ∀ k,MemLp (K k) ∞ (productLaw d)) :
    predictableIntegral d T (windowMultiplier d T s t H hp hH (intervalInput d T a b hab hbT K hKp hK)) =
      sourceMultiplier d H hH (incrementAt d T s t (intervalInput d T a b hab hbT K hKp hK)) := by
  let f := intervalInput d T a b hab hbT K hKp hK
  have hR : sourceMultiplier d H hH (incrementAt d T s t f) =ᵐ[productLaw d]
      fun ω => H ω*(oneStep d K a (clamp a b t) ω-oneStep d K a (clamp a b s) ω) := by
    filter_upwards [sourceMultiplier_coe d H hH (incrementAt d T s t f),incrementAt_coe d T s t f,
      interval_process_coe d T a b t hab hbT K hKp hK,interval_process_coe d T a b s hab hbT K hKp hK]
      with ω hm hi ht hs
    rw [hm,hi]
    change H ω*(continuousIntegralProcess d T (intervalInput d T a b hab hbT K hKp hK) t ω-
      continuousIntegralProcess d T (intervalInput d T a b hab hbT K hKp hK) s ω) = _
    rw [ht,hs]
  by_cases hc : max a s ≤ min b t
  · rw [window_interval_overlap d T a b s t hab hbT hc H hp hH K hKp hK,integral_interval_literal]
    apply Lp.ext
    filter_upwards [(oneStep_memLp_two (fun k => (hK k).mul hH) (max a s) (min b t)).coeFn_toLp,hR]
      with ω hl hr
    apply hl.trans
    apply Eq.trans _ hr.symm
    change oneStep d (fun k x => H x*K k x) (max a s) (min b t) ω = _
    rw [oneStep_mul,oneStep_prefix_difference,
      (clamp_overlap a b s t hab hst hc).1,(clamp_overlap a b s t hab hst hc).2]
  · have hz : windowMultiplier d T s t H hp hH f = 0 := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [windowMultiplier_coe d T s t H hp hH f,intervalInput_coe d T a b hab hbT K hKp hK,
        Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)] with p hw hi hz
      change (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p = _ at hi
      rw [hw,hi,window_interval_function]
      have hle : ((min b t : ℝ≥0) : ℝ) ≤ ((max a s : ℝ≥0) : ℝ) := by exact_mod_cast le_of_not_ge hc
      have hempty : Ioc ((max a s : ℝ≥0) : ℝ) ((min b t : ℝ≥0) : ℝ) = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x hx => not_lt_of_ge (hx.2.trans hle) hx.1)
      rw [BrownianVectorTimeInput.intervalInput,hempty,Set.indicator_empty,zero_smul]
      exact hz.symm
    change predictableIntegral d T (windowMultiplier d T s t H hp hH f) = _
    rw [hz,map_zero]
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero ℝ 2 (productLaw d),hR] with ω hz hr
    rw [hz,hr,clamp_no_overlap a b s t hab hst (le_of_not_ge hc)]
    simp only [sub_self,mul_zero,Pi.zero_apply]

private theorem literal_input_sum {T : ℝ≥0} (r : ElementaryInput d T) :
    literalPredictableInput d r = ∑ i : Fin r.n,
      intervalInput d T (r.clock i.castSucc) (r.clock i.succ)
        (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ)))
        ((r.clock_mono (Fin.le_last i.succ)).trans_eq r.clock_end)
        (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i) := by
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  apply Lp.ext
  have hi : ∀ᵐ p ∂inputLaw d T, ∀ i : Fin r.n,
      (intervalInput d T (r.clock i.castSucc) (r.clock i.succ)
        (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ)))
        ((r.clock_mono (Fin.le_last i.succ)).trans_eq r.clock_end)
        (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i) :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p =
      BrownianVectorTimeInput.intervalInput d (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p :=
    ae_all_iff.mpr (fun i => intervalInput_coe d T _ _ _ _ _ _ _)
  filter_upwards [(integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin r.n =>
      (intervalInput d T (r.clock i.castSucc) (r.clock i.succ)
        (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ)))
        ((r.clock_mono (Fin.le_last i.succ)).trans_eq r.clock_end)
        (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i) :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))),hi] with p hr hs hi
  change (literalPredictableInput d r : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p = _ at hr
  simp only [Finset.sum_apply] at hs
  exact hr.trans ((Finset.sum_congr rfl (fun i _ => (hi i).symm)).trans hs.symm)

/-- Same bounded original Fs coefficient commutes with the actual future
integral, proved on literal interval overlaps and extended by genuine density.
The coefficient is never granted access before s, including collapsed cells. -/
theorem windowMultiplier_integral_class (T s t : ℝ≥0) (hst : s ≤ t)
    (H : Sample d → ℝ) (hp : StronglyMeasurable[jointNaturalFiltration d s] H) (hH : MemLp H ∞ (productLaw d))
    (f : fullPredictableL2 d T) :
    predictableIntegral d T (windowMultiplier d T s t H hp hH f) =
      sourceMultiplier d H hH (incrementAt d T s t f) := by
  let L := (predictableIntegral d T).comp (windowMultiplier d T s t H hp hH)
  let R := (sourceMultiplier d H hH).comp (incrementAt d T s t)
  have helem (r : ElementaryInput d T) : L (literalPredictableInput d r) = R (literalPredictableInput d r) := by
    rw [literal_input_sum]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact window_interval_class d T _ _ s t _ _ hst H hp hH _ _ _
  have hspan (a : ElementaryInput d T →₀ ℝ) : L (spanInput d T a) = R (spanInput d T a) := by
    simp only [spanInput,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
    exact Finset.sum_congr rfl (fun r _ => congrArg (a r • ·) (helem r))
  have hd : DenseRange (spanInput d T) := by
    intro g
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,ha⟩ := exists_spanInput_dist_lt d T g ε hε
    exact ⟨spanInput d T a,⟨a,rfl⟩,by simpa only [dist_comm] using ha⟩
  exact congrFun (hd.equalizer L.continuous R.continuous (funext hspan)) f

theorem windowMultiplier_integral_coe (T s t : ℝ≥0) (hst : s ≤ t)
    (H : Sample d → ℝ) (hp : StronglyMeasurable[jointNaturalFiltration d s] H) (hH : MemLp H ∞ (productLaw d))
    (f : fullPredictableL2 d T) :
    (predictableIntegral d T (windowMultiplier d T s t H hp hH f) : Sample d → ℝ) =ᵐ[productLaw d]
      fun ω => H ω*(continuousIntegralProcess d T f t ω-continuousIntegralProcess d T f s ω) := by
  rw [windowMultiplier_integral_class d T s t hst]
  filter_upwards [sourceMultiplier_coe d H hH (incrementAt d T s t f),incrementAt_coe d T s t f]
    with ω hm hi
  rw [hm,hi]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPastMultiplierBinding
