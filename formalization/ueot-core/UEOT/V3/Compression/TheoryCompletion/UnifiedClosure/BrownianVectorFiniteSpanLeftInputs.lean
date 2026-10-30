import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorLiteralGridBinding
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteClockLeftApproximation

/-!
Original commitment: fixed full-input vector QV needs actual legal START approximations to the ORIGINAL dense finite inputs.
Existing result: same joint-vector full domain/grid/energy stability, actual literal error limits and necessary pure left-clock facts.
Premise reduced: construct same-source Ioc-left finite-span trace and a bounded current-past version, proving original native input equality.
Model: original productLaw/inputLaw/full jointNaturalFiltration, arbitrary original native finite combinations, d0/T0/repeats, SOURCE-AE bounds retained.
Consumer: genuine same-input caller-clock sampling then native density QV; no future coefficient access, new source or desired approximation field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorFiniteSpanLeftInputs
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralFinitePaths
open FiniteClockLeftApproximation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Original scalar coordinate trace retains the predictable LEFT value. -/
def rowTrace (H : Sample d→ℝ) (a b u : ℝ≥0) (ω : Sample d) : ℝ :=
  (Ioc a b).indicator (fun _=>H ω) u

theorem rowTrace_left (H : Sample d→ℝ) (a b u : ℝ≥0) (ω : Sample d) :
    ContinuousWithinAt (fun v=>rowTrace d H a b v ω) (Iic u) u := Ioc_indicator_left (H ω) a b u

theorem rowTrace_adapted (H : Sample d→ℝ) (a b : ℝ≥0)
    (hH : StronglyMeasurable[jointNaturalFiltration d a] H) :
    StronglyAdapted (jointNaturalFiltration d) (rowTrace d H a b) := by
  intro u
  by_cases hu : u∈Ioc a b
  · have he : rowTrace d H a b u=H := funext (fun _=>Set.indicator_of_mem hu _)
    rw [he]
    exact hH.mono ((jointNaturalFiltration d).mono hu.1.le)
  · have he : rowTrace d H a b u=0 := funext (fun _=>Set.indicator_of_notMem hu _)
    rw [he]
    exact stronglyMeasurable_zero

theorem rowTrace_measurable (H : Sample d→ℝ) (a b : ℝ≥0) (hH : Measurable H) :
    Measurable (Function.uncurry (rowTrace d H a b)) := by
  have he : Function.uncurry (rowTrace d H a b)=(Ioc a b×ˢ(univ : Set (Sample d))).indicator (H∘Prod.snd) := by
    ext p
    by_cases hp : p.1∈Ioc a b <;> simp [Function.uncurry,rowTrace,hp]
  rw [he]
  exact (hH.comp measurable_snd).indicator (measurableSet_Ioc.prod MeasurableSet.univ)

theorem rowTrace_norm_le (H : Sample d→ℝ) (a b u : ℝ≥0) (ω : Sample d) :
    ‖rowTrace d H a b u ω‖≤‖H ω‖ := by
  by_cases hu : u∈Ioc a b <;> simp [rowTrace,hu]

def recordTrace {T : ℝ≥0} (r : ElementaryInput d T) (u : ℝ≥0) (k : Fin d) (ω : Sample d) : ℝ :=
  ∑ i : Fin r.n,rowTrace d (r.coefficient i k) (r.clock i.castSucc) (r.clock i.succ) u ω

def spanTrace (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) (u : ℝ≥0) (k : Fin d) (ω : Sample d) : ℝ :=
  ∑ r∈a.support,a r*recordTrace d r u k ω

theorem recordTrace_left {T : ℝ≥0} (r : ElementaryInput d T) (k : Fin d) (u : ℝ≥0) (ω : Sample d) :
    ContinuousWithinAt (fun v=>recordTrace d r v k ω) (Iic u) u :=
  tendsto_finsetSum _ (fun _i _=>rowTrace_left d _ _ _ u ω)

theorem recordTrace_adapted {T : ℝ≥0} (r : ElementaryInput d T) (k : Fin d) :
    StronglyAdapted (jointNaturalFiltration d) (fun u ω=>recordTrace d r u k ω) := by
  intro u
  have he : (fun ω=>recordTrace d r u k ω)=∑ i : Fin r.n,rowTrace d (r.coefficient i k)
      (r.clock i.castSucc) (r.clock i.succ) u := by ext ω; simp only [recordTrace,Finset.sum_apply]
  change StronglyMeasurable[jointNaturalFiltration d u] (fun ω=>recordTrace d r u k ω)
  rw [he]
  exact Finset.stronglyMeasurable_sum _ (fun i _=>rowTrace_adapted d _ _ _ (r.coefficient_past i k) u)

theorem recordTrace_measurable {T : ℝ≥0} (r : ElementaryInput d T) (k : Fin d) :
    Measurable (Function.uncurry (fun u ω=>recordTrace d r u k ω)) := by
  change Measurable (fun p : ℝ≥0×Sample d=>∑ i : Fin r.n,
    rowTrace d (r.coefficient i k) (r.clock i.castSucc) (r.clock i.succ) p.1 p.2)
  apply Finset.measurable_sum
  intro i _
  exact rowTrace_measurable d _ _ _ ((r.coefficient_past i k).mono ((jointNaturalFiltration d).le _)).measurable

theorem spanTrace_left (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) (k : Fin d) (u : ℝ≥0) (ω : Sample d) :
    ContinuousWithinAt (fun v=>spanTrace d T a v k ω) (Iic u) u :=
  tendsto_finsetSum _ (fun r _=>continuousWithinAt_const.mul (recordTrace_left d r k u ω))

theorem spanTrace_adapted (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) (k : Fin d) :
    StronglyAdapted (jointNaturalFiltration d) (fun u ω=>spanTrace d T a u k ω) := by
  intro u
  have he : (fun ω=>spanTrace d T a u k ω)=∑ r∈a.support,a r•(fun ω=>recordTrace d r u k ω) := by
    ext ω
    simp only [spanTrace,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change StronglyMeasurable[jointNaturalFiltration d u] (fun ω=>spanTrace d T a u k ω)
  rw [he]
  exact Finset.stronglyMeasurable_sum _ (fun r _=>stronglyMeasurable_const.smul (recordTrace_adapted d r k u))

theorem spanTrace_measurable (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) (k : Fin d) :
    Measurable (Function.uncurry (fun u ω=>spanTrace d T a u k ω)) :=
  Finset.measurable_sum _ (fun r _=>measurable_const.mul (recordTrace_measurable d r k))

/-- Finite deterministic bound FROM original source essential bounds. -/
def coeffBound {T : ℝ≥0} (r : ElementaryInput d T) (i : Fin r.n) (k : Fin d) : ℝ≥0 :=
  (eLpNormEssSup (r.coefficient i k) (productLaw d)).toNNReal

theorem coeffBound_ae {T : ℝ≥0} (r : ElementaryInput d T) (i : Fin r.n) (k : Fin d) :
    ∀ᵐ ω ∂productLaw d,‖r.coefficient i k ω‖≤(coeffBound d r i k : ℝ) := by
  have hs : eLpNormEssSup (r.coefficient i k) (productLaw d)<∞ := by
    simpa only [eLpNorm_exponent_top] using (r.coefficient_bounded i k).2
  filter_upwards [ae_le_eLpNormEssSup (f:=r.coefficient i k) (μ:=productLaw d)] with ω hω
  change (‖r.coefficient i k ω‖₊ : ℝ)≤(coeffBound d r i k : ℝ)
  apply NNReal.coe_le_coe.mpr
  exact ENNReal.coe_le_coe.mp (by simpa only [coeffBound,ENNReal.coe_toNNReal hs.ne,enorm_eq_nnnorm] using hω)

def spanBound (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) : ℝ :=
  ∑ r∈a.support,‖a r‖*(∑ i : Fin r.n,∑ k : Fin d,(coeffBound d r i k : ℝ))

theorem spanBound_nonneg (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) : 0≤spanBound d T a := by
  unfold spanBound
  positivity

theorem spanTrace_ae_bound (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) :
    ∀ᵐ ω ∂productLaw d,∀ u k,‖spanTrace d T a u k ω‖≤spanBound d T a := by
  have hb : ∀ᵐ ω ∂productLaw d,∀ r∈a.support,∀ i : Fin r.n,∀ k : Fin d,
      ‖r.coefficient i k ω‖≤(coeffBound d r i k : ℝ) :=
    (eventually_all_finset a.support).mpr (fun r _=>ae_all_iff.mpr (fun i=>ae_all_iff.mpr (fun k=>coeffBound_ae d r i k)))
  filter_upwards [hb] with ω hb
  intro u k
  apply (norm_sum_le a.support _).trans
  apply Finset.sum_le_sum
  intro r hr
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le Finset.univ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (rowTrace_norm_le d _ _ _ _ _).trans
  apply (hb r hr i k).trans
  exact Finset.single_le_sum (fun j _=>NNReal.coe_nonneg _) (Finset.mem_univ k)

/-- Actual Euclidean time-input readout; this is not a sup-norm pi space. -/
def inputFunction (H : ℝ≥0→Fin d→Sample d→ℝ) (p : ℝ×Sample d) : EuclideanSpace ℝ (Fin d) :=
  coefficient d (H (Real.toNNReal p.1)) p.2

private theorem rowTrace_input (H : Sample d→ℝ) (a b : ℝ≥0) (p : ℝ×Sample d) :
    rowTrace d H a b (Real.toNNReal p.1) p.2=
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun _=>1) p.1*H p.2 := by
  by_cases hp : p.1∈Ioc (a : ℝ) (b : ℝ)
  · have ht := (toNNReal_mem_Ioc a b p.1).mpr hp
    simp [rowTrace,hp,ht]
  · have ht : Real.toNNReal p.1∉Ioc a b := fun h=>hp ((toNNReal_mem_Ioc a b p.1).mp h)
    simp [rowTrace,hp,ht]

theorem recordTrace_input {T : ℝ≥0} (r : ElementaryInput d T) (p : ℝ×Sample d) :
    inputFunction d (recordTrace d r) p=integrand d r.clock r.coefficient p := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  funext k
  simp only [inputFunction,coefficient,ContinuousLinearEquiv.apply_symm_apply,integrand,map_sum,Finset.sum_apply,
    BrownianVectorTimeInput.intervalInput,map_smul,Pi.smul_apply,smul_eq_mul,recordTrace]
  exact Finset.sum_congr rfl (fun i _=>rowTrace_input d _ _ _ p)

theorem spanInput_coe_trace (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) :
    (spanInput d T a : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      inputFunction d (spanTrace d T a) := by
  have he : (spanInput d T a : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))=
      ∑ r∈a.support,a r•inputValue r := by
    simp only [spanInput,Finsupp.linearCombination_apply,Finsupp.sum,Submodule.coe_sum,Submodule.coe_smul]
    rfl
  rw [he]
  have hr : ∀ᵐ p ∂inputLaw d T,∀ r∈a.support,(a r•inputValue r) p=
      a r•inputFunction d (recordTrace d r) p := by
    apply (eventually_all_finset a.support).mpr
    intro r _
    filter_upwards [Lp.coeFn_smul (a r) (inputValue r),
      (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp] with p hsm hr
    simp only [Pi.smul_apply] at hsm
    change inputValue r p=integrand d r.clock r.coefficient p at hr
    rw [hsm,hr,recordTrace_input]
  filter_upwards [Lp.coeFn_finsetSum a.support (fun r=>a r•inputValue r),hr] with p hp hq
  rw [hp]
  simp only [Finset.sum_apply]
  have heq : inputFunction d (spanTrace d T a) p=
      ∑ r∈a.support,a r•inputFunction d (recordTrace d r) p := by
    apply (EuclideanSpace.equiv (Fin d) ℝ).injective
    funext k
    simp only [inputFunction,coefficient,ContinuousLinearEquiv.apply_symm_apply,map_sum,map_smul,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul,spanTrace]
  rw [heq]
  exact Finset.sum_congr rfl (fun r hr=>hq r hr)

/-- Clipping is a proof approximation only: it reads just CURRENT original
joint past, and equals the original span trace on ONE source-full event. -/
def clippedTrace (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) (u : ℝ≥0) (k : Fin d) (ω : Sample d) : ℝ :=
  BrownianContinuousAdaptedInputs.clip (spanBound d T a) (spanTrace d T a u k ω)

private theorem clip_continuous (K : ℝ) : Continuous (BrownianContinuousAdaptedInputs.clip K) :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem clip_norm_le (K : ℝ) (hK : 0≤K) (x : ℝ) : ‖BrownianContinuousAdaptedInputs.clip K x‖≤K := by
  rw [Real.norm_eq_abs,abs_le]
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

theorem clippedTrace_bound (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) :
    ∀ u k ω,‖clippedTrace d T a u k ω‖≤spanBound d T a :=
  fun _ _ _=>clip_norm_le _ (spanBound_nonneg d T a) _

theorem clippedTrace_left (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) (u : ℝ≥0) (k : Fin d) (ω : Sample d) :
    ContinuousWithinAt (fun v=>clippedTrace d T a v k ω) (Iic u) u :=
  (clip_continuous _).continuousAt.comp_continuousWithinAt (spanTrace_left d T a k u ω)

theorem clippedTrace_adapted (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) (k : Fin d) :
    StronglyAdapted (jointNaturalFiltration d) (fun u ω=>clippedTrace d T a u k ω) :=
  fun u=>(clip_continuous _).comp_stronglyMeasurable (spanTrace_adapted d T a k u)

theorem clippedTrace_measurable (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) (k : Fin d) :
    Measurable (Function.uncurry (fun u ω=>clippedTrace d T a u k ω)) :=
  (clip_continuous _).measurable.comp (spanTrace_measurable d T a k)

theorem clippedTrace_eq_ae (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) :
    ∀ᵐ ω ∂productLaw d,∀ u k,clippedTrace d T a u k ω=spanTrace d T a u k ω := by
  filter_upwards [spanTrace_ae_bound d T a] with ω hω
  intro u k
  have hb := abs_le.mp (show |spanTrace d T a u k ω|≤spanBound d T a from hω u k)
  simp only [clippedTrace,BrownianContinuousAdaptedInputs.clip,min_eq_right hb.2,max_eq_right hb.1]

/-- The bounded START trace represents the EXACT original native span input;
no new input or integral is selected after its error is measured. -/
theorem spanInput_coe_clippedTrace (T : ℝ≥0) (a : ElementaryInput d T→₀ℝ) :
    (spanInput d T a : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      inputFunction d (clippedTrace d T a) := by
  have he : ∀ᵐ p ∂inputLaw d T,∀ u k,clippedTrace d T a u k p.2=spanTrace d T a u k p.2 :=
    Measure.quasiMeasurePreserving_snd.ae (clippedTrace_eq_ae d T a)
  filter_upwards [spanInput_coe_trace d T a,he] with p hp hq
  apply hp.trans
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  funext k
  simp only [inputFunction,coefficient,ContinuousLinearEquiv.apply_symm_apply]
  exact (hq (Real.toNNReal p.1) k).symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorFiniteSpanLeftInputs
