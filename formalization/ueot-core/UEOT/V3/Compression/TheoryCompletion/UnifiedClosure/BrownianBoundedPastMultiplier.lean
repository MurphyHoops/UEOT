import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLeftMultiplierInputs
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSimplePastMultiplier
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
Original commitment: actual left-weighted integral increments require bounded ORIGINAL Fs coefficients, without new future permissions.
Existing result: original event-localization, native bounded multiplier convergence and actual finite simple-source partitions.
Premise reduced: construct same-bound native Fs simple approximants and actual same-input future-window coefficient classes.
Model/witness: SAME original inputLaw T/sourceLaw/naturalFiltration, s≤t≤T, bounded H strongly measurable in ORIGINAL Fs.
Consumer: actual I(1_(s,t] H*f)=H*(M_t-M_s), then actual left-weighted increment sums; no identity is assumed as a field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedPastMultiplier
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralLiteralIntervals BrownianIntegralContinuousVersion BrownianIntegralPastLocalization
open BrownianPredictableMultiplier BrownianBoundedMultiplierLimit BrownianSimplePastMultiplier
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def pastApprox (s : ℝ≥0) (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (n : ℕ) : @SimpleFunc (ℝ≥0 → ℝ) (naturalFiltration s) ℝ := by
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  exact SimpleFunc.approxOn H hp.measurable (range H ∪ {0}) 0 (by simp) n

theorem pastApprox_bound (s : ℝ≥0) (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ω, ‖H ω‖ ≤ K) (n : ℕ) (ω : ℝ≥0 → ℝ) :
    ‖pastApprox s H hp n ω‖ ≤ K := by
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  have hm := SimpleFunc.approxOn_mem hp.measurable (show (0 : ℝ) ∈ range H ∪ {0} by simp) n ω
  rcases hm with hm | hm
  · obtain ⟨x,hx⟩ := hm
    change ‖SimpleFunc.approxOn H hp.measurable (range H ∪ {0}) 0 (by simp) n ω‖ ≤ K
    rw [← hx]
    exact hb x
  · have hm : pastApprox s H hp n ω = 0 := hm
    rw [hm,norm_zero]
    exact hK

theorem pastApprox_tendsto (s : ℝ≥0) (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (ω : ℝ≥0 → ℝ) : Tendsto (fun n => pastApprox s H hp n ω) atTop (𝓝 (H ω)) := by
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  exact SimpleFunc.tendsto_approxOn hp.measurable (show (0 : ℝ) ∈ range H ∪ {0} by simp)
    (subset_closure (Or.inl (mem_range_self ω)))


theorem pastCoefficient_memLp (s : ℝ≥0) (H : (ℝ≥0 → ℝ) → ℝ)
    (hp : StronglyMeasurable[naturalFiltration s] H) (K : ℝ) (hb : ∀ ω, ‖H ω‖ ≤ K) :
    MemLp H ∞ sourceLaw :=
  memLp_top_of_bound (hp.mono (naturalFiltration.le s)).aestronglyMeasurable K (Eventually.of_forall hb)

theorem windowCoefficient_bound (s t : ℝ≥0) (H : (ℝ≥0 → ℝ) → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ω, ‖H ω‖ ≤ K) : ∀ p, ‖intervalIntegrand H s t p‖ ≤ K := by
  intro p
  by_cases h : p.1 ∈ Ioc (s : ℝ) (t : ℝ)
  · simpa only [intervalIntegrand,Set.indicator_of_mem h,one_mul] using hb p.2
  · simpa only [intervalIntegrand,Set.indicator_of_notMem h,zero_mul,norm_zero] using hK

theorem windowCoefficient_predictable (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (K : ℝ) (hb : ∀ ω, ‖H ω‖ ≤ K) :
    AEStronglyMeasurable[predictableSigma] (intervalIntegrand H s t) (inputLaw T) :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp
    (intervalInput T s t hst htT H hp (pastCoefficient_memLp s H hp K hb)).property).congr
      (intervalInput_coe T s t hst htT H hp (pastCoefficient_memLp s H hp K hb))

/-- Actual ORIGINAL future-window multiplier with ORIGINAL start s; no s
clipping silently grants H an earlier filtration permission. -/
def windowMultiplier (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ω, ‖H ω‖ ≤ K) : fullPredictableL2 T →L[ℝ] fullPredictableL2 T :=
  boundedMultiplier T (intervalIntegrand H s t) (windowCoefficient_predictable T s t hst htT H hp K hb) K
    (Eventually.of_forall (windowCoefficient_bound s t H K hK hb))

theorem windowMultiplier_coe (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ω, ‖H ω‖ ≤ K) (f : fullPredictableL2 T) :
    (windowMultiplier T s t hst htT H hp K hK hb f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      fun p => intervalIntegrand H s t p*(f : Lp ℝ 2 (inputLaw T)) p :=
  boundedMultiplier_coe T (intervalIntegrand H s t) (windowCoefficient_predictable T s t hst htT H hp K hb)
    K (Eventually.of_forall (windowCoefficient_bound s t H K hK hb)) f

theorem pastApprox_stronglyMeasurable (s : ℝ≥0) (H : (ℝ≥0 → ℝ) → ℝ)
    (hp : StronglyMeasurable[naturalFiltration s] H) (n : ℕ) :
    StronglyMeasurable[naturalFiltration s] (pastApprox s H hp n) := by
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration s
  exact SimpleFunc.stronglyMeasurable _

/-- Actual ORIGINAL bounded Fs coefficients are approximated at the same
bound K on the same window. Convergence is for the SAME original input f. -/
theorem windowMultiplier_approx_tendsto (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ω, ‖H ω‖ ≤ K) (f : fullPredictableL2 T) :
    Tendsto (fun n => windowMultiplier T s t hst htT (pastApprox s H hp n)
      (pastApprox_stronglyMeasurable s H hp n) K hK (pastApprox_bound s H hp K hK hb n) f)
      atTop (𝓝 (windowMultiplier T s t hst htT H hp K hK hb f)) := by
  apply boundedMultiplier_tendsto T
    (fun n => intervalIntegrand (pastApprox s H hp n) s t) (intervalIntegrand H s t)
    (fun n => windowCoefficient_predictable T s t hst htT (pastApprox s H hp n)
      (pastApprox_stronglyMeasurable s H hp n) K (pastApprox_bound s H hp K hK hb n))
    (windowCoefficient_predictable T s t hst htT H hp K hb) K hK
    (fun n => Eventually.of_forall (windowCoefficient_bound s t (pastApprox s H hp n) K hK
      (pastApprox_bound s H hp K hK hb n)))
    (Eventually.of_forall (windowCoefficient_bound s t H K hK hb))
  exact Eventually.of_forall (fun p =>
    (tendsto_const_nhds (x := (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => (1 : ℝ)) p.1)).mul
      (pastApprox_tendsto s H hp p.2))

/-- Native Fs simple approximation transported to the original ambient
measurable space. The SAME original Fs fiber permission is retained below. -/
def ambientPastApprox (s : ℝ≥0) (H : (ℝ≥0 → ℝ) → ℝ)
    (hp : StronglyMeasurable[naturalFiltration s] H) (n : ℕ) : SimpleFunc (ℝ≥0 → ℝ) ℝ where
  toFun := pastApprox s H hp n
  measurableSet_fiber' c := (naturalFiltration.le s) _
    (@SimpleFunc.measurableSet_fiber _ _ (naturalFiltration s) (pastApprox s H hp n) c)
  finite_range' := @SimpleFunc.finite_range _ _ (naturalFiltration s) (pastApprox s H hp n)

theorem ambientPastApprox_fiber (s : ℝ≥0) (H : (ℝ≥0 → ℝ) → ℝ)
    (hp : StronglyMeasurable[naturalFiltration s] H) (n : ℕ) (c : ℝ) :
    MeasurableSet[naturalFiltration s] (ambientPastApprox s H hp n ⁻¹' {c}) :=
  @SimpleFunc.measurableSet_fiber _ _ (naturalFiltration s) (pastApprox s H hp n) c

private theorem simpleApprox_window_identity (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ω, ‖H ω‖ ≤ K) (n : ℕ) (f : fullPredictableL2 T) :
    simplePastInput T s t (ambientPastApprox s H hp n) (ambientPastApprox_fiber s H hp n) f =
      windowMultiplier T s t hst htT (pastApprox s H hp n) (pastApprox_stronglyMeasurable s H hp n)
        K hK (pastApprox_bound s H hp K hK hb n) f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [simplePastInput_coe T s t (ambientPastApprox s H hp n) (ambientPastApprox_fiber s H hp n) f,
    boundedMultiplier_coe T (intervalIntegrand (pastApprox s H hp n) s t)
      (windowCoefficient_predictable T s t hst htT (pastApprox s H hp n)
        (pastApprox_stronglyMeasurable s H hp n) K (pastApprox_bound s H hp K hK hb n)) K
      (Eventually.of_forall (windowCoefficient_bound s t (pastApprox s H hp n) K hK (pastApprox_bound s H hp K hK hb n))) f]
    with p hs hw
  change (windowMultiplier T s t hst htT (pastApprox s H hp n) (pastApprox_stronglyMeasurable s H hp n)
    K hK (pastApprox_bound s H hp K hK hb n) f : Lp ℝ 2 (inputLaw T)) p = _ at hw
  rw [hs,hw]
  have he : p ∈ eventWindow T s t univ ↔ p.1 ∈ Ioc (s : ℝ) (t : ℝ) := by
    simp only [eventWindow,min_eq_left htT,mem_prod,mem_univ,and_true]
  by_cases h : p.1 ∈ Ioc (s : ℝ) (t : ℝ)
  · rw [Set.indicator_of_mem (he.mpr h)]
    simp only [intervalIntegrand,Set.indicator_of_mem h,one_mul]
    rfl
  · rw [Set.indicator_of_notMem (fun hp => h (he.mp hp))]
    simp only [intervalIntegrand,Set.indicator_of_notMem h,zero_mul,mul_zero]

/-- ACTUAL bounded original Fs coefficient times SAME original continuous
integral increment, proved by actual native simple approximation and source
in-measure uniqueness. No weighted-output or Ito certificate is supplied. -/
theorem windowMultiplier_integral_coe (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hp : StronglyMeasurable[naturalFiltration s] H)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ ω, ‖H ω‖ ≤ K) (f : fullPredictableL2 T) :
    (predictableIntegral T (windowMultiplier T s t hst htT H hp K hK hb f) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      fun ω => H ω*(continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω) := by
  let V (n : ℕ) := predictableIntegral T (windowMultiplier T s t hst htT (pastApprox s H hp n)
    (pastApprox_stronglyMeasurable s H hp n) K hK (pastApprox_bound s H hp K hK hb n) f)
  have hL : Tendsto V atTop (𝓝 (predictableIntegral T (windowMultiplier T s t hst htT H hp K hK hb f))) :=
    ((predictableIntegral T).continuous.tendsto _).comp (windowMultiplier_approx_tendsto T s t hst htT H hp K hK hb f)
  have hid (n : ℕ) : V n =ᵐ[sourceLaw] fun ω => pastApprox s H hp n ω*
      (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω) := by
    change predictableIntegral T (windowMultiplier T s t hst htT (pastApprox s H hp n)
      (pastApprox_stronglyMeasurable s H hp n) K hK (pastApprox_bound s H hp K hK hb n) f) =ᵐ[sourceLaw] _
    rw [← simpleApprox_window_identity T s t hst htT H hp K hK hb n f]
    exact simplePastInput_integral_coe T s t hst (ambientPastApprox s H hp n) (ambientPastApprox_fiber s H hp n) f
  have hm₁ : TendstoInMeasure sourceLaw (fun n ω => pastApprox s H hp n ω*
      (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)) atTop
      (predictableIntegral T (windowMultiplier T s t hst htT H hp K hK hb f)) :=
    TendstoInMeasure.congr hid (Eventually.of_forall (fun _ => rfl)) (tendstoInMeasure_of_tendsto_Lp hL)
  have hm₂ : TendstoInMeasure sourceLaw (fun n ω => pastApprox s H hp n ω*
      (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)) atTop
      (fun ω => H ω*(continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact ((pastApprox_stronglyMeasurable s H hp n).mono (naturalFiltration.le s)).aestronglyMeasurable.mul
        ((continuousIntegralProcess_memLp_two T t f).aestronglyMeasurable.sub
          (continuousIntegralProcess_memLp_two T s f).aestronglyMeasurable)
    · exact Eventually.of_forall (fun ω => (pastApprox_tendsto s H hp ω).mul_const _)
  exact tendstoInMeasure_ae_unique hm₁ hm₂

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedPastMultiplier
