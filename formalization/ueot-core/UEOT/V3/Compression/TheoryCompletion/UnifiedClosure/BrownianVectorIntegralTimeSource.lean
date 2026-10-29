import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableDensity
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-!
Original commitment: the SAME vector-source integral must acquire a time/past consumer from actual transitions.
Existing result: true joint-predictable Euclidean L2 equals the actual elementary closure, returning SAME literal scalar projections.
Premise reduced: derive native predictable cutoff classes and actual one-step conditional prefixes under the WHOLE joint past.
Model/witness: original productLaw d, fixed original inputLaw d T, all finite d/T0/repeated endpoints; u before START uses tower.
Consumer: full-input conditional projection via finite outputs/native dense extension is next; no full-process/continuity/Itô premise.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralTimeSource
open MeasureTheory ProbabilityTheory Set
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput
open BrownianVectorIntegralClosure BrownianVectorPredictableInputs BrownianVectorPredictableDensity
open BrownianCommonRefinement (clamp)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Fixed-horizon time cutoff; there is no new horizon measure or new noise. -/
def timeSet (T s : ℝ≥0) : Set (ℝ × (Sample d)) := Ioc (0 : ℝ) (min s T : ℝ≥0) ×ˢ univ

theorem timeSet_predictable (T s : ℝ≥0) : MeasurableSet[(predictableSigma d)] ((timeSet d) T s) :=
  (predictable_interval_rectangle d) 0 (min s T) MeasurableSet.univ

theorem timeSet_measurable (T s : ℝ≥0) : MeasurableSet ((timeSet d) T s) :=
  (predictableSigma_le d) _ ((timeSet_predictable d) T s)

private def cutoffClass (T s : ℝ≥0) : Lp ℝ ∞ ((inputLaw d) T) :=
  ((memLp_top_const (μ := (inputLaw d) T) (1 : ℝ)).indicator ((timeSet_measurable d) T s)).toLp
    (((timeSet d) T s).indicator (fun _ => (1 : ℝ)))

/-- Native Holder multiplication by the actual L-infinity indicator. -/
def truncateAmbient (T s : ℝ≥0) : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T) →L[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T) :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin d))).holderL ((inputLaw d) T) ∞ 2 2 ((cutoffClass d) T s)

theorem truncateAmbient_coe (T s : ℝ≥0) (f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) :
    (truncateAmbient d) T s f =ᵐ[(inputLaw d) T] ((timeSet d) T s).indicator f := by
  have hc := ((memLp_top_const (μ := (inputLaw d) T) (1 : ℝ)).indicator ((timeSet_measurable d) T s)).coeFn_toLp
  have hh := (ContinuousLinearMap.lsmul ℝ ℝ (E := EuclideanSpace ℝ (Fin d))).coeFn_holder (r := 2) ((cutoffClass d) T s) f
  apply hh.trans
  filter_upwards [hc] with p hp
  change (cutoffClass d) T s p • f p = ((timeSet d) T s).indicator f p
  change (cutoffClass d) T s p = _ at hp
  rw [hp]
  by_cases ht : p ∈ (timeSet d) T s <;> simp [ht]

theorem truncateAmbient_predictable (T s : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (truncateAmbient d) T s f ∈ (fullPredictableL2 d) T := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hf : AEStronglyMeasurable[(predictableSigma d)] (f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) ((inputLaw d) T) :=
    mem_lpMeas_iff_aestronglyMeasurable.mp f.property
  refine ⟨((timeSet d) T s).indicator (hf.mk (f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T))),
    hf.stronglyMeasurable_mk.indicator ((timeSet_predictable d) T s),?_⟩
  filter_upwards [(truncateAmbient_coe d) T s f,hf.ae_eq_mk] with p hp hfp
  rw [hp]
  by_cases ht : p ∈ (timeSet d) T s <;> simp [ht,hfp]

/-- Actual cutoff operator on the independently defined full predictable L2. -/
def truncate (T s : ℝ≥0) : (fullPredictableL2 d) T →L[ℝ] (fullPredictableL2 d) T :=
  (((truncateAmbient d) T s).comp ((fullPredictableL2 d) T).subtypeL).codRestrict
    ((fullPredictableL2 d) T) ((truncateAmbient_predictable d) T s)

theorem truncate_coe (T s : ℝ≥0) (f : (fullPredictableL2 d) T) :
    ((truncate d) T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) =ᵐ[(inputLaw d) T] ((timeSet d) T s).indicator (f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) :=
  (truncateAmbient_coe d) T s f

/-- The actual cutoff is a contraction in the original product-measure L2. -/
theorem truncate_norm_le (T s : ℝ≥0) (f : (fullPredictableL2 d) T) : ‖(truncate d) T s f‖ ≤ ‖f‖ := by
  change ‖((truncate d) T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T))‖ ≤ ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T))‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(truncate_coe d) T s f] with p hp
  rw [hp]
  by_cases ht : p ∈ (timeSet d) T s <;> simp [ht]

theorem truncate_zero (T : ℝ≥0) (f : (fullPredictableL2 d) T) : (truncate d) T 0 f = 0 := by
  apply Subtype.ext
  change ((truncate d) T 0 f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) = 0
  apply Lp.ext
  filter_upwards [(truncate_coe d) T 0 f,Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)] with p hp hz
  rw [hp,hz]
  simp [timeSet]

theorem truncate_horizon (T : ℝ≥0) (f : (fullPredictableL2 d) T) : (truncate d) T T f = f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(truncate_coe d) T T f,(time_support_ae d) T] with p hp ht
  rw [hp]
  exact Set.indicator_of_mem (by simpa only [timeSet,min_self,mem_prod,mem_univ,and_true] using ht) _

/-- Actual time-indexed integral CLASS, defined by the existing full integral
of the literal cutoff input. Exact adapted representatives are a later bridge. -/
def integralClassProcess (T : ℝ≥0) (f : (fullPredictableL2 d) T) (s : ℝ≥0) : Lp ℝ 2 (productLaw d) :=
  (predictableIntegral d) T ((truncate d) T s f)

theorem integralClassProcess_zero (T : ℝ≥0) (f : (fullPredictableL2 d) T) : (integralClassProcess d) T f 0 = 0 := by
  rw [integralClassProcess,(truncate_zero d),map_zero]

theorem integralClassProcess_horizon (T : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (integralClassProcess d) T f T = (predictableIntegral d) T f := by
  rw [integralClassProcess,(truncate_horizon d)]

theorem integralClassProcess_norm_le (T s : ℝ≥0) (f : (fullPredictableL2 d) T) :
    ‖(integralClassProcess d) T f s‖ ≤ ‖f‖ := by
  rw [integralClassProcess,(predictableIntegral_norm d)]
  exact (truncate_norm_le d) T s f

private theorem lp_norm_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (μ : Measure α) (f : Lp E 2 μ) :
    ‖f‖^2 = ∫ a, ‖f a‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- SAME scalar output second energy is the actual cutoff Euclidean input
energy under the ORIGINAL fixed, unnormalized time-times-product-source law. -/
theorem integralClassProcess_energy (T u : ℝ≥0) (f : fullPredictableL2 d T) :
    (∫ ω, integralClassProcess d T f u ω ^ 2 ∂productLaw d) =
      ∫ p in timeSet d T u, ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖^2 ∂inputLaw d T := by
  have hs := lp_norm_sq (productLaw d) (integralClassProcess d T f u)
  simp only [Real.norm_eq_abs,sq_abs] at hs
  rw [← hs,integralClassProcess,predictableIntegral_norm]
  change ‖(truncate d T u f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))‖^2 = _
  rw [lp_norm_sq]
  have he : (fun p => ‖(truncate d T u f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖^2)
      =ᵐ[inputLaw d T] (timeSet d T u).indicator
        (fun p => ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖^2) := by
    filter_upwards [truncate_coe d T u f] with p hp
    rw [hp]
    by_cases ht : p ∈ timeSet d T u <;> simp [ht]
  rw [integral_congr_ae he,integral_indicator (timeSet_measurable d T u)]

/-- Each time evaluation is itself the ACTUAL native continuous linear map,
feeding the conditional-expectation/dense-extension bridge. -/
def integralAt (T s : ℝ≥0) : (fullPredictableL2 d) T →L[ℝ] Lp ℝ 2 (productLaw d) :=
  ((predictableIntegral d) T).comp ((truncate d) T s)

theorem integralAt_apply (T s : ℝ≥0) (f : (fullPredictableL2 d) T) :
    (integralAt d) T s f = (integralClassProcess d) T f s := rfl

theorem integralAt_norm_le_one (T s : ℝ≥0) : ‖(integralAt d) T s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [one_mul]
  exact (integralClassProcess_norm_le d) T s f

/-- Observation before a step uses the TOWER through its own start sigma;
its future coefficient is never pulled directly out of an earlier conditional expectation. -/
theorem oneStep_condExp_prefix {H : Fin d → Sample d → ℝ} (a b u : ℝ≥0) (hab : a ≤ b)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k)) (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (productLaw d)[oneStep d H a b | (jointNaturalFiltration d) u] =ᵐ[(productLaw d)] oneStep d H a (clamp a b u) := by
  by_cases hua : u ≤ a
  · have htower := condExp_condExp_of_le (μ := (productLaw d)) (f := oneStep d H a b)
      ((jointNaturalFiltration d).mono hua) ((jointNaturalFiltration d).le a)
    have hc : (productLaw d)[(productLaw d)[oneStep d H a b | (jointNaturalFiltration d) a] | (jointNaturalFiltration d) u] =ᵐ[(productLaw d)]
        (productLaw d)[(0 : (Sample d) → ℝ) | (jointNaturalFiltration d) u] :=
      condExp_congr_ae (oneStep_condExp_zero a b hab hHpast hH)
    rw [condExp_zero] at hc
    have hz := htower.symm.trans hc
    have he : clamp a b u = a := by simp only [clamp,min_eq_right (hua.trans hab),max_eq_left hua]
    filter_upwards [hz] with ω hω
    rw [hω]
    simp [oneStep,component,coordinateIncrement,he]
  · have hau : a ≤ u := (lt_of_not_ge hua).le
    by_cases hbu : b ≤ u
    · have hm := (oneStep_stronglyMeasurable_end a b hab hHpast).mono ((jointNaturalFiltration d).mono hbu)
      have he : clamp a b u = b := by simp only [clamp,min_eq_left hbu,max_eq_right hab]
      rw [he,condExp_of_stronglyMeasurable ((jointNaturalFiltration d).le u) hm ((oneStep_memLp_two hH a b).integrable (by norm_num))]
    · have hub : u ≤ b := (lt_of_not_ge hbu).le
      have he : oneStep d H a b = oneStep d H a u+oneStep d H u b := by
        funext ω
        simp only [oneStep,Pi.add_apply,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        simp only [component,Pi.mul_apply,coordinateIncrement]
        ring
      have hp := condExp_of_stronglyMeasurable ((jointNaturalFiltration d).le u)
        (oneStep_stronglyMeasurable_end a u hau hHpast) ((oneStep_memLp_two hH a u).integrable (by norm_num))
      have hf := oneStep_condExp_zero u b hub (fun k => (hHpast k).mono ((jointNaturalFiltration d).mono hau)) hH
      have ha := condExp_add ((oneStep_memLp_two hH a u).integrable (by norm_num)) ((oneStep_memLp_two hH u b).integrable (by norm_num)) ((jointNaturalFiltration d) u)
      rw [he]
      apply ha.trans
      rw [hp]
      have hc : clamp a b u = u := by simp only [clamp,min_eq_right hub,max_eq_right hau]
      filter_upwards [hf] with ω hω
      simp only [Pi.add_apply,hω,add_zero,hc]

/-- Native L2 natural conditional projection on the ORIGINAL source law. -/
def naturalProjection (u : ℝ≥0) : Lp ℝ 2 (productLaw d) →L[ℝ] Lp ℝ 2 (productLaw d) :=
  (lpMeas ℝ ℝ ((jointNaturalFiltration d) u) 2 (productLaw d)).subtypeL.comp
    (condExpL2 ℝ ℝ ((jointNaturalFiltration d).le u))

/-- The proved conditional prefix identity, now in the original native source
L2 space, is the exact continuous interface used by the general integral. -/
theorem oneStep_projection_prefix {H : Fin d → Sample d → ℝ} (a b u : ℝ≥0) (hab : a ≤ b)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k)) (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    (naturalProjection d) u ((oneStep_memLp_two hH a b).toLp (oneStep d H a b)) =
      (oneStep_memLp_two hH a (clamp a b u)).toLp (oneStep d H a (clamp a b u)) := by
  apply Lp.ext
  exact ((oneStep_memLp_two hH a b).condExpL2_ae_eq_condExp (𝕜 := ℝ) ((jointNaturalFiltration d).le u)).trans
    (((oneStep_condExp_prefix d) a b u hab hHpast hH).trans (oneStep_memLp_two hH a (clamp a b u)).coeFn_toLp.symm)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralTimeSource
