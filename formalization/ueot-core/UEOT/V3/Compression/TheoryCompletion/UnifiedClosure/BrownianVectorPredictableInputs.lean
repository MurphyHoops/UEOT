import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralClosure
import Mathlib.Probability.Process.Predictable

/-!
Original commitment: the actual vector-noise integral domain must be compared with genuine predictable Euclidean L2.
Existing result: SAME product-source scalar projection extends isometrically on actual native Euclidean elementary closure.
Premise reduced: define true joint-filtration predictable lpMeas independently and derive literal block/elementary inclusion.
Model/witness: original real timeLaw times productLaw d, SAME whole-joint natural filtration, including d0/T0/time-zero nullity.
Consumer: generating-vector-indicator realization and native reverse density remain subsequent proofs, not assumed fields.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableInputs
open MeasureTheory ProbabilityTheory Set
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput BrownianVectorIntegralClosure
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Read the SAME actual real-time/product-source coordinate. -/
def timeReadout (d : ℕ) (p : ℝ × Sample d) : ℝ≥0 × Sample d := (Real.toNNReal p.1,p.2)

private theorem native_predictable_le (d : ℕ) : (jointNaturalFiltration d).predictable ≤
    (inferInstance : MeasurableSpace (ℝ≥0 × Sample d)) := by
  apply MeasurableSpace.generateFrom_le
  rintro _ (⟨A,hA,rfl⟩ | ⟨s,A,hA,rfl⟩)
  · exact (measurableSet_singleton _).prod ((jointNaturalFiltration d).le 0 A hA)
  · exact measurableSet_Ioi.prod ((jointNaturalFiltration d).le s A hA)

@[instance_reducible] def predictableSigma (d : ℕ) : MeasurableSpace (ℝ × Sample d) :=
  MeasurableSpace.comap (timeReadout d) (jointNaturalFiltration d).predictable

theorem predictableSigma_le (d : ℕ) : predictableSigma d ≤
    (inferInstance : MeasurableSpace (ℝ × Sample d)) := by
  have hm : Measurable (timeReadout d) := (measurable_fst.real_toNNReal).prodMk measurable_snd
  exact (hm.mono le_rfl (native_predictable_le d)).comap_le

/-- Native vector-valued predictable L2, independently of the elementary closure. -/
def fullPredictableL2 (d : ℕ) (T : ℝ≥0) : Submodule ℝ (Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) :=
  lpMeas (EuclideanSpace ℝ (Fin d)) ℝ (predictableSigma d) 2 (inputLaw d T)

theorem fullPredictableL2_closed (d : ℕ) (T : ℝ≥0) :
    IsClosed (fullPredictableL2 d T : Set (Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))) :=
  isClosed_aestronglyMeasurable (predictableSigma_le d)

private theorem nnreal_lt_toNNReal (s : ℝ≥0) (x : ℝ) : s < Real.toNNReal x ↔ (s : ℝ) < x := by
  simpa only [not_le] using (Real.toNNReal_le_iff_le_coe (r := x) (p := s)).not

theorem predictable_interval_rectangle (d : ℕ) (s t : ℝ≥0) {A : Set (Sample d)}
    (hA : MeasurableSet[jointNaturalFiltration d s] A) :
    MeasurableSet[predictableSigma d] (Ioc (s : ℝ) (t : ℝ) ×ˢ A) := by
  have hm : @Measurable (ℝ × Sample d) (ℝ≥0 × Sample d)
      (predictableSigma d) (jointNaturalFiltration d).predictable (timeReadout d) :=
    measurable_iff_comap_le.mpr le_rfl
  have h := (measurableSet_predictable_Ioc_prod s t hA).preimage hm
  convert h using 1
  ext p
  simp only [timeReadout,mem_preimage,mem_prod,mem_Ioc,nnreal_lt_toNNReal,Real.toNNReal_le_iff_le_coe]

/-- Each coordinate may read ALL coordinates' actual Fs past. Native
Euclidean measurability is reconstructed from those legitimate coordinates. -/
theorem intervalInput_predictable {d : ℕ} {H : Fin d → Sample d → ℝ} (s t : ℝ≥0)
    (hH : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k)) :
    StronglyMeasurable[predictableSigma d] (intervalInput d H s t) := by
  have hm : @Measurable (Sample d) (EuclideanSpace ℝ (Fin d))
      (jointNaturalFiltration d s) inferInstance (coefficient d H) := by
    let : MeasurableSpace (Sample d) := jointNaturalFiltration d s
    exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp
      (measurable_pi_lambda _ (fun k => (hH k).measurable))
  apply Measurable.stronglyMeasurable
  intro B hB
  have hrect := predictable_interval_rectangle d s t (hm hB)
  have hwhole := predictable_interval_rectangle d s t
    (MeasurableSet.univ : MeasurableSet[jointNaturalFiltration d s] (univ : Set (Sample d)))
  by_cases h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ B
  · have he : intervalInput d H s t ⁻¹' B =
        (Ioc (s : ℝ) (t : ℝ) ×ˢ (coefficient d H ⁻¹' B)) ∪
          (Ioc (s : ℝ) (t : ℝ) ×ˢ (univ : Set (Sample d)))ᶜ := by
      ext p
      by_cases hp : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [intervalInput,hp,h0]
    rw [he]
    exact hrect.union hwhole.compl
  · have he : intervalInput d H s t ⁻¹' B = Ioc (s : ℝ) (t : ℝ) ×ˢ (coefficient d H ⁻¹' B) := by
      ext p
      by_cases hp : p.1 ∈ Ioc (s : ℝ) (t : ℝ) <;> simp [intervalInput,hp,h0]
    rw [he]
    exact hrect

theorem elementary_input_predictable {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) :
    inputValue r ∈ fullPredictableL2 d T := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  have hm : StronglyMeasurable[predictableSigma d] (integrand d r.clock r.coefficient) := by
    have h : StronglyMeasurable[predictableSigma d]
        (∑ i : Fin r.n, intervalInput d (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)) :=
      Finset.stronglyMeasurable_sum Finset.univ (fun i _ =>
        intervalInput_predictable (r.clock i.castSucc) (r.clock i.succ) (r.coefficient_past i))
    convert h using 1
    ext p
    simp only [integrand,Finset.sum_apply]
  exact hm.aestronglyMeasurable.congr
    (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp.symm

/-- This direction is derived before proving any density, and its RHS is
fixed independently by native joint-predictable lpMeas. -/
theorem integralDomain_le_fullPredictableL2 (d : ℕ) (T : ℝ≥0) :
    integralDomain d T ≤ fullPredictableL2 d T := by
  apply (elementarySpan d T).topologicalClosure_minimal _ (fullPredictableL2_closed d T)
  rw [elementarySpan_eq_span]
  exact Submodule.span_le.mpr (by rintro _ ⟨r,rfl⟩; exact elementary_input_predictable r)

/-- Literal vector coefficient block after the same allowed START time. -/
def blockInput (d : ℕ) (T s : ℝ≥0) (hsT : s ≤ T) (H : Fin d → Sample d → ℝ)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) : ElementaryInput d T where
  n := 2
  clock := ![0,s,T]
  coefficient := ![fun _ _ => 0,H]
  clock_mono := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := by intro i k; fin_cases i; exact stronglyMeasurable_const; exact hHpast k
  coefficient_bounded := by intro i k; fin_cases i; exact MemLp.zero; exact hH k

theorem blockInput_class (d : ℕ) (T s : ℝ≥0) (hsT : s ≤ T) (H : Fin d → Sample d → ℝ)
    (hHpast : ∀ k, StronglyMeasurable[jointNaturalFiltration d s] (H k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) :
    inputValue (blockInput d T s hsT H hHpast hH) =
      (intervalInput_memLp_two hH T s T).toLp (intervalInput d H s T) := by
  apply Lp.ext
  apply (integrand_memLp_two T _ _ (blockInput d T s hsT H hHpast hH).coefficient_bounded).coeFn_toLp.trans
  apply Filter.EventuallyEq.trans _ (intervalInput_memLp_two hH T s T).coeFn_toLp.symm
  apply Filter.Eventually.of_forall
  intro p
  change (∑ i : Fin 2, intervalInput d (![fun _ _ => 0,H] i) (![0,s,T] i.castSucc) (![0,s,T] i.succ) p) = _
  rw [Fin.sum_univ_two]
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  funext k
  change intervalInput d (fun _ _ => 0) 0 s p k+intervalInput d H s T p k = intervalInput d H s T p k
  simp only [intervalInput_apply,mul_zero,zero_add]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableInputs
