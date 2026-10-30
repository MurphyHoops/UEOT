import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralEnergyL1
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariationSteps

/-!
Original commitment: SAME finite-vector actual partition energy must derive its Gaussian quadratic errors under the whole joint past.
Existing result: actual product coordinates/increments/whole-joint independence and original full-input grid/energy L1 stability.
Premise reduced: derive actual coordinate-product error L2 moments/conditional moments and permitted weighted orthogonality from the source.
Model: unchanged productLaw d/jointNaturalFiltration, deterministic s<=t, arbitrary joint-START-measurable bounded scalar weights, including repeated times/d0.
Consumer: literal vector-table mesh error and SAME-input QV; no conditional variance/QV certificate, state Ito or SDE is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorQuadraticVariationSteps
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Native Gaussian law belongs to actual SAME product-source coordinate. -/
theorem coordinateIncrement_memLp_four (i : Fin d) (s t : ℝ≥0) :
    MemLp (coordinateIncrement d i s t) 4 (productLaw d) :=
  ((coordinate_preBrownian d i).hasLaw_sub t s).hasGaussianLaw.memLp (by norm_num)

/-- Actual diagonal/cross quadratic increment error. The clock term comes
from the already DERIVED coordinate covariance, not an input field. -/
def productError (i j : Fin d) (s t : ℝ≥0) (ω : Sample d) : ℝ :=
  coordinateIncrement d i s t ω*coordinateIncrement d j s t ω-
    (if i=j then (t : ℝ)-(s : ℝ) else 0)

theorem productError_memLp_two (i j : Fin d) (s t : ℝ≥0) :
    MemLp (productError d i j s t) 2 (productLaw d) := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  have hp : MemLp (fun ω=>coordinateIncrement d i s t ω*coordinateIncrement d j s t ω) 2 (productLaw d) :=
    (coordinateIncrement_memLp_four d j s t).mul (coordinateIncrement_memLp_four d i s t)
  exact hp.sub (memLp_const (if i=j then (t : ℝ)-(s : ℝ) else 0))

theorem productError_condExp_zero (i j : Fin d) (s t : ℝ≥0) (hst : s≤t) :
    (productLaw d)[productError d i j s t | jointNaturalFiltration d s]
      =ᵐ[productLaw d] fun _=>0 := by
  apply (condExp_sub (coordinateIncrement_product_integrable d i j s t)
    (integrable_const (if i=j then (t : ℝ)-(s : ℝ) else 0)) (jointNaturalFiltration d s)).trans
  rw [condExp_const ((jointNaturalFiltration d).le s)]
  filter_upwards [coordinateIncrement_condExp_product d i j s t hst] with ω hω
  simp only [Pi.sub_apply,hω,sub_self]

/-- Exact error variance is derived from actual Gaussian fourth moment and
native cross-coordinate product independence. No L4 condition on a full input. -/
theorem productError_variance (i j : Fin d) (s t : ℝ≥0) (hst : s≤t) :
    (∫ ω, productError d i j s t ω^2 ∂productLaw d)=
      (if i=j then 2 else 1)*((t : ℝ)-(s : ℝ))^2 := by
  by_cases hij : i=j
  · subst j
    have h := (eval_preserving d i).hasLaw.integral_comp
      (f := fun ω => BrownianQuadraticVariationSteps.centeredSquare s t ω^2)
      ((((BrownianMartingaleSource.measurable_increment s t).pow_const 2).sub measurable_const).pow_const 2).aestronglyMeasurable
    change (∫ ω, (coordinateIncrement d i s t ω^2-((t : ℝ)-(s : ℝ)))^2 ∂productLaw d)=_ at h
    simpa [productError,← pow_two] using h.trans
      (BrownianQuadraticVariationSteps.centeredSquare_variance s t hst)
  · have hind := ((coordinateIncrements_independent d s t).indepFun hij).comp
      (measurable_id.pow_const 2) (measurable_id.pow_const 2)
    have h := hind.integral_mul_eq_mul_integral
      ((coordinateIncrement_measurable d i s t).pow_const 2).aestronglyMeasurable
      ((coordinateIncrement_measurable d j s t).pow_const 2).aestronglyMeasurable
    change (∫ ω, coordinateIncrement d i s t ω^2*coordinateIncrement d j s t ω^2 ∂productLaw d)=_ at h
    simp only [Function.comp_apply,id_eq] at h
    rw [coordinateIncrement_square_mean d i s t hst,coordinateIncrement_square_mean d j s t hst] at h
    simpa only [productError,if_neg hij,sub_zero,mul_pow,← pow_two,one_mul] using h

/-- A measurable function of the entire actual future Euclidean increment
is independent of the ENTIRE original joint past; same product source only. -/
theorem condExp_vector_function (s t : ℝ≥0) (hst : s≤t)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Measurable φ) :
    (productLaw d)[fun ω=>φ (vectorIncrement d s t ω) | jointNaturalFiltration d s]
      =ᵐ[productLaw d] fun _=>∫ ω,φ (vectorIncrement d s t ω) ∂productLaw d := by
  have hm : @Measurable (Sample d) (EuclideanSpace ℝ (Fin d))
      (MeasurableSpace.comap (vectorIncrement d s t) inferInstance) inferInstance
      (vectorIncrement d s t) := measurable_iff_comap_le.mpr le_rfl
  exact condExp_indep_eq (vectorIncrement_measurable d s t).comap_le
    ((jointNaturalFiltration d).le s) (hφ.comp hm).stronglyMeasurable
    (vectorIncrement_indep_jointNatural d s t hst)

theorem productError_condExp_square (i j : Fin d) (s t : ℝ≥0) (hst : s≤t) :
    (productLaw d)[fun ω=>productError d i j s t ω^2 | jointNaturalFiltration d s]
      =ᵐ[productLaw d] fun _=>(if i=j then 2 else 1)*((t : ℝ)-(s : ℝ))^2 := by
  let φ : EuclideanSpace ℝ (Fin d) → ℝ := fun z=>(z i*z j-(if i=j then (t : ℝ)-(s : ℝ) else 0))^2
  have hφ : Measurable φ :=
    (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.measurable.mul
      (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.measurable).sub measurable_const).pow_const 2
  have h := condExp_vector_function d s t hst φ hφ
  change (productLaw d)[fun ω=>productError d i j s t ω^2 | jointNaturalFiltration d s]
    =ᵐ[productLaw d] fun _=>∫ ω,productError d i j s t ω^2 ∂productLaw d at h
  exact h.trans (ae_of_all _ (fun _=>productError_variance d i j s t hst))

theorem coordinateIncrement_stronglyMeasurable_end (i : Fin d) (s t : ℝ≥0) (hst : s≤t) :
    StronglyMeasurable[jointNaturalFiltration d t] (coordinateIncrement d i s t) := by
  have hs := (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp_stronglyMeasurable
    (vectorProcess_stronglyAdapted d s)
  have ht := (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp_stronglyMeasurable
    (vectorProcess_stronglyAdapted d t)
  exact ht.sub (hs.mono ((jointNaturalFiltration d).mono hst))

theorem productError_stronglyMeasurable_end (i j : Fin d) (s t : ℝ≥0) (hst : s≤t) :
    StronglyMeasurable[jointNaturalFiltration d t] (productError d i j s t) :=
  ((coordinateIncrement_stronglyMeasurable_end d i s t hst).mul
    (coordinateIncrement_stronglyMeasurable_end d j s t hst)).sub stronglyMeasurable_const

/-- Permitted scalar weights may read EVERY coordinate's actual START past. -/
def weightedError (i j : Fin d) (H : Sample d→ℝ) (s t : ℝ≥0) : Sample d→ℝ :=
  H*productError d i j s t

theorem weightedError_memLp_two (i j : Fin d) {H : Sample d→ℝ}
    (hH : MemLp H ∞ (productLaw d)) (s t : ℝ≥0) :
    MemLp (weightedError d i j H s t) 2 (productLaw d) :=
  (productError_memLp_two d i j s t).mul hH

theorem weightedError_stronglyMeasurable_end (i j : Fin d) {H : Sample d→ℝ}
    (s t : ℝ≥0) (hst : s≤t) (hHpast : StronglyMeasurable[jointNaturalFiltration d s] H) :
    StronglyMeasurable[jointNaturalFiltration d t] (weightedError d i j H s t) :=
  (hHpast.mono ((jointNaturalFiltration d).mono hst)).mul (productError_stronglyMeasurable_end d i j s t hst)

theorem weightedError_condExp_zero (i j : Fin d) {H : Sample d→ℝ}
    (s t : ℝ≥0) (hst : s≤t) (hHpast : StronglyMeasurable[jointNaturalFiltration d s] H)
    (hH : MemLp H ∞ (productLaw d)) :
    (productLaw d)[weightedError d i j H s t | jointNaturalFiltration d s] =ᵐ[productLaw d] fun _=>0 := by
  apply (condExp_mul_of_stronglyMeasurable_left hHpast
    ((weightedError_memLp_two d i j hH s t).integrable one_le_two)
    ((productError_memLp_two d i j s t).integrable one_le_two)).trans
  filter_upwards [productError_condExp_zero d i j s t hst] with ω hω
  simp only [Pi.mul_apply,hω,mul_zero]

theorem weightedError_condExp_square (i j : Fin d) {H : Sample d→ℝ}
    (s t : ℝ≥0) (hst : s≤t) (hHpast : StronglyMeasurable[jointNaturalFiltration d s] H)
    (hH : MemLp H ∞ (productLaw d)) :
    (productLaw d)[fun ω=>weightedError d i j H s t ω^2 | jointNaturalFiltration d s]
      =ᵐ[productLaw d] fun ω=>H ω^2*((if i=j then 2 else 1)*((t : ℝ)-(s : ℝ))^2) := by
  have he : (fun ω=>weightedError d i j H s t ω^2)=
      (fun ω=>H ω^2)*(fun ω=>productError d i j s t ω^2) := by
    ext ω
    simp only [weightedError,Pi.mul_apply,mul_pow]
  have hi : Integrable ((fun ω=>H ω^2)*(fun ω=>productError d i j s t ω^2)) (productLaw d) := by
    rw [← he]
    exact (weightedError_memLp_two d i j hH s t).integrable_sq
  rw [he]
  apply (condExp_mul_of_stronglyMeasurable_left (hHpast.pow 2) hi
    (productError_memLp_two d i j s t).integrable_sq).trans
  filter_upwards [productError_condExp_square d i j s t hst] with ω hω
  simp only [Pi.mul_apply,Pi.pow_apply,hω]

theorem weightedError_variance (i j : Fin d) {H : Sample d→ℝ}
    (s t : ℝ≥0) (hst : s≤t) (hHpast : StronglyMeasurable[jointNaturalFiltration d s] H)
    (hH : MemLp H ∞ (productLaw d)) :
    (∫ ω,weightedError d i j H s t ω^2 ∂productLaw d)=
      ((if i=j then 2 else 1)*((t : ℝ)-(s : ℝ))^2)*(∫ ω,H ω^2 ∂productLaw d) := by
  rw [← integral_condExp ((jointNaturalFiltration d).le s),
    integral_congr_ae (weightedError_condExp_square d i j s t hst hHpast hH),integral_mul_const,mul_comm]

/-- All coordinate pairs share the SAME temporal causal orthogonality. No
independence of weights or the row's coordinates is assumed. -/
theorem weightedError_nonoverlap (i j k l : Fin d) {H K : Sample d→ℝ}
    (s t u v : ℝ≥0) (hst : s≤t) (htu : t≤u) (huv : u≤v)
    (hHpast : StronglyMeasurable[jointNaturalFiltration d s] H)
    (hKpast : StronglyMeasurable[jointNaturalFiltration d u] K)
    (hH : MemLp H ∞ (productLaw d)) (hK : MemLp K ∞ (productLaw d)) :
    (∫ ω,weightedError d i j H s t ω*weightedError d k l K u v ω ∂productLaw d)=0 := by
  have hi := (weightedError_memLp_two d i j hH s t).integrable_mul (weightedError_memLp_two d k l hK u v)
  have hm := (weightedError_stronglyMeasurable_end d i j s t hst hHpast).mono
    ((jointNaturalFiltration d).mono htu)
  have hc := condExp_mul_of_stronglyMeasurable_left hm hi
    ((weightedError_memLp_two d k l hK u v).integrable one_le_two)
  have hz : (productLaw d)[weightedError d i j H s t*weightedError d k l K u v |
      jointNaturalFiltration d u] =ᵐ[productLaw d] fun _=>0 := by
    apply hc.trans
    filter_upwards [weightedError_condExp_zero d k l u v huv hKpast hK] with ω hω
    simp only [Pi.mul_apply,hω,mul_zero]
  simp only [Pi.mul_def] at hz
  rw [← integral_condExp ((jointNaturalFiltration d).le u),integral_congr_ae hz,integral_zero]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorQuadraticVariationSteps
