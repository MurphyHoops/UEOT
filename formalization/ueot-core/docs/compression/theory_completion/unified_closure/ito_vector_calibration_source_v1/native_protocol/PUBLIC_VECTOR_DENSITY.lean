import UEOT

-- Public-root consumer of the actual source; retained original independent discriminator.
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput
open BrownianVectorIntegralClosure BrownianVectorPredictableInputs
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def rotating (s : ℝ≥0) (i : Fin 2) (ω : Sample 2) : ℝ :=
  if i = 0 then Real.cos (coordinate 2 1 s ω) else Real.sin (coordinate 2 1 s ω)

theorem rotating_past (s : ℝ≥0) (i : Fin 2) :
    StronglyMeasurable[jointNaturalFiltration 2 s] (rotating s i) := by
  have hc : StronglyMeasurable[jointNaturalFiltration 2 s] (coordinate 2 1 s) :=
    (EuclideanSpace.proj (𝕜:=ℝ) (1 : Fin 2)).continuous.comp_stronglyMeasurable
      (vectorProcess_stronglyAdapted 2 s)
  unfold rotating
  split_ifs
  · exact Real.continuous_cos.comp_stronglyMeasurable hc
  · exact Real.continuous_sin.comp_stronglyMeasurable hc

theorem rotating_bounded (s : ℝ≥0) (i : Fin 2) : MemLp (rotating s i) ∞ (productLaw 2) := by
  apply memLp_top_of_bound (((rotating_past s i).mono ((jointNaturalFiltration 2).le s)).aestronglyMeasurable) 1
  apply ae_of_all
  intro ω
  simp only [Real.norm_eq_abs,rotating]
  split_ifs
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

theorem rotating_unit (s : ℝ≥0) (ω : Sample 2) : ‖coefficient 2 (rotating s) ω‖^2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  simp only [coefficient_apply,rotating]
  simp only [show (1 : Fin 2) ≠ 0 by decide,ite_true,ite_false]
  simpa only [add_comm] using Real.sin_sq_add_cos_sq (coordinate 2 1 s ω)



-- An actual source-dependent cross-coordinate START reader belongs to the
-- genuine native joint predictable sigma, not an own-scalar substitute.
example : StronglyMeasurable[predictableSigma 2] (intervalInput 2 (rotating 1) 1 2) :=
  intervalInput_predictable 1 2 (rotating_past 1)

example : inputValue (blockInput 2 2 1 (by norm_num) (rotating 1)
    (rotating_past 1) (rotating_bounded 1)) ∈ fullPredictableL2 2 2 :=
  elementary_input_predictable _

-- Domain defined independently using NATIVE lpMeas, with correct E/scalar order.
example (d : ℕ) (T : ℝ≥0) : fullPredictableL2 d T =
    lpMeas (EuclideanSpace ℝ (Fin d)) ℝ (predictableSigma d) 2 (inputLaw d T) := rfl

example (d : ℕ) (T : ℝ≥0) : integralDomain d T ≤ fullPredictableL2 d T :=
  integralDomain_le_fullPredictableL2 d T

example (d : ℕ) : inputValue (blockInput d 0 0 le_rfl (fun _ _ => 0)
    (fun _ => stronglyMeasurable_const) (fun _ => MemLp.zero)) ∈ fullPredictableL2 d 0 :=
  elementary_input_predictable _

example (T : ℝ≥0) : inputValue (blockInput 0 T 0 bot_le (fun k => Fin.elim0 k)
    (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)) ∈ fullPredictableL2 0 T :=
  elementary_input_predictable _

open BrownianVectorPredictableDensity
-- Genuine native full domain, no closed-span membership supplied by caller.
example (d : ℕ) (T : ℝ≥0) (f : fullPredictableL2 d T) :
    ‖predictableIntegral d T f‖ = ‖f‖ := predictableIntegral_norm d T f
example (d : ℕ) (T : ℝ≥0) (f g : fullPredictableL2 d T) :
    dist (predictableIntegral d T f) (predictableIntegral d T g) = dist f g :=
  (predictableIntegralIsometry d T).isometry.dist_eq f g
example (d : ℕ) (T : ℝ≥0) : integralDomain d T =
    lpMeas (EuclideanSpace ℝ (Fin d)) ℝ (predictableSigma d) 2 (inputLaw d T) :=
  integralDomain_eq_fullPredictableL2 d T
example (d : ℕ) (T : ℝ≥0) (A : Set (ℝ × Sample d))
    (hA : MeasurableSet[predictableSigma d] A) (c : EuclideanSpace ℝ (Fin d)) :
    indicatorClass d T A (predictableSigma_le d A hA) c ∈ integralDomain d T :=
  predictable_indicator_mem_domain d T A hA c
-- Literal H_0 reads the OTHER noise coordinate's past, and the very same
-- returned projection output is consumed on the now-proved full domain.
def rotatingRecord := blockInput 2 2 1 (by norm_num) (rotating 1) (rotating_past 1) (rotating_bounded 1)
example : predictableIntegral 2 2 (literalPredictableInput 2 rotatingRecord) = outputValue rotatingRecord :=
  predictableIntegral_returns_literal 2 rotatingRecord
example : ∀ᵐ ω ∂productLaw 2,
    (predictableIntegral 2 2 (literalPredictableInput 2 rotatingRecord) : Lp ℝ 2 (productLaw 2)) ω =
      BrownianVectorSimplePredictableIntegral.simpleIntegral 2 rotatingRecord.clock rotatingRecord.coefficient ω := by
  rw [predictableIntegral_returns_literal]
  exact (BrownianVectorSimplePredictableIntegral.simpleIntegral_memLp_two rotatingRecord.clock
    rotatingRecord.coefficient rotatingRecord.coefficient_bounded).coeFn_toLp
example (d : ℕ) : inputLaw d 0 = 0 := inputLaw_zero d
-- Horizon zero and dimension zero are the SAME native input spaces.
example (d : ℕ) (f : fullPredictableL2 d 0) : predictableIntegral d 0 f = 0 := by
  apply norm_eq_zero.mp
  rw [predictableIntegral_norm]
  change ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d 0))‖ = 0
  apply norm_eq_zero.mpr
  apply Lp.ext
  exact ae_iff.mpr (by simp [inputLaw_zero])
example (T : ℝ≥0) (f : fullPredictableL2 0 T) : predictableIntegral 0 T f = 0 := by
  apply norm_eq_zero.mp
  rw [predictableIntegral_norm]
  change ‖(f : Lp (EuclideanSpace ℝ (Fin 0)) 2 (inputLaw 0 T))‖ = 0
  apply norm_eq_zero.mpr
  apply Lp.ext
  exact ae_of_all _ (fun _ => Subsingleton.elim _ _)

-- Nondegenerate actual cross-coordinate-past input still has Euclidean energy1.
theorem actual_rotating_integral_energy : ‖predictableIntegral 2 2 (literalPredictableInput 2 rotatingRecord)‖^2 = 1 := by
  rw [predictableIntegral_returns_literal,← real_inner_self_eq_norm_sq,L2.inner_def]
  have hc := (BrownianVectorSimplePredictableIntegral.simpleIntegral_memLp_two rotatingRecord.clock
    rotatingRecord.coefficient rotatingRecord.coefficient_bounded).coeFn_toLp
  change (∫ ω, inner ℝ (outputValue rotatingRecord ω) (outputValue rotatingRecord ω) ∂productLaw 2) = 1
  calc
    _ = ∫ ω, BrownianVectorSimplePredictableIntegral.simpleIntegral 2 rotatingRecord.clock
          rotatingRecord.coefficient ω ^ 2 ∂productLaw 2 := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω
      have he : outputValue rotatingRecord ω = BrownianVectorSimplePredictableIntegral.simpleIntegral 2
          rotatingRecord.clock rotatingRecord.coefficient ω := hω
      rw [he,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    _ = _ := BrownianVectorSimplePredictableIntegral.simpleIntegral_isometry _ _
      rotatingRecord.clock_mono rotatingRecord.coefficient_past rotatingRecord.coefficient_bounded
    _ = 1 := by
      change (∑ i : Fin 2, (((![0,1,2] i.succ : ℝ≥0) : ℝ) - ((![0,1,2] i.castSucc : ℝ≥0) : ℝ)) *
        (∫ ω, ‖coefficient 2 (![fun _ _ => 0,rotating 1] i) ω‖^2 ∂productLaw 2)) = 1
      rw [Fin.sum_univ_two]
      have hz : coefficient 2 (fun _ _ => 0) = fun _ => 0 := by
        funext ω
        apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
        funext k
        rfl
      norm_num [rotating_unit,hz,show (![0,1,2] (2 : Fin 3) : ℝ≥0) = 2 from rfl]

-- Positive-horizon clock contains an actual repeated zero endpoint.
def repeatedStart : ElementaryInput 2 1 := blockInput 2 1 0 bot_le (fun _ _ => 1)
  (fun _ => stronglyMeasurable_const) (fun _ => memLp_top_const 1)
example : predictableIntegral 2 1 (literalPredictableInput 2 repeatedStart) = outputValue repeatedStart :=
  predictableIntegral_returns_literal 2 repeatedStart
#print axioms actual_rotating_integral_energy

namespace IndependentVectorZeroHorizon
open MeasureTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
example (d : ℕ) (f : BrownianVectorPredictableInputs.fullPredictableL2 d 0) :
    BrownianVectorPredictableDensity.predictableIntegral d 0 f = 0 := by
  have hf : f = 0 := by
    apply Subtype.ext
    apply Lp.ext
    simp [BrownianVectorPredictableDensity.inputLaw_zero]
    exact Filter.eventually_bot
  rw [hf,map_zero]
#print axioms BrownianVectorPredictableDensity.integralDomain_eq_fullPredictableL2
#print axioms BrownianVectorPredictableDensity.predictableIntegral_returns_literal
end IndependentVectorZeroHorizon
