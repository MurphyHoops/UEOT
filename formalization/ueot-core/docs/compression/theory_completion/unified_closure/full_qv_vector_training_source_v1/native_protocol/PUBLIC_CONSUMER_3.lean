import UEOT
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory BigOperators
noncomputable section

-- Both weights read the real SECOND coordinate at the interval start.
-- In particular the first weight is not restricted to its own-coordinate past.
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

-- A random, cross-coordinate past-reading coefficient has energy
-- exactly the actual elapsed source clock, not a supplied variance premise.
example : (∫ ω, oneStep 2 (rotating 1) 1 2 ω ^ 2 ∂productLaw 2) = 1 ∧
    ((productLaw 2)[oneStep 2 (rotating 1) 1 2 | jointNaturalFiltration 2 1]
      =ᵐ[productLaw 2] fun _ => (0 : ℝ)) ∧
    StronglyMeasurable[jointNaturalFiltration 2 2] (oneStep 2 (rotating 1) 1 2) := by
  refine ⟨?_,oneStep_condExp_zero 1 2 (by norm_num) (rotating_past 1) (rotating_bounded 1),
    oneStep_stronglyMeasurable_end 1 2 (by norm_num) (rotating_past 1)⟩
  rw [oneStep_isometry 1 2 (by norm_num) (rotating_past 1) (rotating_bounded 1)]
  simp_rw [rotating_unit]
  norm_num

example (H : Fin 0 → Sample 0 → ℝ) (s t : ℝ≥0) (ω : Sample 0) : oneStep 0 H s t ω = 0 :=
  oneStep_zero_dimension H s t ω

-- No covariance of two chosen weights was assumed: native conditional matrix
-- pulls back both real weights against the same actual joint filtration.
example (s t : ℝ≥0) (hst : s ≤ t) :
    (productLaw 2)[fun ω => component 2 (rotating s) 0 s t ω * component 2 (rotating s) 1 s t ω |
      jointNaturalFiltration 2 s] =ᵐ[productLaw 2] fun _ => (0 : ℝ) := by
  simpa using component_condExp_product 0 1 s t hst (rotating_past s) (rotating_bounded s)


open BrownianVectorSimplePredictableIntegral

def repeatedClock (i : Fin 4) : ℝ≥0 :=
  if (i : ℕ) = 0 then 0 else if (i : ℕ) = 3 then 2 else 1

example : repeatedClock 0 = 0 ∧ repeatedClock 1 = 1 ∧ repeatedClock 2 = 1 ∧ repeatedClock 3 = 2 :=
  ⟨rfl,rfl,rfl,rfl⟩
def feedbackWeights (j : Fin 3) : Fin 2 → Sample 2 → ℝ := rotating (repeatedClock j.castSucc)

theorem repeatedClock_monotone : Monotone repeatedClock := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  fin_cases i <;> norm_num [repeatedClock,Fin.castSucc,Fin.succ,Fin.castAdd]

theorem feedback_past (j : Fin 3) (k : Fin 2) :
    StronglyMeasurable[jointNaturalFiltration 2 (repeatedClock j.castSucc)] (feedbackWeights j k) :=
  rotating_past _ k

theorem feedback_bound (j : Fin 3) (k : Fin 2) : MemLp (feedbackWeights j k) ∞ (productLaw 2) :=
  rotating_bounded _ k

-- This genuinely combines two different nonzero intervals and retains the
-- repeated-time interval, with the later weights read from its actual past.
example :
    (∫ ω, simpleIntegral 2 repeatedClock feedbackWeights ω ^ 2 ∂productLaw 2) = 2 ∧
    (∫ ω, simpleIntegral 2 repeatedClock feedbackWeights ω ∂productLaw 2) = 0 ∧
    StronglyMeasurable[jointNaturalFiltration 2 2] (simpleIntegral 2 repeatedClock feedbackWeights) := by
  refine ⟨?_,simpleIntegral_mean_zero repeatedClock feedbackWeights repeatedClock_monotone
    feedback_past feedback_bound,?_⟩
  · rw [simpleIntegral_isometry repeatedClock feedbackWeights repeatedClock_monotone feedback_past feedback_bound]
    have he (j : Fin 3) : (∫ ω, ‖coefficient 2 (feedbackWeights j) ω‖^2 ∂productLaw 2) = 1 := by
      simp_rw [feedbackWeights,rotating_unit]
      simp
    simp_rw [he]
    rw [Fin.sum_univ_three]
    norm_num [repeatedClock,Fin.castSucc,Fin.succ,Fin.castAdd]
  · exact simpleIntegral_stronglyMeasurable_end repeatedClock feedbackWeights
      repeatedClock_monotone feedback_past

example (d : ℕ) (τ : Fin 1 → ℝ≥0) (H : Fin 0 → Fin d → Sample d → ℝ) (ω : Sample d) :
    simpleIntegral d τ H ω = 0 := by simp [simpleIntegral]

example (n : ℕ) (τ : Fin (n+1) → ℝ≥0) (H : Fin n → Fin 0 → Sample 0 → ℝ) (ω : Sample 0) :
    simpleIntegral 0 τ H ω = 0 := by simp [simpleIntegral,oneStep]

-- An all-repeated clock has zero literal output at every sample, even before
-- passing to an AE/class or invoking a mean-square limit.
example (d n : ℕ) (r : ℝ≥0) (H : Fin n → Fin d → Sample d → ℝ) (ω : Sample d) :
    simpleIntegral d (fun _ : Fin (n+1) => r) H ω = 0 := by
  simp [simpleIntegral,oneStep,component,coordinateIncrement]

namespace IndependentExtraVector
-- Unequal coefficients distinguish Euclidean energy from the sup norm.
def unequal (i : Fin 3) (_w : Sample 3) : ℝ := if i = 0 then 1 else 2
example : (∫ w, oneStep 3 unequal 1 3 w ^ 2 ∂productLaw 3) = 18 := by
  have hp (i : Fin 3) : StronglyMeasurable[jointNaturalFiltration 3 1] (unequal i) := stronglyMeasurable_const
  have hb (i : Fin 3) : MemLp (unequal i) ∞ (productLaw 3) := memLp_top_const _
  rw [oneStep_isometry 1 3 (by norm_num) hp hb]
  have he (w : Sample 3) : ‖coefficient 3 unequal w‖^2 = 9 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    norm_num [coefficient_apply,unequal,show (1 : Fin 3) ≠ 0 from by decide,show (2 : Fin 3) ≠ 0 from by decide]
  simp_rw [he]
  norm_num
example (d : ℕ) : IsProbabilityMeasure (productLaw d) := inferInstance
#check vectorIncrement_indep_jointNatural
#check coordinateIncrement_condExp_product
#print axioms BrownianFiniteProductSource.vectorIncrement_hasLaw
#print axioms BrownianFiniteProductSource.vectorIncrement_indep_jointNatural
#print axioms BrownianFiniteProductSource.coordinateIncrement_condExp_product
#print axioms BrownianVectorOneStepIntegral.oneStep_isometry
#print axioms BrownianVectorSimplePredictableIntegral.nonoverlap_orthogonal
#print axioms BrownianVectorSimplePredictableIntegral.simpleIntegral_isometry
end IndependentExtraVector
