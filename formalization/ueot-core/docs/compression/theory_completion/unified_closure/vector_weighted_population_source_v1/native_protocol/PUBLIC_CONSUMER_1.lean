import UEOT
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorSimplePredictableIntegral
open BrownianVectorTimeInput
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

-- Native input has the actual Euclidean codomain, not a pair with sup norm.
example (d : ℕ) (T : ℝ≥0) : IsFiniteMeasure (inputLaw d T) := inferInstance
example (d : ℕ) (H : Fin d → Sample d → ℝ) (s : ℝ≥0) (p : ℝ × Sample d) :
    intervalInput d H s s p = 0 := by simp [intervalInput]
example (H : Fin 0 → Sample 0 → ℝ) (s t : ℝ≥0) (p : ℝ × Sample 0) :
    intervalInput 0 H s t p = 0 := Subsingleton.elim _ _

-- Concrete two-coordinate unit weights over the actual unit interval.
def clock : Fin 2 → ℝ≥0 := fun i => (i : ℕ)
def weights : Fin 1 → Fin 2 → Sample 2 → ℝ := fun _ _ _ => 1

theorem clock_mono : Monotone clock := by
  intro i j hij
  unfold clock
  exact_mod_cast hij

theorem weights_bound (j : Fin 1) (k : Fin 2) : MemLp (weights j k) ∞ (productLaw 2) :=
  memLp_top_const 1

theorem weights_past (j : Fin 1) (k : Fin 2) :
    StronglyMeasurable[jointNaturalFiltration 2 (clock j.castSucc)] (weights j k) :=
  stronglyMeasurable_const

theorem coefficient_energy (ω : Sample 2) : ‖coefficient 2 (weights 0) ω‖^2 = 2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  norm_num [weights]

theorem actual_input_energy : (∫ p, ‖integrand 2 clock weights p‖^2 ∂inputLaw 2 1) = 2 := by
  have h := integrand_energy 1 clock weights clock_mono (show clock (Fin.last 1) ≤ 1 by norm_num [clock]) weights_bound
  rw [Fin.sum_univ_one] at h
  simp only [clock,Fin.val_succ,Fin.val_castSucc,Fin.val_zero,Nat.cast_zero,NNReal.coe_zero] at h
  simp_rw [coefficient_energy] at h
  simpa using h


-- The native class square norm is two. A sup-norm substitution would give one.
example : ‖inputClass 1 clock weights weights_bound‖^2 = 2 ∧
    ‖outputClass clock weights weights_bound‖ = ‖inputClass 1 clock weights weights_bound‖ := by
  refine ⟨?_,input_output_norm 1 clock weights clock_mono (by norm_num [clock]) weights_past weights_bound⟩
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  have he : (fun p => inner ℝ (inputClass 1 clock weights weights_bound p)
      (inputClass 1 clock weights weights_bound p)) =ᵐ[inputLaw 2 1]
      fun p => ‖integrand 2 clock weights p‖^2 := by
    filter_upwards [(integrand_memLp_two 1 clock weights weights_bound).coeFn_toLp] with p hp
    change (inputClass 1 clock weights weights_bound) p = _ at hp
    rw [hp,real_inner_self_eq_norm_sq]
  rw [integral_congr_ae he,actual_input_energy]

-- The literal empty/zero-time input is retained before any completion.
example (d : ℕ) (p : ℝ × Sample d) :
    integrand d (fun _ : Fin 1 => (0 : ℝ≥0)) (fun j : Fin 0 => Fin.elim0 j) p = 0 := by
  simp [integrand]


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



-- The new native Euclidean input actually accepts cross-coordinate PAST
-- weights; it is not transported to the old own-scalar filtration.
def laterClock : Fin 2 → ℝ≥0 := ![1,2]
def pastWeights : Fin 1 → Fin 2 → Sample 2 → ℝ := fun _ => rotating 1

example : ‖outputClass laterClock pastWeights (fun _ => rotating_bounded 1)‖ =
    ‖inputClass 2 laterClock pastWeights (fun _ => rotating_bounded 1)‖ := by
  apply input_output_norm
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i
    norm_num [laterClock]
  · change (2 : ℝ≥0) ≤ 2
    exact le_rfl
  · intro j k
    fin_cases j
    exact rotating_past 1 k
