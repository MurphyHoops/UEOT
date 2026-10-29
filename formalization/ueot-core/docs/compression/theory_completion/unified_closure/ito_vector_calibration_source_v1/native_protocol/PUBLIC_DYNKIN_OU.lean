import UEOT

-- Public-root consumer of the actual source; retained original independent discriminator.
namespace IndependentReusedAuthor0
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianBoundedC2DynkinSource BrownianPredictableInputs BrownianTimeIntegrand
open scoped NNReal Topology MeasureTheory
#check actual_boundedC2_dynkin
#check actual_source_p_rec_02
#check constantInput_coe
#print axioms actual_boundedC2_dynkin
#print axioms actual_source_p_rec_02
#print axioms actual_nonzero_noise_witness
example (T : ℝ) (hT : 0 ≤ T) :
    UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate
      (fun t => ∫ x, Real.sin x ∂stateLaw 3 2 t)
      (fun t => ∫ x, generator 2 Real.sin x ∂stateLaw 3 2 t) T :=
  actual_boundedC2_dynkin 3 2 T hT Real.sin (by fun_prop) 1 1 (by norm_num) (by norm_num)
    (fun x => by simpa only [Real.deriv_sin,Real.norm_eq_abs] using Real.abs_cos_le_one x)
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_iteratedDeriv_sin_le_one 2 x)
example : (∫ ω, (state 3 2 1 ω-3)^2 ∂sourceLaw) = 4 := actual_nonzero_noise_witness
example : UEOT.V3.RecoveryDynkin.DynkinExpectationCertificate
    (fun t => ∫ x, Real.sin x ∂stateLaw 3 2 t)
    (fun t => ∫ x, generator 2 Real.sin x ∂stateLaw 3 2 t) 0 :=
  actual_boundedC2_dynkin 3 2 0 (by norm_num) Real.sin (by fun_prop) 1 1 (by norm_num) (by norm_num)
    (fun x => by simpa only [Real.deriv_sin,Real.norm_eq_abs] using Real.abs_cos_le_one x)
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_iteratedDeriv_sin_le_one 2 x)

private noncomputable def W (x : ℝ) := 2+Real.sin x
private theorem W_deriv : deriv W = Real.cos := by
  funext x
  exact ((Real.hasDerivAt_sin x).const_add 2).deriv
private theorem W_second : iteratedDeriv 2 W = -Real.sin := by
  rw [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,W_deriv]
  exact funext (fun x => Real.deriv_cos (x := x))
private theorem W_bound (x : ℝ) : ‖deriv W x‖ ≤ 1 := by
  simpa only [W_deriv,Real.norm_eq_abs] using Real.abs_cos_le_one x
private theorem W_bound₂ (x : ℝ) : ‖iteratedDeriv 2 W x‖ ≤ 1 := by
  simpa only [W_second,Pi.neg_apply,norm_neg,Real.norm_eq_abs] using Real.abs_sin_le_one x
/-- Nontrivial actual P-REC nonlinear-test consumer. d2 is the bounded test
energy W itself; this is not Euclidean-distance coercivity or state recurrence. -/
example (T : ℝ) (hT : 0 ≤ T) : ∀ t ∈ Icc 0 T,
    (∫ x, W x ∂stateLaw 3 2 t) ≤
      (Real.exp (-2*t)*W 3+(4/2)*(1-Real.exp (-2*t)))/1 := by
  apply actual_source_p_rec_02 3 2 T hT W (by unfold W; fun_prop) 1 1
    (by norm_num) (by norm_num) W_bound W_bound₂ W
    (fun t _ => stateLaw_test_integrable 3 2 t W (by unfold W; fun_prop) 1 (by norm_num) W_bound)
    2 4 1 (by norm_num) (by norm_num) (by norm_num)
  · intro x
    simp only [generator,W_second,Pi.neg_apply,W]
    linarith
  · intro x; simp
end IndependentReusedAuthor0

namespace IndependentReusedAuthor1
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource OUConditionalInnovationSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory
#check actualOU_condExp_residual
#check innovation_indep_whole_past
#check actualOU_stronglyAdapted
#print axioms actualOU_transition_decomposition
#print axioms innovation_hasLaw
#print axioms innovation_condExp_transform
#print axioms actualOU_condExp_mean
#print axioms actualOU_condExp_centered_square
#print axioms transitionVariance_pos
example (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    actualOU 1 2 3 t ω = OUQuadraticDynkinSource.ouSource process 1 2 3 t ω := rfl
example : sourceLaw[actualOU 1 2 3 2 | ouFiltration 1 (by norm_num) 1] =ᵐ[sourceLaw]
    fun ω => Real.exp (-1)*actualOU 1 2 3 1 ω := by
  have hd : decay 1 1 2 = Real.exp (-1) := by norm_num [decay]
  simpa only [hd] using
    actualOU_condExp_mean 1 2 3 (by norm_num) 1 2 (by norm_num)
example : sourceLaw[fun ω => (actualOU 1 2 3 2 ω-decay 1 1 2*actualOU 1 2 3 1 ω)^2 |
    ouFiltration 1 (by norm_num) 1] =ᵐ[sourceLaw] fun _ => 2*(1-Real.exp (-2)) := by
  convert actualOU_condExp_centered_square 1 2 3 (by norm_num) 1 2 (by norm_num) using 1; norm_num
example : 0 < (transitionVariance 1 2 1 2 : ℝ) :=
  transitionVariance_pos 1 2 (by norm_num) (by norm_num) 1 2 (by norm_num)
example (s : ℝ≥0) : (transitionVariance 1 2 s s : ℝ)=0 := by
  rw [transitionVariance_coe 1 2 (by norm_num) s s le_rfl]
  simp
example : sourceLaw[fun ω => Real.sin (actualOU 1 2 3 2 ω-decay 1 1 2*actualOU 1 2 3 1 ω) |
    ouFiltration 1 (by norm_num) 1] =ᵐ[sourceLaw]
    fun _ => ∫ x, Real.sin x ∂gaussianReal 0 (transitionVariance 1 2 1 2) :=
  actualOU_condExp_residual 1 2 3 (by norm_num) 1 2 (by norm_num) Real.sin Real.measurable_sin
/-- Identity reuse of the old OU recovery family on the SAME actual source;
not a rebinding to the newly constructed free-Brownian test law. -/
example (T : ℝ) (hT : 0 ≤ T) : ∀ t ∈ Icc 0 T,
    (∫ x, x^2 ∂OUQuadraticDynkinSource.ouLaw sourceLaw process 1 2 3 t) ≤
      Real.exp (-(2*1)*t)*3^2+2^2/(2*1)*(1-Real.exp (-(2*1)*t)) :=
  OUQuadraticDynkinSource.actual_source_p_rec_02 process_isPreBrownian 1 2 3 T (by norm_num) hT
end IndependentReusedAuthor1

namespace IndependentReusedAuthor2
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource OUConditionalInnovationSource OUTransitionKernelSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory
#check innovation_condDistrib
#check actualOU_condExp_transition
#check transitionKernel_markov
#print axioms innovation_condDistrib
#print axioms actualOU_condExp_transition
#print axioms transitionKernel_apply
#print axioms actualOU_condExp_kernel
example : sourceLaw[fun ω => Real.sin (actualOU 1 2 3 2 ω) | ouFiltration 1 (by norm_num) 1]
    =ᵐ[sourceLaw] fun ω => ∫ y, Real.sin y ∂transitionKernel 1 2 1 2 (actualOU 1 2 3 1 ω) :=
  actualOU_condExp_kernel 1 2 3 (by norm_num) 1 2 (by norm_num) Real.sin Real.measurable_sin 1
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
example : sourceLaw[fun ω => Real.cos (actualOU 1 2 3 2 ω) | ouFiltration 1 (by norm_num) 1]
    =ᵐ[sourceLaw] fun ω => ∫ y, Real.cos y ∂gaussianReal (decay 1 1 2*actualOU 1 2 3 1 ω)
      (transitionVariance 1 2 1 2) := by
  simpa only [transitionKernel_apply] using actualOU_condExp_kernel 1 2 3 (by norm_num) 1 2 (by norm_num)
    Real.cos Real.measurable_cos 1 (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)
example (k σ x : ℝ) (t : ℝ≥0) : transitionKernel k σ t t x = Measure.dirac x := by
  have hv : transitionVariance k σ t t=0 := by
    apply NNReal.coe_injective
    change (Real.exp (-k*(t : ℝ))*σ)^2*(nndist (OUQuadraticDynkinSource.ouClock k t : ℝ) (OUQuadraticDynkinSource.ouClock k t : ℝ) : ℝ)=0
    simp
  rw [transitionKernel_apply,hv,gaussianReal_zero_var]
  simp [decay]
example (k x : ℝ) (s t : ℝ≥0) : transitionKernel k 0 s t x = Measure.dirac (decay k s t*x) := by
  have hv : transitionVariance k 0 s t=0 := by
    apply NNReal.coe_injective
    change (Real.exp (-k*(t : ℝ))*0)^2*(nndist (OUQuadraticDynkinSource.ouClock k t : ℝ) (OUQuadraticDynkinSource.ouClock k s : ℝ) : ℝ)=0
    simp
  rw [transitionKernel_apply,hv,gaussianReal_zero_var]
example : 0 < (transitionVariance 1 2 1 2 : ℝ) :=
  transitionVariance_pos 1 2 (by norm_num) (by norm_num) 1 2 (by norm_num)
example : IsMarkovKernel (transitionKernel 1 2 1 2) := inferInstance
end IndependentReusedAuthor2

namespace IndependentReusedAuthor3
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource OUQuadraticDynkinSource
open OUConditionalInnovationSource OUTransitionKernelSource OUSemigroupSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory
#check actualOU_hasLaw
#check original_ouLaw_eq_transitionKernel
#check semigroup_add
#print axioms actualOU_hasLaw
#print axioms semigroup_add
#print axioms semigroup_zero
#print axioms original_ouLaw_eq_transitionKernel
example : semigroup 1 2 (1+2) Real.sin 3 = semigroup 1 2 1 (semigroup 1 2 2 Real.sin) 3 :=
  semigroup_add 1 2 (by norm_num) 1 2 Real.sin Real.measurable_sin 1
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x) 3
example (x : ℝ) : semigroup 1 2 0 Real.sin x=Real.sin x :=
  semigroup_zero 1 2 Real.sin Real.measurable_sin x
example (t : ℝ≥0) : ouLaw sourceLaw process 1 2 3 (t : ℝ)=transitionKernel 1 2 0 t 3 :=
  original_ouLaw_eq_transitionKernel 1 2 3 t
example : 0 < (transitionVariance 1 2 1 2 : ℝ) := same_source_positive_transition
example (t : ℝ≥0) : Integrable (fun ω => Real.sin (actualOU 1 2 3 t ω)) sourceLaw :=
  actualOU_test_integrable 1 2 3 t Real.sin Real.measurable_sin 1
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
/-- A discontinuous Borel observable: the theorem is not only a continuous-test identity. -/
example (s t : ℝ≥0) (x : ℝ) :
    semigroup 1 2 (s+t) ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) x =
      semigroup 1 2 s (semigroup 1 2 t ((Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)))) x := by
  apply semigroup_add 1 2 (by norm_num) s t _ (measurable_const.indicator measurableSet_Ioi) 1 _ x
  intro y
  by_cases hy : y ∈ Ioi (0 : ℝ)
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]
end IndependentReusedAuthor3

namespace IndependentActualSourceDiscriminators
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource OUQuadraticDynkinSource
open OUConditionalInnovationSource OUTransitionKernelSource OUSemigroupSource
open scoped NNReal Topology ProbabilityTheory MeasureTheory
-- All initial states use the EXACT old source, not a replacement Gaussian law.
example (k σ x₀ : ℝ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : actualOU k σ x₀ t ω = ouSource process k σ x₀ t ω := rfl
example (k : ℝ) (hk : 0 < k) (t : ℝ≥0) : ouFiltration k hk t =
    BrownianMartingaleSource.naturalFiltration (ouClock k t) := rfl
-- The time-change can actually see past physical time1: it is NOT a grant of F1 access.
theorem actual_clock_beyond_physical_one : (1 : ℝ) < (ouClock 1 1 : ℝ) := by
  rw [ouClock_coe 1 (by norm_num) 1]
  norm_num only [mul_one,NNReal.coe_one]
  have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
  linarith
noncomputable def closedHalf := (Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ))
private theorem closedHalf_meas : Measurable closedHalf := measurable_const.indicator measurableSet_Iic
private theorem closedHalf_bound (x : ℝ) : ‖closedHalf x‖ ≤ 1 := by
  by_cases hx : x ∈ Iic (0 : ℝ) <;> simp [closedHalf,hx]
-- Actual random-current-state conditional kernel for a discontinuous Borel test.
theorem actual_state_indicator_conditional (x₀ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[fun ω => closedHalf (actualOU 1 2 x₀ t ω) | ouFiltration 1 (by norm_num) s] =ᵐ[sourceLaw]
      fun ω => ∫ y, closedHalf y ∂transitionKernel 1 2 s t (actualOU 1 2 x₀ s ω) :=
  actualOU_condExp_kernel 1 2 x₀ (by norm_num) s t hst closedHalf closedHalf_meas 1 closedHalf_bound
-- ALL supplied initial x, discontinuous Borel observable, zero identity at its jump.
theorem all_initial_indicator_semigroup (x : ℝ) (s t : ℝ≥0) :
    semigroup 1 2 (s+t) closedHalf x = semigroup 1 2 s (semigroup 1 2 t closedHalf) x :=
  semigroup_add 1 2 (by norm_num) s t closedHalf closedHalf_meas 1 closedHalf_bound x
example : semigroup 1 2 0 closedHalf 0 = 1 := by
  rw [semigroup_zero 1 2 closedHalf closedHalf_meas]
  simp [closedHalf]
example : semigroup 1 2 0 closedHalf 1 = 0 := by
  rw [semigroup_zero 1 2 closedHalf closedHalf_meas]
  simp [closedHalf]
example (x : ℝ) (t : ℝ≥0) : ouLaw sourceLaw process 1 2 x (t : ℝ) = transitionKernel 1 2 0 t x :=
  original_ouLaw_eq_transitionKernel 1 2 x t
#print axioms actual_clock_beyond_physical_one
#print axioms actual_state_indicator_conditional
#print axioms all_initial_indicator_semigroup
end IndependentActualSourceDiscriminators
