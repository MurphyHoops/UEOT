import UEOT
namespace IndependentWeightedCrossConsumer
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralClosure
open BrownianVectorIntegralTimeSource BrownianVectorIntegralConditionalSource BrownianVectorIntegralContinuousVersion
open BrownianVectorIntegralGridL1
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




def f : fullPredictableL2 2 3 := intervalInput 2 3 1 2 (by norm_num) (by norm_num)
  (rotating 1) (rotating_past 1) (rotating_bounded 1)
open BrownianVectorFiniteStateCrossQV BrownianVectorPredictableMultiplier
def family : Fin 2 → fullPredictableL2 2 3 := ![f,(-3 : ℝ) • f]
def F (x : EuclideanSpace ℝ (Fin 2)) : ℝ := Real.sin (x 0) * Real.cos (x 1)
theorem F_continuous : Continuous F :=
  (Real.continuous_sin.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous).mul
    (Real.continuous_cos.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
theorem F_bound (x : EuclideanSpace ℝ (Fin 2)) : ‖F x‖ ≤ 1 := by
  change |Real.sin (x 0) * Real.cos (x 1)| ≤ 1
  rw [abs_mul]
  nlinarith [Real.abs_sin_le_one (x 0),Real.abs_cos_le_one (x 1),abs_nonneg (Real.sin (x 0)),abs_nonneg (Real.cos (x 1))]
def g : fullPredictableL2 2 3 := functionOfStateInput 2 3 family F F_continuous 1 F_bound f
open BrownianVectorPastMultiplierBinding BrownianVectorLeftMultiplierBinding
open BrownianQuadraticVariation (mesh uniformClock uniformClock_mono uniformClock_zero uniformClock_end uniformClock_mesh_tendsto)
open BrownianVectorWeightedCrossQV
-- Actual nonlinear weight on the SAME finite state and SAME supplied f/(-3f).
example : TendstoInMeasure (productLaw 2) (fun n=>weightedCrossSum 2 3 (uniformClock 3 n)
      (fun u ω=>F (stateProcess 2 3 family u ω)) f ((-3 : ℝ) • f)) atTop
    (BrownianVectorWeightedCrossQV.weightedTimeEnergy 2 3 (fun u ω=>F (stateProcess 2 3 family u ω)) f ((-3 : ℝ) • f)) :=
  functionOfState_weightedCross_QV_tendstoInMeasure 2 3 (fun n=>n+1) (uniformClock 3) (uniformClock_mono 3)
    (uniformClock_zero 3) (uniformClock_end 3) (uniformClock_mesh_tendsto 3) family F F_continuous 1 F_bound f ((-3 : ℝ) • f)
-- Each Hessian-style coordinate pair is on the same ORIGINAL state, without approximate-state replacement.
example (j k : Fin 2) : TendstoInMeasure (productLaw 2) (fun n=>weightedCrossSum 2 3 (uniformClock 3 n)
      (fun u ω=>F (stateProcess 2 3 family u ω)) (family j) (family k)) atTop
    (BrownianVectorWeightedCrossQV.weightedTimeEnergy 2 3 (fun u ω=>F (stateProcess 2 3 family u ω)) (family j) (family k)) :=
  functionOfState_weightedCross_QV_tendstoInMeasure 2 3 (fun n=>n+1) (uniformClock 3) (uniformClock_mono 3)
    (uniformClock_zero 3) (uniformClock_end 3) (uniformClock_mesh_tendsto 3) family F F_continuous 1 F_bound _ _
-- Constructed sampled-input increments are truly ORIGINAL H_START times SAME original Mf increment.
example (i : Fin 3) :
    (fun ω=>continuousIntegralProcess 2 3 (sampledMultiplier 2 3 ![0,1,1,3]
      (by intro j k hjk; fin_cases j <;> fin_cases k <;> simp_all)
      (fun u ω=>F (stateProcess 2 3 family u ω))
      (fun u=>F_continuous.comp_stronglyMeasurable (stateProcess_stronglyAdapted 2 3 family u))
      1 (by norm_num) (fun _ _=>F_bound _) f) (![0,1,1,3] i.succ) ω-
      continuousIntegralProcess 2 3 (sampledMultiplier 2 3 ![0,1,1,3]
      (by intro j k hjk; fin_cases j <;> fin_cases k <;> simp_all)
      (fun u ω=>F (stateProcess 2 3 family u ω))
      (fun u=>F_continuous.comp_stronglyMeasurable (stateProcess_stronglyAdapted 2 3 family u))
      1 (by norm_num) (fun _ _=>F_bound _) f) (![0,1,1,3] i.castSucc) ω) =ᵐ[productLaw 2]
      fun ω=>F (stateProcess 2 3 family (![0,1,1,3] i.castSucc) ω)*
        (continuousIntegralProcess 2 3 f (![0,1,1,3] i.succ) ω-continuousIntegralProcess 2 3 f (![0,1,1,3] i.castSucc) ω) :=
  sampledProcess_cell_increment 2 3 _ _ _ _ 1 (by norm_num) _ f i
-- Actual repeated cell contributes zero to the observed weighted CROSS sum.
example (ω : Sample 2) : weightedCrossSum 2 3 ![0,1,1,3] (fun u ω=>F (stateProcess 2 3 family u ω)) f ((-3 : ℝ) • f) ω =
    F (stateProcess 2 3 family 0 ω)*(continuousIntegralProcess 2 3 f 1 ω-continuousIntegralProcess 2 3 f 0 ω)*
      (continuousIntegralProcess 2 3 ((-3 : ℝ) • f) 1 ω-continuousIntegralProcess 2 3 ((-3 : ℝ) • f) 0 ω)+
    F (stateProcess 2 3 family 1 ω)*(continuousIntegralProcess 2 3 f 3 ω-continuousIntegralProcess 2 3 f 1 ω)*
      (continuousIntegralProcess 2 3 ((-3 : ℝ) • f) 3 ω-continuousIntegralProcess 2 3 ((-3 : ℝ) • f) 1 ω) := by
  simp [weightedCrossSum,Fin.sum_univ_succ]
-- Native L1 limit consumes actual varying original inputs, not a supplied weighted covariance.
example (d : ℕ) (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(mesh (τ n) : ℝ)) atTop (𝓝 0))
    (v : ℕ→fullPredictableL2 d T) (f g : fullPredictableL2 d T) (hv : Tendsto v atTop (𝓝 g)) :
    Tendsto (fun n=>BrownianVectorCrossPartitionQV.gridCross d T (τ n) f (v n)) atTop
      (𝓝 (BrownianVectorCrossPartitionQV.crossEnergyClass d T T f g)) :=
  partition_crossVariation_of_input_tendsto d T N τ hm h0 hT hmesh f v g hv
-- Zero noise/state/time and empty clock remain included by the actual theorem.
example (h : fullPredictableL2 0 0) : TendstoInMeasure (productLaw 0)
    (fun _n : ℕ=>weightedCrossSum 0 0 (fun _ : Fin 1=>0) (fun _ _=>1) h h) atTop
      (BrownianVectorWeightedCrossQV.weightedTimeEnergy 0 0 (fun _ _=>1) h h) := by
  apply functionOfState_weightedCross_QV_tendstoInMeasure 0 0 (fun _=>0) (fun _ _=>0)
    (fun _ _ _ _=>le_rfl) (fun _=>rfl) (fun _=>rfl) _ (fun _ : Fin 0=>h) (fun _=>1)
    continuous_const 1 (fun _=>by norm_num) h h
  have hz : mesh (fun _ : Fin 1=>(0 : ℝ≥0))=0 := by simp [mesh]
  simpa only [hz,NNReal.coe_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0 : ℝ)) atTop (𝓝 0))
#print axioms sampledProcess_cell_increment
#print axioms gridCross_sampled_coe
#print axioms weightedCross_QV_class_tendsto
#print axioms weightedCross_QV_tendstoInMeasure
#print axioms functionOfState_weightedCross_QV_tendstoInMeasure
end
end IndependentWeightedCrossConsumer
