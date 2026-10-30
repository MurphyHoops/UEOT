import UEOT
namespace NonAuthorBoundedDriftReview
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralClosure
open BrownianVectorIntegralConditionalSource BrownianVectorIntegralContinuousVersion BrownianVectorFiniteStateCrossQV
open BrownianFiniteStateTaylorRemainder BrownianFiniteStateItoSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
-- Independently constructed inputs: two independent coordinate unit records.
def unitH (j k : Fin 2) (_ω : Sample 2) : ℝ := if k=j then 1 else 0
theorem unit_past (j k : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 0] (unitH j k) := by
  unfold unitH
  exact stronglyMeasurable_const
theorem unit_top (j k : Fin 2) : MemLp (unitH j k) ∞ (productLaw 2) := by
  unfold unitH
  exact memLp_top_const _
def unit (T : ℝ≥0) (j : Fin 2) : fullPredictableL2 2 T :=
  BrownianVectorIntegralConditionalSource.intervalInput 2 T 0 T (by exact bot_le) le_rfl (unitH j) (unit_past j) (unit_top j)
theorem unit_input (T : ℝ≥0) (j : Fin 2) : (unit T j : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T))=ᵐ[inputLaw 2 T]
    fun _ => EuclideanSpace.single j 1 := by
  filter_upwards [BrownianVectorIntegralConditionalSource.intervalInput_coe 2 T 0 T (by exact bot_le) le_rfl (unitH j) (unit_past j) (unit_top j),
    time_support_ae 2 T] with p hp ht
  change (unit T j : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T)) p=_ at hp
  rw [hp]
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext k
  simp [BrownianVectorTimeInput.intervalInput_apply,unitH,ht]
theorem unit_integral (T : ℝ≥0) (j : Fin 2) : (predictableIntegral 2 T (unit T j) : Sample 2→ℝ)=ᵐ[productLaw 2]
    coordinateIncrement 2 j 0 T := by
  rw [unit,integral_interval_literal]
  apply (oneStep_memLp_two (unit_top j) 0 T).coeFn_toLp.trans
  exact Eventually.of_forall (fun ω => by
    fin_cases j <;> simp [oneStep,component,unitH])
-- Full rank triangular state: X0=dB0; X1=dB0+2*dB1. Both original independent unit inputs are consumed.
def family (T : ℝ≥0) : Fin 2→fullPredictableL2 2 T := ![unit T 0,unit T 0+(2 : ℝ) • unit T 1]
def triangular (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0,x 0+2*x 1]
theorem triangular_injective : Function.Injective triangular := by
  intro x y h
  have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
  have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h
  change x 0=y 0 at h0
  change x 0+2*x 1=y 0+2*y 1 at h1
  ext i
  fin_cases i
  · exact h0
  · change x (1 : Fin 2)=y (1 : Fin 2)
    linarith
-- The returned ACTUAL state, not merely a formal coefficient matrix, is this injective image of the genuine independent source increments.
theorem actual_state (T : ℝ≥0) : ∀ᵐ ω ∂productLaw 2,
    stateProcess 2 T (family T) T ω 0=coordinateIncrement 2 0 0 T ω ∧
    stateProcess 2 T (family T) T ω 1=coordinateIncrement 2 0 0 T ω+2*coordinateIncrement 2 1 0 T ω := by
  have hm : predictableIntegral 2 T (family T 1)=predictableIntegral 2 T (unit T 0)+(2 : ℝ) • predictableIntegral 2 T (unit T 1) := by
    change predictableIntegral 2 T (unit T 0+(2 : ℝ) • unit T 1)=_
    rw [map_add,map_smul]
  have hc := Lp.coeFn_add (predictableIntegral 2 T (unit T 0)) ((2 : ℝ) • predictableIntegral 2 T (unit T 1))
  rw [← hm] at hc
  filter_upwards [continuousIntegralProcess_horizon 2 T (family T 0),continuousIntegralProcess_horizon 2 T (family T 1),
    unit_integral T 0,unit_integral T 1,hc,Lp.coeFn_smul (2 : ℝ) (predictableIntegral 2 T (unit T 1))] with ω h0 h1 hu0 hu1 ha hs
  constructor
  · change continuousIntegralProcess 2 T (unit T 0) T ω=_
    exact h0.trans hu0
  · change continuousIntegralProcess 2 T (family T 1) T ω=_
    rw [h1,ha]
    simp only [Pi.add_apply] at *
    simp only [Pi.smul_apply,smul_eq_mul] at hs
    rw [hs,hu0,hu1]

def originalIncrements (T : ℝ≥0) (ω : Sample 2) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j => coordinateIncrement 2 j 0 T ω)
theorem actual_state_full_rank_image (T : ℝ≥0) : stateProcess 2 T (family T) T=ᵐ[productLaw 2]
    fun ω => triangular (originalIncrements T ω) := by
  filter_upwards [actual_state T] with ω h
  ext j
  fin_cases j
  · exact h.1
  · exact h.2
example (T : ℝ≥0) : iIndepFun (fun j : Fin 2 => coordinateIncrement 2 j 0 T) (productLaw 2) :=
  coordinateIncrements_independent 2 0 T

open BrownianVectorIntegralTimeEnergy BrownianVectorCrossPartitionQV BrownianVectorIntegralTimeSource
-- Native actual family has NONZERO cross energy, so its mixed Hessian is not killed by an orthogonal or collinear test input.
theorem mixed_input (T : ℝ≥0) : (family T 1 : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T))=ᵐ[inputLaw 2 T]
    fun _ => EuclideanSpace.single (0 : Fin 2) 1+(2 : ℝ) • EuclideanSpace.single (1 : Fin 2) 1 := by
  have hc := Lp.coeFn_add (unit T 0 : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T))
    ((2 : ℝ) • (unit T 1 : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T)))
  filter_upwards [hc,Lp.coeFn_smul (2 : ℝ) (unit T 1 : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T)),unit_input T 0,unit_input T 1]
    with p hc hs h0 h1
  change ((unit T 0 : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T))+(2 : ℝ) • (unit T 1 : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T))) p=_
  rw [hc]
  simp only [Pi.add_apply,Pi.smul_apply] at *
  rw [hs,h0,h1]
theorem actual_cross_energy (T : ℝ≥0) : crossTimeEnergy 2 T (family T 0) (family T 1) T=ᵐ[productLaw 2] fun _ => (T : ℝ) := by
  have he : crossEnergyIntegrand 2 T T (family T 0) (family T 1)=ᵐ[inputLaw 2 T] fun _ => (1 : ℝ) := by
    filter_upwards [time_support_ae 2 T,representative_ae 2 T (family T 0),representative_ae 2 T (family T 1),unit_input T 0,mixed_input T]
      with p ht hr0 hr1 h0 h1
    have hm : p∈BrownianVectorIntegralTimeSource.timeSet 2 T T := by
      simpa only [BrownianVectorIntegralTimeSource.timeSet,min_self,mem_prod,mem_univ,and_true] using ht
    rw [crossEnergyIntegrand,Set.indicator_of_mem hm,← hr0,← hr1]
    change inner ℝ ((unit T 0 : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T)) p)
      ((family T 1 : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T)) p)=1
    rw [h0,h1]
    simp [EuclideanSpace.inner_single_left]
  have hs : ∀ᵐ ω ∂productLaw 2, (fun t => crossEnergyIntegrand 2 T T (family T 0) (family T 1) (t,ω))=ᵐ[BrownianTimeIntegrand.timeLaw T]
      fun _ => (1 : ℝ) :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := productLaw 2) (ν := BrownianTimeIntegrand.timeLaw T)).quasiMeasurePreserving.ae he)
  filter_upwards [hs] with ω h
  unfold crossTimeEnergy
  rw [integral_congr_ae h]
  simp [BrownianTimeIntegrand.timeLaw,Measure.real,Real.volume_Icc]

open BrownianFiniteStateDriftSource BrownianFiniteStateDriftRiemann BrownianFiniteStateDriftCrossQV BrownianFiniteStateDriftItoSource
open BrownianFiniteStateTaylorRemainder BrownianFiniteStateItoSource
local notation "E" => EuclideanSpace ℝ (Fin 2)
-- New two-channel drift: jumps at0/1/2/4, without a beta continuity assumption.
def pulse (a b : ℝ≥0) (j : Fin 2) : ℝ×Sample 2→E :=
  (Ioc (a : ℝ) b×ˢ univ).indicator (fun _=>basisVector j)
theorem pulse_predictable (a b : ℝ≥0) (j : Fin 2) : StronglyMeasurable[predictableSigma 2] (pulse a b j) :=
  stronglyMeasurable_const.indicator (predictable_interval_rectangle 2 a b MeasurableSet.univ)
theorem pulse_bound (a b : ℝ≥0) (j : Fin 2) (p : ℝ×Sample 2) : ‖pulse a b j p‖≤(1 : ℝ) := by
  exact (norm_indicator_le_norm_self _ _).trans (by simp[basisVector_norm])
def beta : ℝ×Sample 2→E := pulse 2 4 0-pulse 0 1 1
theorem beta_predictable : StronglyMeasurable[predictableSigma 2] beta := (pulse_predictable 2 4 0).sub (pulse_predictable 0 1 1)
theorem beta_bound (p : ℝ×Sample 2) : ‖beta p‖≤(2 : ℝ≥0) := by
  calc _ ≤ ‖pulse 2 4 0 p‖+‖pulse 0 1 1 p‖ := norm_sub_le _ _
       _ ≤ 1+1 := add_le_add (pulse_bound _ _ _ p) (pulse_bound _ _ _ p)
       _ = _ := by norm_num
example (ω : Sample 2) : beta ((1/2 : ℝ),ω)=-basisVector 1 := by norm_num[beta,pulse]
example (ω : Sample 2) : beta ((3 : ℝ),ω)=basisVector 0 := by norm_num[beta,pulse]
def initial : E := (-3 : ℝ) • basisVector 0+basisVector 1
-- Every raw-sample actual primitive, not a table of beta rates.
theorem actual_drift_terminal (ω : Sample 2) : drift 2 4 beta 4 ω=(2 : ℝ) • basisVector 0-basisVector 1 := by
  rw[drift_primitive,min_self]
  have h0:=beta_intervalIntegrable 2 (pulse 2 4 0) (pulse_predictable _ _ _) 1 (pulse_bound _ _ _) ω 0 4
  have h1:=beta_intervalIntegrable 2 (pulse 0 1 1) (pulse_predictable _ _ _) 1 (pulse_bound _ _ _) ω 0 4
  change (∫t in (0 : ℝ)..4,pulse 2 4 0 (t,ω)-pulse 0 1 1 (t,ω))=_
  rw[intervalIntegral.integral_sub h0 h1,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤4),intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤4)]
  have hp (a b : ℝ≥0) (j : Fin 2) : (fun t=>pulse a b j (t,ω))=(Ioc (a : ℝ) b).indicator (fun _=>basisVector j) := by
    funext t
    by_cases h : t∈Ioc (a : ℝ) b <;> simp[pulse,h]
  rw[hp,hp,integral_indicator measurableSet_Ioc,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
  norm_num [Set.Ioc_inter_Ioc,integral_const,Measure.real,Real.volume_Ioc]
-- The actual state, with full-rank triangular noise and nonzero initial/drift, is explicitly bound.
example : ∀ᵐ ω ∂productLaw 2,state 2 4 initial beta (family 4) 4 ω=
    initial+((2 : ℝ) • basisVector 0-basisVector 1)+triangular (originalIncrements 4 ω) := by
  filter_upwards [actual_state_full_rank_image 4] with ω h
  rw[state,actual_drift_terminal,h]
example : state 2 4 initial beta (family 4) 0=ᵐ[productLaw 2] fun _=>initial := state_initial _ _ _ _ _
-- Independent cosine derivative proofs, a mixed nonlinear test with both Hessian indices active.
def L : E→L[ℝ] ℝ := EuclideanSpace.proj (𝕜:=ℝ) 0-(2 : ℝ) • EuclideanSpace.proj (𝕜:=ℝ) 1
def phi (x : E) : ℝ := Real.cos (L x)
theorem phi_C2 : ContDiff ℝ 2 phi := Real.contDiff_cos.comp L.contDiff
theorem phi_D (x : E) : fderiv ℝ phi x=(-Real.sin (L x)) • L := L.hasFDerivAt.cos.fderiv
theorem phi_DD (x : E) : hessian phi x=((-Real.cos (L x)) • L).smulRight L := by
  unfold hessian
  rw[show fderiv ℝ phi=(fun y=>(-Real.sin (L y)) • L) from funext phi_D]
  rw[show (-Real.cos (L x)) • L=-(Real.cos (L x) • L) from neg_smul (Real.cos (L x)) L]
  exact ((L.hasFDerivAt (x:=x)).sin.neg.smul_const L).fderiv
theorem phi_D_bound (x : E) : ‖fderiv ℝ phi x‖≤‖L‖ := by
  rw[phi_D,norm_smul,norm_neg]
  exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg _)).trans_eq (one_mul _)
theorem phi_DD_bound (x : E) : ‖hessian phi x‖≤‖L‖^2 := by
  rw[phi_DD,ContinuousLinearMap.norm_smulRight_apply,norm_smul,norm_neg]
  calc _ ≤ 1*‖L‖*‖L‖ := by gcongr;exact Real.abs_cos_le_one _
       _ = _ := by ring
example : hessianEntry phi (0 : Fin 2) 1 0=2 := by
  have h0 : L (basisVector (0 : Fin 2))=1 := by simp[L,basisVector]
  have h1 : L (basisVector (1 : Fin 2))=-2 := by simp[L,basisVector]
  simp only[hessianEntry,phi_DD,map_zero,Real.cos_zero,neg_mul,ContinuousLinearMap.smulRight_apply,
    smul_apply,smul_eq_mul,h0,h1]
  norm_num
-- SAME full Y / actual beta dt / exact gradient-generated returned native input.
example : (fun ω=>phi (state 2 4 initial beta (family 4) 4 ω))=ᵐ[productLaw 2] fun ω=>phi initial+
    continuousIntegralProcess 2 4 (driftItoInput 2 4 initial beta beta_predictable 2 beta_bound (family 4) phi phi_C2 ‖L‖₊ phi_D_bound) 4 ω+
    (∫t in (0 : ℝ)..4,fderiv ℝ phi (state 2 4 initial beta (family 4) (Real.toNNReal t) ω) (beta (t,ω)))+
    (1/2 : ℝ)*driftSecondEnergy 2 4 initial beta (family 4) phi ω :=
  actual_drift_state_ito_integral 2 4 initial beta beta_predictable 2 beta_bound (family 4) phi phi_C2 ‖L‖₊ (‖L‖₊^2) phi_D_bound (by simpa using phi_DD_bound)
example : (driftItoInput 2 4 initial beta beta_predictable 2 beta_bound (family 4) phi phi_C2 ‖L‖₊ phi_D_bound :
    Lp E 2 (inputLaw 2 4))=ᵐ[inputLaw 2 4] fun p=>∑ j,gradientEntry phi j
      (state 2 4 initial beta (family 4) (Real.toNNReal p.1) p.2) • (family 4 j : Lp E 2 (inputLaw 2 4)) p :=
  driftItoInput_coe 2 4 initial beta beta_predictable 2 beta_bound (family 4) phi phi_C2 ‖L‖₊ phi_D_bound
example (ω : Sample 2) : driftFirstEnergy 2 4 initial beta (family 4) phi ω=
    ∫t in (0 : ℝ)..4,fderiv ℝ phi (state 2 4 initial beta (family 4) (Real.toNNReal t) ω) (beta (t,ω)) :=
  driftFirstEnergy_eq_integral 2 4 initial beta beta_predictable 2 beta_bound (family 4) phi phi_C2 ‖L‖₊ phi_D_bound ω
example (ω : Sample 2) : phi (state 2 4 initial beta (family 4) 4 ω)-phi (state 2 4 initial beta (family 4) 0 ω)=
    firstSum phi ![0,2,2,4] (fun u=>state 2 4 initial beta (family 4) u ω)+
    (1/2 : ℝ)*secondSum phi ![0,2,2,4] (fun u=>state 2 4 initial beta (family 4) u ω)+
    remainderSum phi ![0,2,2,4] (fun u=>state 2 4 initial beta (family 4) u ω) :=
  finite_taylor_telescope phi ![0,2,2,4] (fun u=>state 2 4 initial beta (family 4) u ω)
example : state 2 0 initial beta (family 0) 0=ᵐ[productLaw 2] fun _=>initial := state_initial _ _ _ _ _
example : (fun ω=>phi (state 2 0 initial beta (family 0) 0 ω))=ᵐ[productLaw 2] fun ω=>phi initial+
    continuousIntegralProcess 2 0 (driftItoInput 2 0 initial beta beta_predictable 2 beta_bound (family 0) phi phi_C2 ‖L‖₊ phi_D_bound) 0 ω+
    (∫t in (0 : ℝ)..0,fderiv ℝ phi (state 2 0 initial beta (family 0) (Real.toNNReal t) ω) (beta (t,ω)))+
    (1/2 : ℝ)*driftSecondEnergy 2 0 initial beta (family 0) phi ω :=
  actual_drift_state_ito_integral 2 0 initial beta beta_predictable 2 beta_bound (family 0) phi phi_C2 ‖L‖₊ (‖L‖₊^2) phi_D_bound (by simpa using phi_DD_bound)
example (n : ℕ) : (∑ i : Fin (n+1),PredictableDriftPointSamplingCounterexample.rate (BrownianQuadraticVariation.uniformClock 1 n i.castSucc)*
    ((BrownianQuadraticVariation.uniformClock 1 n i.succ : ℝ)-(BrownianQuadraticVariation.uniformClock 1 n i.castSucc : ℝ)))≠
    ∫t in (0 : ℝ)..1,PredictableDriftPointSamplingCounterexample.rate t := PredictableDriftPointSamplingCounterexample.point_sampling_is_not_actual_drift n
-- Actual primitive-weight Riemann convergence; beta itself is not point sampled.
example : ∀ᵐ ω ∂productLaw 2,Tendsto
    (fun n=>weightedDriftSum 2 4 beta (BrownianQuadraticVariation.uniformClock 4 n)
      (fun u=>phi (state 2 4 initial beta (family 4) u ω)) ω) atTop
    (𝓝 (∫t in (0 : ℝ)..4,phi (state 2 4 initial beta (family 4) (Real.toNNReal t) ω) • beta (t,ω))) :=
  functionOfState_weightedDriftSum_tendsto 2 4 (fun n=>n+1) (BrownianQuadraticVariation.uniformClock 4)
    (BrownianQuadraticVariation.uniformClock_mono 4) (BrownianQuadraticVariation.uniformClock_zero 4)
    (BrownianQuadraticVariation.uniformClock_end 4) (BrownianQuadraticVariation.uniformClock_mesh_tendsto 4)
    initial beta beta_predictable 2 beta_bound (family 4) phi phi_C2.continuous 1 (fun _x=>Real.abs_cos_le_one _)
example : TendstoInMeasure (productLaw 2)
    (fun n=>weightedStateCrossSum 2 4 (BrownianQuadraticVariation.uniformClock 4 n) (fun _ _=>1)
      initial beta (family 4) 0 1) atTop
    (BrownianVectorWeightedCrossQV.weightedTimeEnergy 2 4 (fun _ _=>1) (family 4 0) (family 4 1)) :=
  weightedStateCross_QV_tendstoInMeasure 2 4 (fun n=>n+1) (BrownianQuadraticVariation.uniformClock 4)
    (BrownianQuadraticVariation.uniformClock_mono 4) (BrownianQuadraticVariation.uniformClock_zero 4)
    (BrownianQuadraticVariation.uniformClock_end 4) (BrownianQuadraticVariation.uniformClock_mesh_tendsto 4)
    (fun _ _=>1) measurable_const (fun _=>stronglyMeasurable_const) (ae_of_all _ (fun _=>continuous_const))
    1 (fun _ _=>by norm_num) initial beta beta_predictable 2 beta_bound (family 4) 0 1
example : (∫t in (0 : ℝ)..1,PredictableDriftPointSamplingCounterexample.rate t)=0 := PredictableDriftPointSamplingCounterexample.actual_integral_zero
example : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (BrownianQuadraticVariation.uniformClock 1 n) : ℝ)) atTop (𝓝 0) :=
  BrownianQuadraticVariation.uniformClock_mesh_tendsto 1
#print axioms beta_predictable
#print axioms actual_drift_terminal
#print axioms phi_DD
#print axioms actual_drift_state_ito_integral
#print axioms driftItoInput_coe
#print axioms actual_cross_energy
#print axioms triangular_injective
end
end NonAuthorBoundedDriftReview
