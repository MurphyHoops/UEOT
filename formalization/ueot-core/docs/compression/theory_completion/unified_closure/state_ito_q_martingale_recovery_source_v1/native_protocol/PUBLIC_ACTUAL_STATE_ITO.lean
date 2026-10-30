import UEOT
namespace NonAuthorFullRankStateReview
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

-- Reuse only the author's GENERAL native linear-sine analytic helper proofs, as expressly authorized; family/state and consumers above/below are new.
namespace Observable
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
def phi (L : E→L[ℝ] ℝ) (x : E) : ℝ := Real.sin (L x)
theorem C2 (L : E→L[ℝ] ℝ) : ContDiff ℝ 2 (phi L) := Real.contDiff_sin.comp L.contDiff
theorem D (L : E→L[ℝ] ℝ) (x : E) : fderiv ℝ (phi L) x=Real.cos (L x) • L := L.hasFDerivAt.sin.fderiv
theorem DD (L : E→L[ℝ] ℝ) (x : E) : hessian (phi L) x=((-Real.sin (L x)) • L).smulRight L := by
  unfold hessian
  rw [show fderiv ℝ (phi L)=(fun y=>Real.cos (L y) • L) from funext (D L)]
  exact (L.hasFDerivAt.cos.smul_const L).fderiv
theorem Db (L : E→L[ℝ] ℝ) (x : E) : ‖fderiv ℝ (phi L) x‖≤‖L‖ := by
  rw [D,norm_smul]
  calc _ ≤ 1*‖L‖ := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)
       _ = _ := one_mul _
theorem DDb (L : E→L[ℝ] ℝ) (x : E) : ‖hessian (phi L) x‖≤‖L‖^2 := by
  rw [DD,ContinuousLinearMap.norm_smulRight_apply,norm_smul,norm_neg]
  calc _ ≤ 1*‖L‖*‖L‖ := by gcongr; exact Real.abs_sin_le_one _
       _ = _ := by ring
end Observable
-- Nonlinear mixed Hessian with two independent state directions, not the author's collinear [f,2f,-f].
def L : EuclideanSpace ℝ (Fin 2)→L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) 0+EuclideanSpace.proj (𝕜 := ℝ) 1
example : hessianEntry (Observable.phi L) (0 : Fin 2) 1 ((Real.pi/2) • basisVector (0 : Fin 2)) = -1 := by
  have h0 : L (basisVector (0 : Fin 2))=1 := by simp [L,basisVector]
  have h1 : L (basisVector (1 : Fin 2))=1 := by simp [L,basisVector]
  have hx : L ((Real.pi/2) • basisVector (0 : Fin 2))=Real.pi/2 := by rw [map_smul,h0]; simp
  simp only [hessianEntry,Observable.DD,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul,hx,Real.sin_pi_div_two,h0,h1,mul_one]
example (T : ℝ≥0) : (fun ω => Observable.phi L (stateProcess 2 T (family T) T ω))=ᵐ[productLaw 2] fun ω =>
    Observable.phi L 0+continuousIntegralProcess 2 T (itoInput 2 T (family T) (Observable.phi L) (Observable.C2 L) ‖L‖ (Observable.Db L)) T ω+
      (1/2 : ℝ)*itoSecondEnergy 2 T (family T) (Observable.phi L) ω :=
  actual_state_ito 2 T (family T) (Observable.phi L) (Observable.C2 L) ‖L‖ (‖L‖^2) (Observable.Db L) (Observable.DDb L)
example (T : ℝ≥0) : (itoInput 2 T (family T) (Observable.phi L) (Observable.C2 L) ‖L‖ (Observable.Db L) :
    Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T))=ᵐ[inputLaw 2 T] fun p =>
      ∑ j,gradientEntry (Observable.phi L) j (stateProcess 2 T (family T) (Real.toNNReal p.1) p.2) •
        (family T j : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 T)) p :=
  itoInput_coe 2 T (family T) (Observable.phi L) (Observable.C2 L) ‖L‖ (Observable.Db L)
example (ω : Sample 2) : Observable.phi L (stateProcess 2 4 (family 4) 4 ω)-Observable.phi L (stateProcess 2 4 (family 4) 0 ω)=
    firstSum (Observable.phi L) ![0,1,1,4] (fun u=>stateProcess 2 4 (family 4) u ω)+
      (1/2 : ℝ)*secondSum (Observable.phi L) ![0,1,1,4] (fun u=>stateProcess 2 4 (family 4) u ω)+
        remainderSum (Observable.phi L) ![0,1,1,4] (fun u=>stateProcess 2 4 (family 4) u ω) :=
  finite_taylor_telescope (Observable.phi L) ![0,1,1,4] (fun u=>stateProcess 2 4 (family 4) u ω)
-- Taylor theorem genuinely needs ONLY C2: this mixed quadratic has no global gradient bound.
def quadratic (x : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0*x 1
example : TendstoInMeasure (productLaw 2)
    (fun n ω => remainderSum quadratic (BrownianQuadraticVariation.uniformClock 4 n) (fun u => stateProcess 2 4 (family 4) u ω)) atTop
    (fun _ => (0 : ℝ)) :=
  actual_remainderSum_tendstoInMeasure 2 4 (family 4) quadratic (by unfold quadratic; fun_prop)
    (fun n => n+1) (BrownianQuadraticVariation.uniformClock 4)
    (BrownianQuadraticVariation.uniformClock_mono 4) (BrownianQuadraticVariation.uniformClock_zero 4)
    (BrownianQuadraticVariation.uniformClock_end 4) (BrownianQuadraticVariation.uniformClock_mesh_tendsto 4)
example (x : EuclideanSpace ℝ (Fin 2)) : cellRatio (Observable.phi L) x x=0 := by simp [cellRatio,secondRemainder]
-- Explicit source boundary: same nonzero noise dimension at zero horizon; no Ito initial offset or new state is introduced.
example : (fun ω => Observable.phi L (stateProcess 2 0 (family 0) 0 ω))=ᵐ[productLaw 2] fun ω =>
    Observable.phi L 0+continuousIntegralProcess 2 0 (itoInput 2 0 (family 0) (Observable.phi L) (Observable.C2 L) ‖L‖ (Observable.Db L)) 0 ω+
      (1/2 : ℝ)*itoSecondEnergy 2 0 (family 0) (Observable.phi L) ω :=
  actual_state_ito 2 0 (family 0) (Observable.phi L) (Observable.C2 L) ‖L‖ (‖L‖^2) (Observable.Db L) (Observable.DDb L)
#print axioms actual_state_ito
#print axioms actual_remainderSum_tendstoInMeasure
#print axioms actual_state
#print axioms actual_state_full_rank_image
#print axioms actual_cross_energy
#print axioms triangular_injective
end
end NonAuthorFullRankStateReview
