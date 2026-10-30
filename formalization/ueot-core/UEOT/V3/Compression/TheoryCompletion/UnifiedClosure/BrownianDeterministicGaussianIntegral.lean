import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianGaussianL2Closure
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousAdaptedInputs
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralMartingale

/-!
Original commitment: physical OU must obtain Gaussian noise from SAME actual Brownian deterministic integral, not a postulated innovation law.
Existing result: actual causal left tables converge in native L2 and Gaussian-law L2 closure is derived by native characteristic functions/moments.
Premise reduced: derive Gaussian law/mean/actual dt second moment for the constructed native deterministic continuous bounded input and its SAME returned integral.
Model/witness: canonical B/sourceLaw/original Fs, any supplied continuous globally bounded deterministic weight, all finite integration horizons including zero.
Consumer/boundary: clipped exponential weight realizes physical OU stochastic convolution; Volterra/native integral identity, conditional innovation and original recovery remain subsequent source proofs.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianDeterministicGaussianIntegral
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianContinuousAdaptedInputs BrownianIntegralMartingale
open BrownianGaussianL2Closure BrownianOneStepIntegral BrownianSimplePredictableIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory RealInnerProductSpace
noncomputable section

def lifted (H : ℝ≥0→ℝ) (u : ℝ≥0) (_ω : ℝ≥0→ℝ) : ℝ := H u

theorem lifted_joint (H : ℝ≥0→ℝ) (hH : Continuous H) : Measurable (Function.uncurry (lifted H)) :=
  hH.measurable.comp measurable_fst

theorem lifted_adapted (H : ℝ≥0→ℝ) : StronglyAdapted naturalFiltration (lifted H) := fun _ => stronglyMeasurable_const

theorem lifted_continuous (H : ℝ≥0→ℝ) (hH : Continuous H) :
    ∀ᵐ ω ∂sourceLaw,Continuous (fun u => lifted H u ω) := Eventually.of_forall (fun _ => hH)

def input (T : ℝ≥0) (H : ℝ≥0→ℝ) (hH : Continuous H) (K : ℝ) (hK : 0≤K) (hb : ∀ u,‖H u‖≤K) : fullPredictableL2 T :=
  continuousPredictableInput T (lifted H) (lifted_joint H hH) (lifted_adapted H) (lifted_continuous H hH) K hK (fun u _ => hb u)

def integralValue (T : ℝ≥0) (H : ℝ≥0→ℝ) (hH : Continuous H) (K : ℝ) (hK : 0≤K) (hb : ∀ u,‖H u‖≤K) : Lp ℝ 2 sourceLaw :=
  predictableIntegral T (input T H hH K hK hb)

/-- Genuine finite Gaussian increments of the ACTUAL canonical source,
weighted by the supplied deterministic coefficients. No independent source. -/
theorem weighted_increments_gaussian {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (c : Fin n→ℝ) :
    HasGaussianLaw (fun ω => ∑ i : Fin n,c i*increment (τ i.castSucc) (τ i.succ) ω) sourceLaw := by
  let L : (Fin n→ℝ)→L[ℝ] ℝ := ∑ i : Fin n,c i • ContinuousLinearMap.proj i
  have h := process_isPreBrownian.isGaussianProcess.hasGaussianLaw_increments (t := τ)
  have hg := h.map L
  convert! hg using 1
  funext ω
  simp [L,increment,smul_eq_mul]

theorem left_outputs_gaussian (T : ℝ≥0) (H : ℝ≥0→ℝ) (K : ℝ) (hb : ∀ u,‖H u‖≤K) (n : ℕ) :
    HasGaussianLaw (outputValue (leftRecord T (lifted H) (lifted_adapted H) K (fun u _ => hb u) n) : (ℝ≥0→ℝ)→ℝ) sourceLaw := by
  let r := leftRecord T (lifted H) (lifted_adapted H) K (fun u _ => hb u) n
  have h : HasGaussianLaw (simpleIntegral r.clock r.coefficient) sourceLaw := by
    change HasGaussianLaw (fun ω => ∑ i : Fin (n+1),H (BrownianQuadraticVariation.uniformClock T n i.castSucc)*
      increment (BrownianQuadraticVariation.uniformClock T n i.castSucc) (BrownianQuadraticVariation.uniformClock T n i.succ) ω) sourceLaw
    exact weighted_increments_gaussian _ _
  exact h.congr (BrownianSimplePredictableIntegral.simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp.symm

/-- Actual native deterministic integral is Gaussian by ITS proved literal
left-output limits, not by an assumed Gaussian limit/source certificate. -/
theorem integralValue_gaussian (T : ℝ≥0) (H : ℝ≥0→ℝ) (hH : Continuous H) (K : ℝ) (hK : 0≤K) (hb : ∀ u,‖H u‖≤K) :
    HasGaussianLaw (integralValue T H hH K hK hb : (ℝ≥0→ℝ)→ℝ) sourceLaw :=
  hasGaussianLaw_of_tendsto sourceLaw
    (left_outputs_tendsto T (lifted H) (lifted_joint H hH) (lifted_adapted H) (lifted_continuous H hH) K hK (fun u _ => hb u))
    (left_outputs_gaussian T H K hb)

theorem input_coe (T : ℝ≥0) (H : ℝ≥0→ℝ) (hH : Continuous H) (K : ℝ) (hK : 0≤K) (hb : ∀ u,‖H u‖≤K) :
    (input T H hH K hK hb : Lp ℝ 2 (inputLaw T))=ᵐ[inputLaw T] fun p => H (Real.toNNReal p.1) :=
  continuousPredictableInput_coe T (lifted H) (lifted_joint H hH) (lifted_adapted H) (lifted_continuous H hH) K hK (fun u _ => hb u)

theorem integralValue_mean (T : ℝ≥0) (H : ℝ≥0→ℝ) (hH : Continuous H) (K : ℝ) (hK : 0≤K) (hb : ∀ u,‖H u‖≤K) :
    (∫ ω, integralValue T H hH K hK hb ω ∂sourceLaw)=0 := by
  have h : (∫ ω, integralProcess T (input T H hH K hK hb) 0 ω ∂sourceLaw)=
      ∫ ω, integralValue T H hH K hK hb ω ∂sourceLaw := integral_condExp (naturalFiltration.le 0)
  rw [integral_congr_ae (integralProcess_zero T (input T H hH K hK hb))] at h
  simpa using h.symm

private theorem lp_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : Lp ℝ 2 μ) :
    ‖X‖^2=∫ a,X a^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

theorem integralValue_second_moment (T : ℝ≥0) (H : ℝ≥0→ℝ) (hH : Continuous H) (K : ℝ) (hK : 0≤K) (hb : ∀ u,‖H u‖≤K) :
    (∫ ω,integralValue T H hH K hK hb ω^2 ∂sourceLaw)=
      ∫ s,H (Real.toNNReal s)^2 ∂timeLaw T := by
  rw [← lp_norm_sq,integralValue,predictableIntegral_norm]
  change ‖(input T H hH K hK hb : Lp ℝ 2 (inputLaw T))‖^2=_
  rw [lp_norm_sq]
  have he := (input_coe T H hH K hK hb).mono (fun _ h => congrArg (fun x : ℝ => x^2) h)
  rw [integral_congr_ae he]
  have hi : Integrable (fun p : ℝ×(ℝ≥0→ℝ) => H (Real.toNNReal p.1)^2) (inputLaw T) :=
    (Lp.memLp (input T H hH K hK hb : Lp ℝ 2 (inputLaw T))).integrable_sq.congr he
  apply (integral_prod _ hi).trans
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by simp)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianDeterministicGaussianIntegral
