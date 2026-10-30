import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
Original commitment: physical-clock OU Gaussian innovations must follow from actual finite Gaussian source approximations, not an assumed Gaussian-limit certificate.
Existing result: native L2 space/characteristic function Gaussian characterization and actual canonical Brownian path/source are available.
Premise reduced: derive real Gaussian-law closure under native strong L2 convergence using actual moments and bounded characteristic tests.
Model/witness: any actual probability source and real native L2 variables; later instantiated by SAME canonical/shifted Brownian deterministic integral approximations.
Consumer/boundary: necessary physical OU Gaussian-law/conditional kernel bridge; this lemma alone asserts no OU dynamics, variance formula or general SDE.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianGaussianL2Closure
open MeasureTheory ProbabilityTheory Set Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory RealInnerProductSpace BoundedContinuousFunction
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

private def oneLp : Lp ℝ 2 P := (memLp_const (μ := P) (p := 2) (1 : ℝ)).toLp (fun _ => 1)
private def meanLinear : Lp ℝ 2 P →L[ℝ] ℝ := innerSL ℝ (oneLp P)

private theorem meanLinear_eq (X : Lp ℝ 2 P) : meanLinear P X=∫ ω, X ω ∂P := by
  change inner ℝ (oneLp P) X=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (μ := P) (p := 2) (1 : ℝ)).coeFn_toLp] with ω h
  change oneLp P ω=(1 : ℝ) at h
  rw [h]
  simp [RCLike.inner_apply]

omit [IsProbabilityMeasure P] in
private theorem lp_norm_sq (X : Lp ℝ 2 P) : ‖X‖^2=∫ ω, X ω^2 ∂P := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

private theorem variance_eq_norm (X : Lp ℝ 2 P) : variance (X : Ω→ℝ) P=‖X‖^2-(meanLinear P X)^2 := by
  rw [variance_eq_sub (Lp.memLp X)]
  change (∫ ω, X ω^2 ∂P)-(∫ ω, X ω ∂P)^2=_
  rw [← lp_norm_sq,meanLinear_eq]

/-- Native strong L2 implies actual first and second centered moment convergence. -/
theorem moments_tendsto {X : ℕ→Lp ℝ 2 P} {Y : Lp ℝ 2 P} (h : Tendsto X atTop (𝓝 Y)) :
    Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 (∫ ω, Y ω ∂P)) ∧
      Tendsto (fun n => variance (X n : Ω→ℝ) P) atTop (𝓝 (variance (Y : Ω→ℝ) P)) := by
  have hm : Tendsto (fun n => meanLinear P (X n)) atTop (𝓝 (meanLinear P Y)) :=
    ((meanLinear P).continuous.tendsto Y).comp h
  constructor
  · simpa only [meanLinear_eq] using hm
  · simp_rw [variance_eq_norm]
    exact (h.norm.pow 2).sub (hm.pow 2)

private theorem bounded_tests_tendsto {X : ℕ→Lp ℝ 2 P} {Y : Lp ℝ 2 P}
    (h : Tendsto X atTop (𝓝 Y)) (φ : ℝ →ᵇ ℂ) :
    Tendsto (fun n => ∫ ω, φ (X n ω) ∂P) atTop (𝓝 (∫ ω, φ (Y ω) ∂P)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,hms,hAE⟩ := ((tendstoInMeasure_of_tendsto_Lp h).comp hns).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro n
    exact φ.continuous.measurable.comp_aemeasurable ((Lp.aestronglyMeasurable (X (ns (ms n)))).aemeasurable) |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall (fun ω => φ.norm_coe_le_norm _)
  · filter_upwards [hAE] with ω hω
    exact (φ.continuous.tendsto _).comp hω

theorem charFun_tendsto {X : ℕ→Lp ℝ 2 P} {Y : Lp ℝ 2 P}
    (h : Tendsto X atTop (𝓝 Y)) (t : ℝ) :
    Tendsto (fun n => charFun (P.map (X n)) t) atTop (𝓝 (charFun (P.map Y) t)) := by
  have he (Z : Lp ℝ 2 P) : charFun (P.map Z) t=∫ ω, innerProbChar t (Z ω) ∂P := by
    rw [charFun_eq_integral_innerProbChar,integral_map ((Lp.aestronglyMeasurable Z).aemeasurable) (innerProbChar t).continuous.aestronglyMeasurable]
  simp_rw [he]
  exact bounded_tests_tendsto P h (innerProbChar t)

/-- Actual Gaussian closure is DERIVED from native moment/characteristic
convergence. No desired limiting law or Gaussian certificate is supplied. -/
theorem hasGaussianLaw_of_tendsto {X : ℕ→Lp ℝ 2 P} {Y : Lp ℝ 2 P}
    (h : Tendsto X atTop (𝓝 Y)) (hG : ∀ n, HasGaussianLaw (X n : Ω→ℝ) P) :
    HasGaussianLaw (Y : Ω→ℝ) P := by
  apply (hasGaussianLaw_iff_charFun_map_eq ((Lp.aestronglyMeasurable Y).aemeasurable)).mpr
  intro t
  have he (Z : Lp ℝ 2 P) : (fun ω => inner ℝ t (Z ω))=ᵐ[P] (t • Z : Lp ℝ 2 P) := by
    apply Filter.EventuallyEq.trans _ (Lp.coeFn_smul t Z).symm
    exact Eventually.of_forall (fun ω => by simp [RCLike.inner_apply,mul_comm])
  have hm := moments_tendsto P (h.const_smul t)
  have hm' : Tendsto (fun n => ∫ ω, inner ℝ t (X n ω) ∂P) atTop (𝓝 (∫ ω, inner ℝ t (Y ω) ∂P)) := by
    simpa only [← integral_congr_ae (he _)] using hm.1
  have hv : Tendsto (fun n => variance (fun ω => inner ℝ t (X n ω)) P) atTop
      (𝓝 (variance (fun ω => inner ℝ t (Y ω)) P)) := by
    simpa only [← variance_congr (he _)] using hm.2
  have hh := (hm'.ofReal.mul_const Complex.I).sub (hv.ofReal.div_const (2 : ℂ))
  have hr := Complex.continuous_exp.continuousAt.tendsto.comp hh
  have ht := charFun_tendsto P h t
  have hc := (tendsto_congr' (Eventually.of_forall (fun n => (hG n).charFun_map_eq t))).mpr hr
  exact tendsto_nhds_unique ht hc

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianGaussianL2Closure
