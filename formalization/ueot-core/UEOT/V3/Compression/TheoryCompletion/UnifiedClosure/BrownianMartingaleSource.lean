import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousSource
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
Original commitment: actual stochastic dynamics need causal conditional-moment sources.
Existing result: one constructed continuous Brownian process and probability law, with finite Gaussian laws.
Premise reduced: derive natural-filtration martingale and compensated/exponential sources from independent increments.
Model/witness: the SAME actual nonzero-noise source, all nonnegative real times; no martingale certificate input.
Consumer: conditional moments and normalized finite-horizon density; general Ito/Girsanov remain open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMartingaleSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianContinuousSource BrownianProjectiveSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- The genuine natural filtration of the actual continuous version. -/
def naturalFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
  Filtration.natural process (fun t => (measurable_process t).stronglyMeasurable)

theorem process_stronglyAdapted : StronglyAdapted naturalFiltration process :=
  Filtration.stronglyAdapted_natural (fun t => (measurable_process t).stronglyMeasurable)

def increment (s t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := process t ω - process s ω

theorem measurable_increment (s t : ℝ≥0) : Measurable (increment s t) :=
  (measurable_process t).sub (measurable_process s)

/-- Actual future increment is independent of the ENTIRE natural past, not
merely of the single current observation. -/
theorem increment_indep_past (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (increment s t) (fun ω (r : Iic s) => process r ω) sourceLaw := by
  have h := process_isPreBrownian.indepFun_shift s
  have he := h.comp (measurable_pi_apply (t-s)) measurable_id
  have hs : s+(t-s) = t := add_tsub_cancel_of_le hst
  change IndepFun (fun ω => process (s+(t-s)) ω-process s ω)
    (fun ω (r : Iic s) => process r ω) sourceLaw at he
  rw [hs] at he
  change IndepFun (fun ω => process t ω-process s ω) (fun ω (r : Iic s) => process r ω) sourceLaw
  exact he

private theorem increment_indep_natural (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (increment s t) inferInstance) (naturalFiltration s) sourceLaw := by
  rw [naturalFiltration, Filtration.natural_eq_comap]
  exact increment_indep_past s t hst

/-- Conditional expectation of any measurable increment transform comes from
actual independence. Integrability is separately proved for each consumer. -/
theorem condExp_increment_function (s t : ℝ≥0) (hst : s ≤ t) (φ : ℝ → ℝ)
    (hφ : Measurable φ) :
    sourceLaw[fun ω => φ (increment s t ω) | naturalFiltration s] =ᵐ[sourceLaw]
      fun _ => ∫ ω, φ (increment s t ω) ∂sourceLaw := by
  have hm : @Measurable (ℝ≥0 → ℝ) ℝ
      (MeasurableSpace.comap (increment s t) inferInstance) inferInstance (increment s t) :=
    measurable_iff_comap_le.mpr le_rfl
  exact condExp_indep_eq (measurable_increment s t).comap_le (naturalFiltration.le s)
    (hφ.comp hm).stronglyMeasurable (increment_indep_natural s t hst)

theorem increment_integrable (s t : ℝ≥0) : Integrable (increment s t) sourceLaw :=
  (process_isPreBrownian.integrable_eval t).sub (process_isPreBrownian.integrable_eval s)

theorem increment_mean (s t : ℝ≥0) : (∫ ω, increment s t ω ∂sourceLaw) = 0 := by
  change (∫ ω, process t ω-process s ω ∂sourceLaw) = 0
  rw [integral_sub (process_isPreBrownian.integrable_eval t)
    (process_isPreBrownian.integrable_eval s), process_isPreBrownian.integral_eval,
    process_isPreBrownian.integral_eval, sub_self]

theorem condExp_increment_zero (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[increment s t | naturalFiltration s] =ᵐ[sourceLaw] fun _ => 0 := by
  simpa only [id_eq, increment_mean] using condExp_increment_function s t hst id measurable_id

/-- The actual process is a martingale under its own actual natural filtration. -/
theorem process_martingale : Martingale process naturalFiltration sourceLaw := by
  refine ⟨process_stronglyAdapted, fun s t hst => ?_⟩
  have he : process t = increment s t + process s := by funext ω; simp [increment]
  rw [he]
  have ha := condExp_add (increment_integrable s t) (process_isPreBrownian.integrable_eval s)
    (naturalFiltration s)
  have hs := condExp_of_stronglyMeasurable (naturalFiltration.le s) (process_stronglyAdapted s)
    (process_isPreBrownian.integrable_eval s)
  apply ha.trans
  rw [hs]
  filter_upwards [condExp_increment_zero s t hst] with ω hω
  simp only [Pi.add_apply, hω, zero_add]

private theorem gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [id_eq, integral_id_gaussianReal, sub_zero] using h

theorem increment_square_integrable (s t : ℝ≥0) :
    Integrable (fun ω => increment s t ω ^ 2) sourceLaw :=
  (process_isPreBrownian.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable_sq

theorem increment_square_mean (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, increment s t ω ^ 2 ∂sourceLaw) = (t : ℝ)-(s : ℝ) := by
  calc
    _ = ∫ x : ℝ, x^2 ∂gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) :=
      (process_isPreBrownian.hasLaw_sub t s).integral_comp (by fun_prop)
    _ = (nndist (t : ℝ) (s : ℝ) : ℝ) := gaussian_second_moment _
    _ = _ := by
      rw [coe_nndist,Real.dist_eq,abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hst)

theorem condExp_increment_square (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[fun ω => increment s t ω ^ 2 | naturalFiltration s] =ᵐ[sourceLaw]
      fun _ => (t : ℝ)-(s : ℝ) := by
  exact (condExp_increment_function s t hst (fun x => x^2) (by fun_prop)).trans
    (ae_of_all sourceLaw (fun _ => increment_square_mean s t hst))

private theorem cross_integrable (s t : ℝ≥0) :
    Integrable (process s * increment s t) sourceLaw :=
  (process_isPreBrownian.hasLaw_eval s).hasGaussianLaw.memLp_two.integrable_mul
    (process_isPreBrownian.hasLaw_sub t s).hasGaussianLaw.memLp_two

private theorem condExp_cross_zero (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[process s * increment s t | naturalFiltration s] =ᵐ[sourceLaw] fun _ => 0 := by
  have h := condExp_mul_of_stronglyMeasurable_left (process_stronglyAdapted s)
    (cross_integrable s t) (increment_integrable s t)
  apply h.trans
  filter_upwards [condExp_increment_zero s t hst] with ω hω
  simp only [Pi.mul_apply,hω,mul_zero]

/-- Actual conditional second moment, exposing the real elapsed-time noise
term that a simple predictable integral consumer needs. -/
theorem condExp_process_square (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[fun ω => process t ω ^ 2 | naturalFiltration s] =ᵐ[sourceLaw]
      fun ω => process s ω ^ 2 + ((t : ℝ)-(s : ℝ)) := by
  have hs : Integrable (fun ω => process s ω ^ 2) sourceLaw :=
    (process_isPreBrownian.hasLaw_eval s).hasGaussianLaw.memLp_two.integrable_sq
  have he : (fun ω => process t ω ^ 2) =
      (fun ω => increment s t ω ^ 2) + (2 : ℝ) • (process s * increment s t) +
        (fun ω => process s ω ^ 2) := by
    funext ω
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,increment]
    ring
  rw [he]
  have h1 := condExp_add ((increment_square_integrable s t).add
    ((cross_integrable s t).const_mul 2)) hs (naturalFiltration s)
  have h2 := condExp_add (increment_square_integrable s t)
    ((cross_integrable s t).const_mul 2) (naturalFiltration s)
  have h3 := condExp_smul (μ := sourceLaw) (2 : ℝ) (process s * increment s t) (naturalFiltration s)
  have h4 : sourceLaw[(fun ω => process s ω ^ 2) | naturalFiltration s] =
      (fun ω => process s ω ^ 2) := condExp_of_stronglyMeasurable (naturalFiltration.le s)
    ((process_stronglyAdapted s).pow 2) hs
  simp only [Pi.smul_def, smul_eq_mul] at h3
  apply h1.trans
  filter_upwards [h2,h3,condExp_increment_square s t hst,condExp_cross_zero s t hst] with ω h2ω h3ω hsq hcross
  simp only [Pi.add_apply] at *
  rw [h4,h2ω,h3ω,hsq,hcross]
  ring

/-- The compensated-square process of the SAME actual Brownian source. -/
def compensatedSquare (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := process t ω ^ 2 - (t : ℝ)

theorem compensatedSquare_martingale : Martingale compensatedSquare naturalFiltration sourceLaw := by
  refine ⟨fun t => ((process_stronglyAdapted t).pow 2).sub stronglyMeasurable_const,
    fun s t hst => ?_⟩
  have h := condExp_sub
    (process_isPreBrownian.hasLaw_eval t).hasGaussianLaw.memLp_two.integrable_sq
    (integrable_const (t : ℝ)) (naturalFiltration s)
  apply h.trans
  rw [condExp_const (naturalFiltration.le s)]
  filter_upwards [condExp_process_square s t hst] with ω hω
  change _ - (t : ℝ) = process s ω ^ 2 - (s : ℝ)
  rw [hω]
  ring

private def gaussianExp (u : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (u*x-u^2*(v : ℝ)/2)

private theorem gaussianExp_integrable {X : (ℝ≥0 → ℝ) → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) sourceLaw) (u : ℝ) :
    Integrable (fun ω => gaussianExp u v (X ω)) sourceLaw := by
  have hi : Integrable (fun x => Real.exp (u*x)) (sourceLaw.map X) := by
    rw [hX.map_eq]
    exact integrable_exp_mul_gaussianReal u
  have hj := hi.comp_aemeasurable hX.aemeasurable
  have he : (fun ω => gaussianExp u v (X ω)) =
      (fun ω => Real.exp (u*X ω) * Real.exp (-(u^2*(v : ℝ)/2))) := by
    funext ω
    simp only [gaussianExp, sub_eq_add_neg, Real.exp_add]
  rw [he]
  exact hj.mul_const _

private theorem gaussianExp_mean {X : (ℝ≥0 → ℝ) → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) sourceLaw) (u : ℝ) :
    (∫ ω, gaussianExp u v (X ω) ∂sourceLaw) = 1 := by
  simp only [gaussianExp,sub_eq_add_neg,Real.exp_add,integral_mul_const]
  change mgf X sourceLaw u * Real.exp (-(u^2*(v : ℝ)/2)) = 1
  rw [mgf_gaussianReal hX.map_eq]
  rw [← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

theorem increment_hasLaw (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (increment s t) (gaussianReal 0 (t-s)) sourceLaw := by
  have hd : nndist (t : ℝ) (s : ℝ) = t-s := by
    apply NNReal.coe_injective
    rw [coe_nndist,Real.dist_eq,NNReal.coe_sub hst,abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast hst)
  rw [← hd]
  exact process_isPreBrownian.hasLaw_sub t s

/-- Actual exponential martingale candidate, with real drift parameter and
source variance clock. Its defining formula is consumed, not a chosen version. -/
def exponentialProcess (u : ℝ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  gaussianExp u t (process t ω)

theorem exponentialProcess_pos (u : ℝ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    0 < exponentialProcess u t ω := Real.exp_pos _

theorem exponentialProcess_stronglyAdapted (u : ℝ) :
    StronglyAdapted naturalFiltration (exponentialProcess u) := by
  intro t
  apply Real.continuous_exp.comp_stronglyMeasurable
  exact ((process_stronglyAdapted t).const_mul u).sub stronglyMeasurable_const

theorem exponentialProcess_integrable (u : ℝ) (t : ℝ≥0) :
    Integrable (exponentialProcess u t) sourceLaw :=
  gaussianExp_integrable (process_isPreBrownian.hasLaw_eval t) u

theorem exponentialProcess_mean_one (u : ℝ) (t : ℝ≥0) :
    (∫ ω, exponentialProcess u t ω ∂sourceLaw) = 1 :=
  gaussianExp_mean (process_isPreBrownian.hasLaw_eval t) u

private def exponentialIncrement (u : ℝ) (s t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  gaussianExp u (t-s) (increment s t ω)

private theorem exponentialIncrement_integrable (u : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    Integrable (exponentialIncrement u s t) sourceLaw :=
  gaussianExp_integrable (increment_hasLaw s t hst) u

private theorem condExp_exponentialIncrement_one (u : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[exponentialIncrement u s t | naturalFiltration s] =ᵐ[sourceLaw] fun _ => 1 := by
  exact (condExp_increment_function s t hst (gaussianExp u (t-s)) (by
    unfold gaussianExp
    fun_prop)).trans (ae_of_all sourceLaw (fun _ => gaussianExp_mean (increment_hasLaw s t hst) u))

private theorem exponentialProcess_factor (u : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    exponentialProcess u t = exponentialProcess u s * exponentialIncrement u s t := by
  funext ω
  dsimp [exponentialProcess,exponentialIncrement,gaussianExp,increment]
  rw [← Real.exp_add,NNReal.coe_sub hst]
  congr 1
  ring

/-- Actual natural-filtration exponential martingale, for EVERY real parameter
and ALL nonnegative real times, derived from this same source's Gaussian law. -/
theorem exponentialProcess_martingale (u : ℝ) :
    Martingale (exponentialProcess u) naturalFiltration sourceLaw := by
  refine ⟨exponentialProcess_stronglyAdapted u, fun s t hst => ?_⟩
  have hi : Integrable (exponentialProcess u s * exponentialIncrement u s t) sourceLaw := by
    rw [← exponentialProcess_factor u s t hst]
    exact exponentialProcess_integrable u t
  rw [exponentialProcess_factor u s t hst]
  apply (condExp_mul_of_stronglyMeasurable_left
    (exponentialProcess_stronglyAdapted u s) hi (exponentialIncrement_integrable u s t hst)).trans
  filter_upwards [condExp_exponentialIncrement_one u s t hst] with ω hω
  simp only [Pi.mul_apply,hω,mul_one]

/-- A normalized finite-horizon change of measure on the original source
space. No new latent path or new Brownian law is introduced. -/
def tiltedLaw (u : ℝ) (T : ℝ≥0) : Measure (ℝ≥0 → ℝ) :=
  sourceLaw.withDensity (fun ω => ENNReal.ofReal (exponentialProcess u T ω))

theorem measurable_exponentialProcess (u : ℝ) (t : ℝ≥0) :
    Measurable (exponentialProcess u t) :=
  (exponentialProcess_stronglyAdapted u t).measurable.mono (naturalFiltration.le t) le_rfl

instance tiltedLaw_isProbabilityMeasure (u : ℝ) (T : ℝ≥0) : IsProbabilityMeasure (tiltedLaw u T) where
  measure_univ := by
    rw [tiltedLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (exponentialProcess_integrable u T)
        (ae_of_all sourceLaw (fun ω => (exponentialProcess_pos u T ω).le)),
      exponentialProcess_mean_one]
    norm_num

theorem tiltedLaw_absolutelyContinuous (u : ℝ) (T : ℝ≥0) : tiltedLaw u T ≪ sourceLaw :=
  withDensity_absolutelyContinuous sourceLaw _

/-- The actual Radon--Nikodym derivative is the same explicit, normalized
exponential process whose conditional expectation has just been proved. -/
theorem tiltedLaw_rnDeriv (u : ℝ) (T : ℝ≥0) :
    (tiltedLaw u T).rnDeriv sourceLaw =ᵐ[sourceLaw]
      fun ω => ENNReal.ofReal (exponentialProcess u T ω) :=
  Measure.rnDeriv_withDensity sourceLaw (measurable_exponentialProcess u T).ennreal_ofReal

/-- Horizon consistency on every genuine natural-past event is supplied by
the actual martingale, not postulated as a family-of-measures certificate. -/
theorem tiltedLaw_agrees_on_past (u : ℝ) (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) :
    tiltedLaw u t A = tiltedLaw u s A := by
  have hmA : MeasurableSet A := naturalFiltration.le s A hA
  rw [tiltedLaw,tiltedLaw,withDensity_apply _ hmA,withDensity_apply _ hmA,
    ← ofReal_integral_eq_lintegral_ofReal (exponentialProcess_integrable u t).integrableOn
      (ae_of_all _ (fun ω => (exponentialProcess_pos u t ω).le)),
    ← ofReal_integral_eq_lintegral_ofReal (exponentialProcess_integrable u s).integrableOn
      (ae_of_all _ (fun ω => (exponentialProcess_pos u s ω).le))]
  exact congrArg ENNReal.ofReal ((exponentialProcess_martingale u).setIntegral_eq hst hA).symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMartingaleSource
