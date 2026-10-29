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




open BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource BrownianVectorIntegralConditionalSource
example (d : ℕ) (T u : ℝ≥0) (f : fullPredictableL2 d T) :
    naturalProjection d u (predictableIntegral d T f) = integralClassProcess d T f u :=
  integral_projection_identity d T u f
example (d : ℕ) (T u : ℝ≥0) (f : fullPredictableL2 d T) :
    integralClassProcess d T f u ∈ lpMeas ℝ ℝ (jointNaturalFiltration d u) 2 (productLaw d) :=
  integralClassProcess_adapted d T u f
example (d : ℕ) (T : ℝ≥0) (f : fullPredictableL2 d T) :
    Martingale (integralProcess d T f) (jointNaturalFiltration d) (productLaw d) :=
  integralProcess_martingale d T f
example (d : ℕ) (T u : ℝ≥0) (f : fullPredictableL2 d T) :
    integralProcess d T f u =ᵐ[productLaw d] (integralClassProcess d T f u : Sample d → ℝ) :=
  integralProcess_eq_truncated d T u f
example (d : ℕ) (T u : ℝ≥0) (f : fullPredictableL2 d T) :
    (∫ ω, integralProcess d T f u ω ^ 2 ∂productLaw d) =
      ∫ p in timeSet d T u, ‖(f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p‖^2 ∂inputLaw d T :=
  integralProcess_energy d T u f
-- One actual record, not a new chosen process: at time1 its first coefficient
-- reads the OTHER coordinate at1. Zero input before1/after2, horizon3.
def realRecord := intervalRecord 2 3 1 2 (by norm_num) (by norm_num)
  (rotating 1) (rotating_past 1) (rotating_bounded 1)
theorem actual_record_prefix (u : ℝ≥0) :
    integralProcess 2 3 (literalPredictableInput 2 realRecord) u =ᵐ[productLaw 2]
      oneStep 2 (rotating 1) 1 (BrownianCommonRefinement.clamp 1 2 u) := by
  apply (integralProcess_returns_literal_prefix 2 realRecord u).trans
  apply ae_of_all
  intro ω
  change (∑ i : Fin 3, oneStep 2 (![fun _ _ => 0,rotating 1,fun _ _ => 0] i)
    (![0,1,2,3] i.castSucc) (BrownianCommonRefinement.clamp
      (![0,1,2,3] i.castSucc) (![0,1,2,3] i.succ) u) ω) = _
  simp [Fin.sum_univ_succ,oneStep,component]
example : integralProcess 2 3 (literalPredictableInput 2 realRecord) 0 =ᵐ[productLaw 2] fun _ => 0 :=
  integralProcess_zero 2 3 _
example : integralProcess 2 3 (literalPredictableInput 2 realRecord) (3/2) =ᵐ[productLaw 2]
    oneStep 2 (rotating 1) 1 (3/2) := by
  have he : BrownianCommonRefinement.clamp (1 : ℝ≥0) 2 (3/2) = 3/2 := by
    unfold BrownianCommonRefinement.clamp
    rw [min_eq_right (show (3/2 : ℝ≥0) ≤ 2 by exact_mod_cast (by norm_num : (3/2 : ℝ) ≤ 2)),
      max_eq_right (show (1 : ℝ≥0) ≤ 3/2 by exact_mod_cast (by norm_num : (1 : ℝ) ≤ 3/2))]
  simpa only [he] using actual_record_prefix (3/2)
example : integralProcess 2 3 (literalPredictableInput 2 realRecord) 4 =ᵐ[productLaw 2]
    oneStep 2 (rotating 1) 1 2 := by
  have he : BrownianCommonRefinement.clamp (1 : ℝ≥0) 2 4 = 2 := by norm_num [BrownianCommonRefinement.clamp]
  simpa only [he] using actual_record_prefix 4
-- Actual nonzero Euclidean energy survives terminal/native conditional version.
theorem actual_record_energy :
    (∫ ω, integralProcess 2 3 (literalPredictableInput 2 realRecord) 3 ω ^ 2 ∂productLaw 2) = 1 := by
  have he : BrownianCommonRefinement.clamp (1 : ℝ≥0) 2 3 = 2 := by norm_num [BrownianCommonRefinement.clamp]
  have hp := actual_record_prefix 3
  rw [he] at hp
  calc
    _ = ∫ ω, oneStep 2 (rotating 1) 1 2 ω ^ 2 ∂productLaw 2 :=
      integral_congr_ae (hp.mono (fun _ h => congrArg (fun x : ℝ => x^2) h))
    _ = ((2 : ℝ)-1)*(∫ ω, ‖coefficient 2 (rotating 1) ω‖^2 ∂productLaw 2) :=
      oneStep_isometry 1 2 (by norm_num) (rotating_past 1) (rotating_bounded 1)
    _ = 1 := by norm_num [rotating_unit]
example (T u : ℝ≥0) (f : fullPredictableL2 0 T) : integralProcess 0 T f u =ᵐ[productLaw 0] fun _ => 0 := by
  have hz : (f : Lp (EuclideanSpace ℝ (Fin 0)) 2 (inputLaw 0 T)) = 0 :=
    Lp.ext (ae_of_all _ (fun _ => Subsingleton.elim _ _))
  have hf : f = 0 := Subtype.ext hz
  rw [hf]
  have h := integralProcess_eq_truncated 0 T u 0
  simp only [integralClassProcess,map_zero] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (productLaw 0))
example (d : ℕ) (u : ℝ≥0) (f : fullPredictableL2 d 0) : integralProcess d 0 f u =ᵐ[productLaw d] fun _ => 0 := by
  have hz : (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d 0)) = 0 :=
    Lp.ext (ae_iff.mpr (by simp [inputLaw_zero]))
  have hf : f = 0 := Subtype.ext hz
  rw [hf]
  have h := integralProcess_eq_truncated d 0 u 0
  simp only [integralClassProcess,map_zero] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (productLaw d))
example (d : ℕ) (T u : ℝ≥0) (r : ElementaryInput d T) :
    integralProcess d T (literalPredictableInput d r) u =ᵐ[productLaw d]
      fun ω => ∑ i : Fin r.n, oneStep d (r.coefficient i) (r.clock i.castSucc)
        (BrownianCommonRefinement.clamp (r.clock i.castSucc) (r.clock i.succ) u) ω :=
  integralProcess_returns_literal_prefix d r u
#print axioms actual_record_prefix
#print axioms actual_record_energy

namespace RootActualStoppingBoundary
open BrownianVectorIntegralL2TimeContinuity Filter
-- New root discriminator: the actual arbitrary full-input process stops at
-- the caller's ORIGINAL horizon, without a new noise or terminal variable.
theorem full_input_stops_at_own_horizon (d : ℕ) (T u : ℝ≥0)
    (f : fullPredictableL2 d T) (hTu : T ≤ u) :
    integralProcess d T f u =ᵐ[productLaw d]
      (predictableIntegral d T f : Sample d → ℝ) := by
  have hc : truncate d T u f = f := by
    have ht : timeSet d T u = timeSet d T T := by
      simp only [timeSet, min_eq_right hTu, min_self]
    have he : truncate d T u f = truncate d T T f := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [truncate_coe d T u f, truncate_coe d T T f] with p hu hT
      rw [hu,hT,ht]
    exact he.trans (truncate_horizon d T f)
  have he := integralProcess_eq_truncated d T u f
  simpa only [integralClassProcess,hc] using he
example (d : ℕ) (T : ℝ≥0) (f : fullPredictableL2 d T) :
    Continuous (processClass d T f) := continuous_processClass d T f
example (d : ℕ) (T : ℝ≥0) (f : fullPredictableL2 d T)
    (v : ℕ → ℝ≥0) (s : ℝ≥0) (hv : Tendsto v atTop (𝓝 s)) :
    Tendsto (fun n => ∫ ω, (integralProcess d T f (v n) ω -
      integralProcess d T f s ω)^2 ∂productLaw d) atTop (𝓝 0) :=
  integralProcess_meanSquare_tendsto d T f v s hv
#print axioms full_input_stops_at_own_horizon
#print axioms continuous_processClass
#print axioms integralProcess_meanSquare_tendsto
end RootActualStoppingBoundary
