import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralMartingale
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Original commitment: the actual source integral process needs justified time continuity in its own energy norm.
Existing result: actual fixed-horizon cutoff inputs and naturally adapted martingale agree in native source L2.
Premise reduced: derive mean-square time continuity by actual atomless time and native dominated convergence.
Model/witness: SAME inputLaw T/sourceLaw; arbitrary genuine predictable L2 input, all T including zero.
Consumer: later continuous modification/quadratic variation; L2 continuity is not asserted to be sample-path continuity.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralL2TimeContinuity
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs
open BrownianPredictableDensity BrownianIntegralTimeTruncation BrownianIntegralMartingale
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem time_boundary_ae (T : ℝ≥0) (c : ℝ) : ∀ᵐ p ∂inputLaw T, p.1 ≠ c := by
  have ht : ∀ᵐ x : ℝ ∂timeLaw T, x ≠ c := by
    exact ae_restrict_of_ae (by rw [ae_iff]; simp)
  apply (Measure.ae_prod_iff_ae_ae ((measurable_fst (measurableSet_singleton c)).compl)).mpr
  exact ht.mono (fun x hx => Eventually.of_forall (fun _ => hx))

private theorem lp_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : Lp ℝ 2 μ) :
    ‖g‖ ^ 2 = ∫ a, g a ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

private theorem cutoff_difference_integral_tendsto (T : ℝ≥0) (f : Lp ℝ 2 (inputLaw T))
    (v : ℕ → ℝ≥0) (s : ℝ≥0) (hv : Tendsto v atTop (𝓝 s)) :
    Tendsto (fun n => ∫ p, ((timeSet T (v n)).indicator f p-(timeSet T s).indicator f p)^2 ∂inputLaw T)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun n => ((min (v n) T : ℝ≥0) : ℝ)) atTop (𝓝 ((min s T : ℝ≥0) : ℝ)) :=
    (continuous_subtype_val.tendsto (min s T)).comp (hv.min tendsto_const_nhds)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun p => ((timeSet T (v n)).indicator f p-(timeSet T s).indicator f p)^2) (inputLaw T) :=
    (((Lp.aestronglyMeasurable f).indicator (timeSet_measurable T (v n))).sub
      ((Lp.aestronglyMeasurable f).indicator (timeSet_measurable T s))).pow 2
  have hb (n : ℕ) : ∀ᵐ p ∂inputLaw T,
      ‖((timeSet T (v n)).indicator f p-(timeSet T s).indicator f p)^2‖ ≤ f p ^ 2 := by
    apply Eventually.of_forall
    intro p
    by_cases hn : p ∈ timeSet T (v n) <;> by_cases hs : p ∈ timeSet T s <;>
      simp [hn,hs,Real.norm_eq_abs] <;> positivity
  have hlim : ∀ᵐ p ∂inputLaw T,
      Tendsto (fun n => ((timeSet T (v n)).indicator f p-(timeSet T s).indicator f p)^2) atTop (𝓝 0) := by
    filter_upwards [time_support_ae T,time_boundary_ae T ((min s T : ℝ≥0) : ℝ)] with p hp hne
    have he : ∀ᶠ n in atTop, (timeSet T (v n)).indicator f p = (timeSet T s).indicator f p := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · filter_upwards [hc.eventually (lt_mem_nhds hlt)] with n hn
        have hnset : p ∈ timeSet T (v n) := ⟨⟨hp.1,hn.le⟩,mem_univ _⟩
        have hsset : p ∈ timeSet T s := ⟨⟨hp.1,hlt.le⟩,mem_univ _⟩
        rw [Set.indicator_of_mem hnset,Set.indicator_of_mem hsset]
      · filter_upwards [hc.eventually (gt_mem_nhds hgt)] with n hn
        have hnset : p ∉ timeSet T (v n) := fun h => not_le.mpr hn h.1.2
        have hsset : p ∉ timeSet T s := fun h => not_le.mpr hgt h.1.2
        rw [Set.indicator_of_notMem hnset,Set.indicator_of_notMem hsset]
    exact (tendsto_congr' (he.mono (fun n hn => by rw [hn]; simp))).mpr tendsto_const_nhds
  have h := tendsto_integral_of_dominated_convergence (fun p => f p ^ 2) hm (Lp.memLp f).integrable_sq hb hlim
  simpa only [integral_zero] using h

private theorem truncate_sequence_tendsto (T : ℝ≥0) (f : fullPredictableL2 T)
    (v : ℕ → ℝ≥0) (s : ℝ≥0) (hv : Tendsto v atTop (𝓝 s)) :
    Tendsto (fun n => truncate T (v n) f) atTop (𝓝 (truncate T s f)) := by
  apply tendsto_subtype_rng.mpr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (n : ℕ) :
      ‖(truncate T (v n) f : Lp ℝ 2 (inputLaw T))-(truncate T s f : Lp ℝ 2 (inputLaw T))‖ ^ 2 =
        ∫ p, ((timeSet T (v n)).indicator (f : Lp ℝ 2 (inputLaw T)) p-
          (timeSet T s).indicator (f : Lp ℝ 2 (inputLaw T)) p)^2 ∂inputLaw T := by
    rw [lp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (truncate T (v n) f : Lp ℝ 2 (inputLaw T)) (truncate T s f : Lp ℝ 2 (inputLaw T)),
      truncate_coe T (v n) f,truncate_coe T s f] with p hs hn ht
    simp only [Pi.sub_apply] at hs
    rw [hs,hn,ht]
  have hsq : Tendsto (fun n =>
      ‖(truncate T (v n) f : Lp ℝ 2 (inputLaw T))-(truncate T s f : Lp ℝ 2 (inputLaw T))‖ ^ 2)
      atTop (𝓝 0) :=
    (tendsto_congr' (Eventually.of_forall he)).mpr (cutoff_difference_integral_tendsto T f v s hv)
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hroot

/-- Actual truncation varies continuously in time in the ORIGINAL product
L2 norm; no path-continuity certificate is supplied. -/
theorem continuous_truncate (T : ℝ≥0) (f : fullPredictableL2 T) : Continuous (fun s => truncate T s f) := by
  apply continuous_iff_seqContinuous.mpr
  intro v s hv
  exact truncate_sequence_tendsto T f v s hv

/-- Necessary mean-square time continuity of the ACTUAL same-source integral
classes. This is strictly the native source L2 topology. -/
theorem continuous_integralClassProcess (T : ℝ≥0) (f : fullPredictableL2 T) :
    Continuous (integralClassProcess T f) :=
  (predictableIntegral T).continuous.comp (continuous_truncate T f)

/-- Canonical martingale's L2 class, using its proved actual L2 membership. -/
def processClass (T : ℝ≥0) (f : fullPredictableL2 T) (u : ℝ≥0) : Lp ℝ 2 sourceLaw :=
  (integralProcess_memLp_two T u f).toLp (integralProcess T f u)

theorem processClass_eq_actual (T u : ℝ≥0) (f : fullPredictableL2 T) :
    processClass T f u = integralClassProcess T f u := by
  apply Lp.ext
  exact (integralProcess_memLp_two T u f).coeFn_toLp.trans (integralProcess_eq_truncated T u f)

/-- The canonical ACTUAL martingale inherits the proved source-energy time
continuity. This theorem makes no almost-sure continuous-path assertion. -/
theorem continuous_processClass (T : ℝ≥0) (f : fullPredictableL2 T) : Continuous (processClass T f) := by
  have he : processClass T f = integralClassProcess T f := funext (fun u => processClass_eq_actual T u f)
  rw [he]
  exact continuous_integralClassProcess T f

/-- Direct mean-square continuity of the actual strongly adapted martingale,
for EVERY converging time sequence on the SAME source sample space. -/
theorem integralProcess_meanSquare_tendsto (T : ℝ≥0) (f : fullPredictableL2 T)
    (v : ℕ → ℝ≥0) (s : ℝ≥0) (hv : Tendsto v atTop (𝓝 s)) :
    Tendsto (fun n => ∫ ω, (integralProcess T f (v n) ω-integralProcess T f s ω)^2 ∂sourceLaw)
      atTop (𝓝 0) := by
  have he (n : ℕ) : ‖processClass T f (v n)-processClass T f s‖ ^ 2 =
      ∫ ω, (integralProcess T f (v n) ω-integralProcess T f s ω)^2 ∂sourceLaw := by
    rw [lp_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (processClass T f (v n)) (processClass T f s),
      (integralProcess_memLp_two T (v n) f).coeFn_toLp,
      (integralProcess_memLp_two T s f).coeFn_toLp] with ω hs hn ht
    simp only [Pi.sub_apply] at hs
    rw [hs]
    simp only [processClass]
    rw [hn,ht]
  have hc := ((continuous_processClass T f).tendsto s).comp hv
  have hc' : Tendsto (fun n => processClass T f (v n)-processClass T f s)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self] using hc.sub (tendsto_const_nhds (x := processClass T f s))
  have hsq : Tendsto (fun n => ‖processClass T f (v n)-processClass T f s‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using hc'.norm.pow 2
  exact (tendsto_congr' (Eventually.of_forall he)).mp hsq

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralL2TimeContinuity
