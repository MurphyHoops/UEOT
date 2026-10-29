import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUConditionalInnovationSource
import Mathlib.Probability.Kernel.CondDistrib

/-!
Original commitment: the actual OU family needs its random-current-state conditional transition and semigroup.
Existing result: SAME original actual OU source, full time-changed-past Gaussian innovation and literal state decomposition.
Premise reduced: native independent joint law/disintegration identifies the actual bounded-Borel transition operator.
Model/witness: SAME sourceLaw/ouSource/actual B, k>0, explicit F_(ouClock k t); bounded Borel tests retain genuine integration.
Consumer: original actual OU mechanism/conditional-generator source; physical-clock SDE and general Girsanov remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUTransitionKernelSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianContinuousSource OUQuadraticDynkinSource
open OUConditionalInnovationSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem measurable_innovation (k σ : ℝ) (s t : ℝ≥0) : Measurable (innovation k σ s t) :=
  measurable_const.mul (measurable_increment _ _)

/-- Actual disintegration under the WHOLE time-changed source past equals
the native constant Gaussian kernel, by the actual independent joint law. -/
theorem innovation_condDistrib (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t) :
    @condDistrib (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance inferInstance inferInstance
      inferInstance (ouFiltration k hk s) (innovation k σ s t) id sourceLaw inferInstance
    =ᵐ[@Measure.map (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (ouFiltration k hk s) id sourceLaw]
      @Kernel.const (ℝ≥0 → ℝ) ℝ (ouFiltration k hk s) inferInstance (gaussianReal 0 (transitionVariance k σ s t)) := by
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (ouFiltration k hk s) id :=
    measurable_id'' (ouFiltration k hk |>.le s)
  have hida : @AEMeasurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) (ouFiltration k hk s) inferInstance id sourceLaw :=
    ⟨id,hid,Eventually.of_forall (fun _ => rfl)⟩
  have hi : Indep (MeasurableSpace.comap (innovation k σ s t) inferInstance) (ouFiltration k hk s) sourceLaw := by
    change Indep (MeasurableSpace.comap (innovation k σ s t) inferInstance) (naturalFiltration (ouClock k s)) sourceLaw
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact innovation_indep_whole_past k σ hk s t hst
  have hi' : @IndepFun (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance (ouFiltration k hk s) inferInstance
      id (innovation k σ s t) sourceLaw := by
    change Indep (MeasurableSpace.comap id (ouFiltration k hk s))
      (MeasurableSpace.comap (innovation k σ s t) inferInstance) sourceLaw
    rw [MeasurableSpace.comap_id]
    exact hi.symm
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hid (measurable_innovation k σ s t)
  rw [Measure.compProd_const,← (innovation_hasLaw k σ s t).map_eq]
  exact @IndepFun.map_prod_eq_prod_map_map (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance sourceLaw
    id (innovation k σ s t) (ouFiltration k hk s) inferInstance inferInstance
    hida (measurable_innovation k σ s t).aemeasurable hi'

/-- Literal transition expectation of the same source's actual Gaussian
innovation, with the actual current state as input. -/
def transition (k σ : ℝ) (s t : ℝ≥0) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, φ (decay k s t*x+z) ∂gaussianReal 0 (transitionVariance k σ s t)

/-- Genuine bounded-Borel Markov transition under the entire time-changed
natural past. The random current state is not fixed before conditioning. -/
theorem actualOU_condExp_transition (k σ x₀ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (K : ℝ) (hb : ∀ x, ‖φ x‖ ≤ K) :
    sourceLaw[fun ω => φ (actualOU k σ x₀ t ω) | ouFiltration k hk s] =ᵐ[sourceLaw]
      fun ω => transition k σ s t φ (actualOU k σ x₀ s ω) := by
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (ouFiltration k hk s) id :=
    measurable_id'' (ouFiltration k hk |>.le s)
  have hida : @AEMeasurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) (ouFiltration k hk s) inferInstance id sourceLaw :=
    ⟨id,hid,Eventually.of_forall (fun _ => rfl)⟩
  let F : (ℝ≥0 → ℝ) × ℝ → ℝ := fun p => φ (decay k s t*actualOU k σ x₀ s p.1+p.2)
  have hF : @StronglyMeasurable ((ℝ≥0 → ℝ) × ℝ) ℝ inferInstance
      ((ouFiltration k hk s).prod inferInstance) F := by
    exact (hφ.comp ((measurable_const.mul
      ((actualOU_stronglyAdapted k σ x₀ hk s).measurable.comp measurable_fst)).add measurable_snd)).stronglyMeasurable
  have hU : Measurable (actualOU k σ x₀ s) :=
    ((actualOU_stronglyAdapted k σ x₀ hk s).mono (ouFiltration k hk |>.le s)).measurable
  have hFi : Integrable (fun ω => F (id ω,innovation k σ s t ω)) sourceLaw := by
    apply (integrable_const K).mono'
      (hφ.comp ((measurable_const.mul hU).add (measurable_innovation k σ s t))).aestronglyMeasurable
    filter_upwards [] with ω
    exact hb _
  have hc := condExp_prod_ae_eq_integral_condDistrib hid (measurable_innovation k σ s t).aemeasurable hF hFi
  rw [MeasurableSpace.comap_id] at hc
  have hkern := @ae_of_ae_map (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (ouFiltration k hk s)
    sourceLaw id hida _ (innovation_condDistrib k σ hk s t hst)
  have he : (fun ω => F (id ω,innovation k σ s t ω)) = fun ω => φ (actualOU k σ x₀ t ω) := by
    funext ω
    exact congrArg φ (actualOU_transition_decomposition k σ x₀ s t ω).symm
  rw [he] at hc
  filter_upwards [hc,hkern] with ω hc hkern
  rw [hkern] at hc
  exact hc

/-- Native Markov kernel obtained by mapping the deterministic current
state times the SAME proved Gaussian innovation measure. -/
def transitionKernel (k σ : ℝ) (s t : ℝ≥0) : Kernel ℝ ℝ :=
  ((Kernel.id : Kernel ℝ ℝ).prod (Kernel.const ℝ (gaussianReal 0 (transitionVariance k σ s t)))).map
    (fun p : ℝ × ℝ => decay k s t*p.1+p.2)

instance transitionKernel_markov (k σ : ℝ) (s t : ℝ≥0) : IsMarkovKernel (transitionKernel k σ s t) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Actual finite Gaussian transition, including degenerate zero-noise and
zero-time laws; its parameters come from the same innovation computation. -/
theorem transitionKernel_apply (k σ : ℝ) (s t : ℝ≥0) (x : ℝ) :
    transitionKernel k σ s t x = gaussianReal (decay k s t*x) (transitionVariance k σ s t) := by
  rw [transitionKernel,Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop)]
  change (gaussianReal 0 (transitionVariance k σ s t)).map (fun z => decay k s t*x+z) = _
  simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := transitionVariance k σ s t) (decay k s t*x)

theorem transitionKernel_integral (k σ : ℝ) (s t : ℝ≥0) (φ : ℝ → ℝ) (hφ : Measurable φ) (x : ℝ) :
    (∫ y, φ y ∂transitionKernel k σ s t x) = transition k σ s t φ x := by
  rw [transitionKernel_apply]
  have hm := gaussianReal_map_const_add (μ := 0) (v := transitionVariance k σ s t) (decay k s t*x)
  rw [zero_add] at hm
  rw [← hm,integral_map (by fun_prop) hφ.aestronglyMeasurable]
  rfl

theorem transition_measurable (k σ : ℝ) (s t : ℝ≥0) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    Measurable (transition k σ s t φ) :=
  (hφ.comp ((measurable_const.mul measurable_fst).add measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem transition_norm_le (k σ : ℝ) (s t : ℝ≥0) (φ : ℝ → ℝ) (K : ℝ) (hb : ∀ x, ‖φ x‖ ≤ K) (x : ℝ) :
    ‖transition k σ s t φ x‖ ≤ K := by
  unfold transition
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := gaussianReal 0 (transitionVariance k σ s t))
      (Eventually.of_forall (fun z => hb (decay k s t*x+z)))

/-- The actual conditional distribution, tested against any bounded Borel
observable, is the original source-derived native Markov kernel. -/
theorem actualOU_condExp_kernel (k σ x₀ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (K : ℝ) (hb : ∀ x, ‖φ x‖ ≤ K) :
    sourceLaw[fun ω => φ (actualOU k σ x₀ t ω) | ouFiltration k hk s] =ᵐ[sourceLaw]
      fun ω => ∫ y, φ y ∂transitionKernel k σ s t (actualOU k σ x₀ s ω) := by
  exact (actualOU_condExp_transition k σ x₀ hk s t hst φ hφ K hb).trans
    (Eventually.of_forall (fun ω => (transitionKernel_integral k σ s t φ hφ (actualOU k σ x₀ s ω)).symm))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUTransitionKernelSource
