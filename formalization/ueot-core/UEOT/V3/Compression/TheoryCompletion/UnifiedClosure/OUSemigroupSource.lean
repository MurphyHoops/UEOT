import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUTransitionKernelSource

/-!
Original commitment: source-derived conditional OU transitions must compose as the same actual semigroup.
Existing result: SAME actual OU bounded-Borel conditional Markov kernel under the whole time-changed past.
Premise reduced: derive time-homogeneous semigroup from actual initial law, actual conditional expectation and tower integration.
Model/witness: SAME original sourceLaw/ouSource/process, k>0, arbitrary noise and initial state; bounded Borel tests.
Consumer: actual OU mechanism/generator source; physical-clock SDE, general drift and Girsanov remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUSemigroupSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource OUQuadraticDynkinSource
open OUConditionalInnovationSource OUTransitionKernelSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- SAME actual initial readout, not merely an initial moment match. -/
theorem actualOU_initial (k σ x₀ : ℝ) : actualOU k σ x₀ 0 =ᵐ[sourceLaw] fun _ => x₀ := by
  filter_upwards [process_zero] with ω hω
  simp [actualOU,ouSource,ouClock,hω]

/-- The native transition kernel is the actual original source pushforward
from every supplied initial state. -/
theorem actualOU_hasLaw (k σ x₀ : ℝ) (t : ℝ≥0) :
    HasLaw (actualOU k σ x₀ t) (transitionKernel k σ 0 t x₀) sourceLaw := by
  rw [transitionKernel_apply]
  have hl := gaussianReal_const_add (innovation_hasLaw k σ 0 t) (decay k 0 t*x₀)
  rw [zero_add] at hl
  apply hl.congr
  filter_upwards [actualOU_initial k σ x₀] with ω hω
  rw [actualOU_transition_decomposition,hω]

theorem decay_add_left (k : ℝ) (s t : ℝ≥0) : decay k s (s+t) = decay k 0 t := by
  unfold decay
  simp only [NNReal.coe_add,NNReal.coe_zero,sub_zero]
  congr 1
  ring

theorem transitionVariance_add_left (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) :
    transitionVariance k σ s (s+t) = transitionVariance k σ 0 t := by
  apply NNReal.coe_injective
  rw [transitionVariance_coe k σ hk s (s+t) (le_self_add),transitionVariance_coe k σ hk 0 t bot_le]
  simp only [NNReal.coe_add,NNReal.coe_zero,sub_zero,add_sub_cancel_left]

theorem transition_add_left (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (φ : ℝ → ℝ) (x : ℝ) :
    transition k σ s (s+t) φ x = transition k σ 0 t φ x := by
  unfold transition
  rw [decay_add_left,transitionVariance_add_left k σ hk]

/-- Actual OU Markov semigroup operator; no composition/source field. -/
def semigroup (k σ : ℝ) (t : ℝ≥0) (φ : ℝ → ℝ) : ℝ → ℝ := transition k σ 0 t φ

theorem semigroup_measurable (k σ : ℝ) (t : ℝ≥0) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    Measurable (semigroup k σ t φ) := transition_measurable k σ 0 t φ hφ

theorem semigroup_norm_le (k σ : ℝ) (t : ℝ≥0) (φ : ℝ → ℝ) (K : ℝ) (hb : ∀ x, ‖φ x‖ ≤ K) (x : ℝ) :
    ‖semigroup k σ t φ x‖ ≤ K := transition_norm_le k σ 0 t φ K hb x

/-- The operator is the expectation of the SAME actual process for every
initial value and every bounded Borel test. -/
theorem actualOU_expectation (k σ x₀ : ℝ) (t : ℝ≥0) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ ω, φ (actualOU k σ x₀ t ω) ∂sourceLaw) = semigroup k σ t φ x₀ := by
  exact ((actualOU_hasLaw k σ x₀ t).integral_comp hφ.aestronglyMeasurable).trans
    (transitionKernel_integral k σ 0 t φ hφ x₀)

/-- Genuine semigroup composition for ALL initial values and bounded Borel
observables, from actual conditioning on the original whole time-changed
past and actual source integration. No independent compositional law assumed. -/
theorem semigroup_add (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (K : ℝ) (hb : ∀ x, ‖φ x‖ ≤ K) (x₀ : ℝ) :
    semigroup k σ (s+t) φ x₀ = semigroup k σ s (semigroup k σ t φ) x₀ := by
  have hc := actualOU_condExp_transition k σ x₀ hk s (s+t) le_self_add φ hφ K hb
  have hi : (∫ ω, φ (actualOU k σ x₀ (s+t) ω) ∂sourceLaw) =
      ∫ ω, transition k σ s (s+t) φ (actualOU k σ x₀ s ω) ∂sourceLaw := by
    rw [← integral_condExp (ouFiltration k hk |>.le s)]
    exact integral_congr_ae hc
  calc
    _ = ∫ ω, φ (actualOU k σ x₀ (s+t) ω) ∂sourceLaw := (actualOU_expectation k σ x₀ (s+t) φ hφ).symm
    _ = ∫ ω, transition k σ s (s+t) φ (actualOU k σ x₀ s ω) ∂sourceLaw := hi
    _ = ∫ ω, semigroup k σ t φ (actualOU k σ x₀ s ω) ∂sourceLaw := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => transition_add_left k σ hk s t φ _)
    _ = _ := actualOU_expectation k σ x₀ s _ (semigroup_measurable k σ t φ hφ)

/-- The original adopted OU law itself is this native transition law. -/
theorem original_ouLaw_eq_transitionKernel (k σ x₀ : ℝ) (t : ℝ≥0) :
    ouLaw sourceLaw process k σ x₀ (t : ℝ) = transitionKernel k σ 0 t x₀ := by
  simpa only [ouLaw,Real.toNNReal_coe,actualOU] using (actualOU_hasLaw k σ x₀ t).map_eq

/-- Bounded tests have ordinary integrable expectations on the actual
source, not only the total Bochner-integral convention. -/
theorem actualOU_test_integrable (k σ x₀ : ℝ) (t : ℝ≥0) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (K : ℝ) (hb : ∀ x, ‖φ x‖ ≤ K) :
    Integrable (fun ω => φ (actualOU k σ x₀ t ω)) sourceLaw := by
  apply (integrable_const K).mono'
    (hφ.comp_aemeasurable (actualOU_hasLaw k σ x₀ t).aemeasurable).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => hb _)

/-- The actual semigroup's zero clock is the identity for every Borel test. -/
theorem semigroup_zero (k σ : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ) (x : ℝ) :
    semigroup k σ 0 φ x = φ x := by
  rw [← actualOU_expectation k σ x 0 φ hφ]
  have he : (fun ω => φ (actualOU k σ x 0 ω)) =ᵐ[sourceLaw] fun _ => φ x :=
    (actualOU_initial k σ x).fun_comp φ
  rw [integral_congr_ae he]
  simp

/-- The SAME old actual nonzero-noise recovery family is retained alongside
its newly derived transition/semigroup law. -/
theorem same_source_positive_transition :
    0 < (transitionVariance 1 2 1 2 : ℝ) :=
  transitionVariance_pos 1 2 (by norm_num) (by norm_num) 1 2 (by norm_num)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUSemigroupSource
