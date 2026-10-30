import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledItoRunSource

/-!
Original commitment: original P-CTL must consume an actual nonempty controlled family and its own actual maximizing-selector run.
Existing result: SAME fixed Q_A supplies actual ItoRun and true infinite reward for bounded measurable reward and bounded C2 source tests.
Premise reduced: instantiate the ORIGINAL ControlFamily and p_ctl_03 with nonconstant V=2+sin, sigma=2 and actual allowed bounded predictable policies.
Model/witness: rho=1, reward=V−(2a V'+2V'')−a², selector=0; finite deployment window A with infinite observation/reward under its fixed Q_A.
Consumer/boundary: actual P-CTL scalar source family, including nonzero noise and nonzero controls; no consistency across different terminal Q_A or arbitrary HJB solution/general filter claim.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledHJBSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianTimeIntegrand BrownianPredictableInputs BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianBoundedC2DynkinSource BrownianControlledTestInput BrownianControlledDiscountSource BrownianControlledOccupationSource
open BrownianControlledInfiniteRewardSource BrownianControlledC2Source BrownianControlledDynkinSource BrownianControlledItoRunSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def value (x : ℝ) : ℝ := 2+Real.sin x

theorem value_nonconstant : value 0=2 ∧ value (Real.pi/2)=3 := by
  norm_num [value]

theorem value_first : deriv value=Real.cos := by
  funext x
  change deriv (fun y => 2+Real.sin y) x=Real.cos x
  exact ((Real.hasDerivAt_sin x).const_add 2).deriv

theorem value_second : iteratedDeriv 2 value = -Real.sin := by
  rw [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,value_first]
  exact funext (fun x => Real.deriv_cos (x := x))

theorem value_bound (x : ℝ) : ‖value x‖≤(3 : ℝ) := by
  have hn := norm_add_le (2 : ℝ) (Real.sin x)
  have hs : ‖Real.sin x‖≤(1 : ℝ) := by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x
  change ‖2+Real.sin x‖≤3
  simp only [Real.norm_eq_abs] at hs ⊢
  norm_num at hn
  linarith

theorem value_first_bound (x : ℝ) : ‖deriv value x‖≤(1 : ℝ) := by
  simpa only [value_first,Real.norm_eq_abs] using Real.abs_cos_le_one x

theorem value_second_bound (x : ℝ) : ‖iteratedDeriv 2 value x‖≤(1 : ℝ) := by
  simpa only [value_second,Pi.neg_apply,norm_neg,Real.norm_eq_abs] using Real.abs_sin_le_one x

theorem generator_formula (x a : ℝ) : controlledGenerator 2 value x a=2*a*Real.cos x-2*Real.sin x := by
  simp only [controlledGenerator,value_first,value_second,Pi.neg_apply]
  ring

/-- This explicit reward is the declared evaluation contract. The source Ito
and occupation laws are derived independently above, rather than fields of it. -/
def model : UEOT.V3.DiffusionHJBVerification.Model ℝ ℝ where
  rho := 1
  rho_pos := by norm_num
  V := value
  V_C2 := by unfold value; fun_prop
  VBound := 3
  VBound_nonneg := by norm_num
  V_bounded := fun x => by simpa only [Real.norm_eq_abs] using value_bound x
  reward := fun x a => value x-controlledGenerator 2 value x a-a^2
  generatorV := controlledGenerator 2 value
  selector := fun _ => 0
  selector_measurable := measurable_const
  hjb_upper := by intro x a; nlinarith [sq_nonneg a]
  hjb_selector := by intro x; ring

theorem reward_measurable : Measurable (fun z : ℝ × ℝ => model.reward z.1 z.2) := by
  change Measurable (fun z : ℝ × ℝ => value z.1-controlledGenerator 2 value z.1 z.2-z.2^2)
  simp_rw [generator_formula]
  unfold value
  fun_prop

theorem reward_bound (K : ℝ) (hK : 0≤K) (x a : ℝ) (ha : ‖a‖≤K) :
    ‖model.reward x a‖≤5+2*K+K^2 := by
  change ‖value x-controlledGenerator 2 value x a-a^2‖≤_
  have hg : ‖controlledGenerator 2 value x a‖≤2*K+2 := by
    rw [generator_formula]
    apply (norm_sub_le _ _).trans
    have hc : ‖Real.cos x‖≤(1 : ℝ) := by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x
    have hs : ‖Real.sin x‖≤(1 : ℝ) := by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x
    simp only [Real.norm_eq_abs] at ha hc hs
    rw [norm_mul,norm_mul,norm_mul]
    norm_num
    nlinarith [mul_le_mul ha hc (abs_nonneg _) hK]
  have hs : ‖a^2‖≤K^2 := by rw [norm_pow]; nlinarith [norm_nonneg a]
  exact ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
    (by nlinarith [value_bound x])

/-- Policy includes the finite deployment window; Q_A stays fixed throughout
its infinite observation/reward horizon. No projective family of Q_A is used. -/
def Policy (K : ℝ) := Σ A : ℝ≥0, {b : fullPredictableL2 A //
  ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K}

private theorem zero_bound (K : ℝ) (hK : 0≤K) :
    ∀ᵐ p ∂inputLaw 0, |(0 : Lp ℝ 2 (inputLaw 0)) p|≤K := by
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := inputLaw 0)] with p hp
  rw [hp]
  change |(0 : ℝ)|≤K
  simpa only [abs_zero] using hK

def selectorPolicy (K : ℝ) (hK : 0≤K) : Policy K := ⟨0,0,zero_bound K hK⟩

def run (K : ℝ) (hK : 0≤K) (π : Policy K) (x₀ : ℝ) : model.ItoRun x₀ :=
  actualItoRun π.1 π.2.1 K hK π.2.2 2 model (fun _ _ => rfl)
    1 1 (by norm_num) (by norm_num) value_first_bound value_second_bound reward_measurable
    (5+2*K+K^2) (reward_bound K hK) x₀

/-- The actual selector action is zero everywhere because its literal deployment
window is empty, not because successful paths are selected or conditioned. -/
def selectorRun (K : ℝ) (hK : 0≤K) (x₀ : ℝ) : model.SelectorRun x₀ where
  toItoRun := run K hK (selectorPolicy K hK) x₀
  selector_ae := by
    intro U
    change ∀ᵐ z ∂occupation 0 0 K x₀ 2 1 U, z.2=0
    rw [occupation]
    apply (ae_map_iff (jointReadout_measurable 0 0 K x₀ 2).aemeasurable
      (isClosed_eq continuous_snd continuous_const).measurableSet).mpr
    exact Eventually.of_forall (fun p => by
      change control 0 0 K p.1 p.2=0
      simp [BrownianBoundedControlSource.control])

def actualControlFamily (K : ℝ) (hK : 0≤K) : model.ControlFamily (Policy K) where
  run := run K hK
  selectorPolicy := selectorPolicy K hK
  selectorRun := selectorRun K hK
  selectorRun_eq := fun _ => rfl

/-- ORIGINAL P-CTL-03 now consumes the constructed SAME-source family. -/
theorem actual_p_ctl_03 (K : ℝ) (hK : 0≤K) : (actualControlFamily K hK).IsOptimalValue :=
  UEOT.V3.DiffusionHJBVerification.p_ctl_03 model (actualControlFamily K hK)

theorem actual_selector_reward (K : ℝ) (hK : 0≤K) (x₀ : ℝ) :
    (run K hK (selectorPolicy K hK) x₀).infiniteReward=2+Real.sin x₀ :=
  (actual_p_ctl_03 K hK x₀).2

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledHJBSource
