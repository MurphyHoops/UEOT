import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledOccupationSource
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Original commitment: original ItoRun infinite reward must be the actual reward of the same state/action path and fixed source measure.
Existing result: literal discounted occupation from dtU×Q_A has exact native Fubini identity at every U.
Premise reduced: derive integrability and finite-occupation reward convergence from positive discount and a reward bound along permitted actual actions.
Model/witness: fixed Q_A, actual X=x0+σB and original clipped predictable control, arbitrary measurable bounded-on-readout reward, rho>0 including zero cut/read horizons.
Consumer/boundary: original ItoRun infiniteReward/reward_tendsto; no reward limit/normalization certificate is an input, no generic unbounded reward claim.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledInfiniteRewardSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianTimeIntegrand BrownianPredictableInputs BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianBoundedC2DynkinSource BrownianControlledTestInput BrownianControlledDiscountSource BrownianControlledOccupationSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def infiniteInputLaw (A : ℝ≥0) (b : fullPredictableL2 A) : Measure (ℝ × (ℝ≥0 → ℝ)) :=
  (volume.restrict (Ici (0 : ℝ))).prod (fullLaw A b)

def infiniteReward (A : ℝ≥0) (b : fullPredictableL2 A) (K x₀ σ ρ : ℝ) (H : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p, discount ρ p.1*H (jointReadout A b K x₀ σ p) ∂infiniteInputLaw A b

variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K)
    (x₀ σ ρ : ℝ) (hρ : 0<ρ) (H : ℝ × ℝ → ℝ) (hH : Measurable H)
    (C : ℝ) (hC : ∀ p, ‖H (jointReadout A b K x₀ σ p)‖≤C)
include hK hB hρ hH C hC

/-- Actual positive-discount integrability, not an assumed convergent reward. -/
theorem reward_integrable_infinite :
    Integrable (fun p => discount ρ p.1*H (jointReadout A b K x₀ σ p)) (infiniteInputLaw A b) := by
  let _ := fullLaw_probability A b K hK hB
  have hd : Integrable (discount ρ) (volume.restrict (Ici (0 : ℝ))) := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    exact integrableOn_exp_mul_Ioi (neg_neg_of_pos hρ) 0
  have hm : Measurable (fun p : ℝ × (ℝ≥0 → ℝ) => discount ρ p.1*H (jointReadout A b K x₀ σ p)) := by
    exact (show Measurable (fun p : ℝ × (ℝ≥0 → ℝ) => discount ρ p.1) by unfold discount; fun_prop).mul
      (hH.comp (jointReadout_measurable A b K x₀ σ))
  apply ((hd.mul_prod (integrable_const C)).mono' hm.aestronglyMeasurable)
  exact Eventually.of_forall (fun p => by
    change ‖discount ρ p.1*H (jointReadout A b K x₀ σ p)‖≤discount ρ p.1*C
    have hp : 0<discount ρ p.1 := Real.exp_pos _
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left (hC p) (Real.exp_pos _).le)

/-- Native Fubini identifies the actual infinite path reward with its actual expected time integral. -/
theorem infiniteReward_eq_time : infiniteReward A b K x₀ σ ρ H=
    ∫ t in Ici (0 : ℝ), discount ρ t*(∫ ω, H (state x₀ σ t ω,control A b K t ω) ∂fullLaw A b) := by
  let _ := fullLaw_probability A b K hK hB
  apply (integral_prod _ (reward_integrable_infinite A b K hK hB x₀ σ ρ hρ H hH C hC)).trans
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change (∫ ω, discount ρ t*H (state x₀ σ t ω,control A b K t ω) ∂fullLaw A b)=_
    exact integral_const_mul _ _)

/-- The original natural-horizon reward convergence is derived by the native improper-integral limit on the same fixed Q_A. -/
theorem actual_reward_tendsto : Tendsto
    (fun n : ℕ => ∫ z, H z ∂occupation A b K x₀ σ ρ (n : ℝ≥0)) atTop
    (𝓝 (infiniteReward A b K x₀ σ ρ H)) := by
  let _ := fullLaw_probability A b K hK hB
  have hi := (reward_integrable_infinite A b K hK hB x₀ σ ρ hρ H hH C hC).integral_prod_left
  have he : IntegrableOn (fun t => discount ρ t*(∫ ω, H (state x₀ σ t ω,control A b K t ω) ∂fullLaw A b)) (Ici (0 : ℝ)) := by
    apply hi.congr
    exact Eventually.of_forall (fun t => by
      change (∫ ω, discount ρ t*H (state x₀ σ t ω,control A b K t ω) ∂fullLaw A b)=_
      exact integral_const_mul _ _)
  rw [infiniteReward_eq_time A b K hK hB x₀ σ ρ hρ H hH C hC]
  have ht := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    ((integrableOn_Ici_iff_integrableOn_Ioi).mp he) tendsto_natCast_atTop_atTop
  rw [← integral_Ici_eq_integral_Ioi] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only
    symm
    rw [occupation_integral A b K hK hB x₀ σ ρ hρ.le (n : ℝ≥0) H hH C hC]
    change (∫ t, _ ∂volume.restrict (Icc (0 : ℝ) (n : ℝ)))=_
    rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (Nat.cast_nonneg n)])

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledInfiniteRewardSource
