import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledDiscountSource

/-!
Original commitment: original ItoRun occupation/terminal outputs must be constructed from the actual joint state/action source.
Existing result: same fixed ownQ_A has actual discounted controlled C2 expectation at every U and exact real progressive action.
Premise reduced: construct literal discounted dtU×Q_A joint pushforward and terminal law, prove bounded-readout integrability and exact time expectation formula.
Model/witness: X=x0+σB and SAME control b/K, rho≥0, all U including zero, Q and actual action unchanged across horizons.
Consumer/boundary: actual ItoRun reward/drift/terminal fields and selector support; infinite reward/control-family are subsequent derivations, not fields supplied here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledOccupationSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianTimeIntegrand BrownianPredictableInputs BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQBoundedInput BrownianBoundedC2DynkinSource BrownianControlledTestInput BrownianControlledDiscountSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def jointReadout (A : ℝ≥0) (b : fullPredictableL2 A) (K x₀ σ : ℝ) (p : ℝ × (ℝ≥0 → ℝ)) : ℝ × ℝ :=
  (state x₀ σ p.1 p.2,control A b K p.1 p.2)

theorem jointReadout_measurable (A : ℝ≥0) (b : fullPredictableL2 A) (K x₀ σ : ℝ) :
    Measurable (jointReadout A b K x₀ σ) := (state_joint x₀ σ).prodMk (control_joint A b K)

def discountedInputLaw (A : ℝ≥0) (b : fullPredictableL2 A) (ρ : ℝ) (U : ℝ≥0) : Measure (ℝ × (ℝ≥0 → ℝ)) :=
  (inputLawQ A b U).withDensity (fun p => ENNReal.ofReal (discount ρ p.1))

def occupation (A : ℝ≥0) (b : fullPredictableL2 A) (K x₀ σ ρ : ℝ) (U : ℝ≥0) : Measure (ℝ × ℝ) :=
  (discountedInputLaw A b ρ U).map (jointReadout A b K x₀ σ)

def terminalLaw (A : ℝ≥0) (b : fullPredictableL2 A) (x₀ σ : ℝ) (U : ℝ≥0) : Measure ℝ :=
  (fullLaw A b).map (state x₀ σ U)

variable (A : ℝ≥0) (b : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hB : ∀ᵐ p ∂inputLaw A, |(b : Lp ℝ 2 (inputLaw A)) p|≤K)
    (x₀ σ ρ : ℝ) (hρ : 0≤ρ) (U : ℝ≥0)
include hK hB

theorem terminalLaw_probability : IsProbabilityMeasure (terminalLaw A b x₀ σ U) := by
  let _ := fullLaw_probability A b K hK hB
  exact Measure.isProbabilityMeasure_map (state_measurable x₀ σ U).aemeasurable

include hρ
omit hK hB in
private theorem discount_bound : ∀ᵐ p ∂inputLawQ A b U, discount ρ p.1≤1 := by
  filter_upwards [(inputLawQ_absolutelyContinuous A b U).ae_le (time_support_ae U)] with p hp
  apply Real.exp_le_one_iff.mpr
  have ht : 0≤p.1 := hp.1.le
  nlinarith

theorem discountedInputLaw_finite : IsFiniteMeasure (discountedInputLaw A b ρ U) := by
  let _ := fullLaw_probability A b K hK hB
  have : IsFiniteMeasure (inputLawQ A b U) := by unfold inputLawQ; infer_instance
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  apply lt_of_le_of_lt (lintegral_mono_ae ?_) (show (∫⁻ _p, (1 : ℝ≥0∞) ∂inputLawQ A b U)<⊤ by simp)
  filter_upwards [discount_bound A b ρ hρ U] with p hp
  exact (ENNReal.ofReal_le_ofReal hp).trans_eq ENNReal.ofReal_one

/-- SAME actual joint readout is integrable for each bounded permitted test,
with a bound along the actual readout rather than an unrelated occupation law. -/
theorem occupation_integrable (H : ℝ × ℝ → ℝ) (hH : Measurable H) (C : ℝ)
    (hC : ∀ p, ‖H (jointReadout A b K x₀ σ p)‖≤C) :
    Integrable H (occupation A b K x₀ σ ρ U) := by
  let _ := discountedInputLaw_finite A b K hK hB ρ hρ U
  apply (integrable_map_measure hH.aestronglyMeasurable (jointReadout_measurable A b K x₀ σ).aemeasurable).mpr
  exact Integrable.of_bound (hH.comp (jointReadout_measurable A b K x₀ σ)).aestronglyMeasurable C (Eventually.of_forall hC)

/-- Exact native pushforward/withDensity/Fubini formula for the actual
discounted occupation. No desired occupation-integral identity is supplied. -/
theorem occupation_integral (H : ℝ × ℝ → ℝ) (hH : Measurable H) (C : ℝ)
    (hC : ∀ p, ‖H (jointReadout A b K x₀ σ p)‖≤C) :
    (∫ z, H z ∂occupation A b K x₀ σ ρ U)=
      ∫ t, discount ρ t*(∫ ω, H (state x₀ σ t ω,control A b K t ω) ∂fullLaw A b) ∂timeLaw U := by
  let _ := fullLaw_probability A b K hK hB
  have : IsFiniteMeasure (inputLawQ A b U) := by unfold inputLawQ; infer_instance
  have hm : Measurable (fun p : ℝ × (ℝ≥0 → ℝ) => discount ρ p.1) := by unfold discount; fun_prop
  have hWeight : Integrable (fun p => discount ρ p.1*H (jointReadout A b K x₀ σ p)) (inputLawQ A b U) := by
    apply Integrable.of_bound (hm.mul (hH.comp (jointReadout_measurable A b K x₀ σ))).aestronglyMeasurable C
    filter_upwards [discount_bound A b ρ hρ U] with p hp
    change ‖discount ρ p.1*H (jointReadout A b K x₀ σ p)‖≤C
    have hd : 0<discount ρ p.1 := Real.exp_pos _
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos hd]
    exact (mul_le_mul hp (hC p) (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
  rw [occupation,integral_map (jointReadout_measurable A b K x₀ σ).aemeasurable hH.aestronglyMeasurable]
  rw [discountedInputLaw,integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun p : ℝ × (ℝ≥0 → ℝ) => (ENNReal.ofReal (discount ρ p.1)).toReal • H (jointReadout A b K x₀ σ p))=
      fun p => discount ρ p.1*H (jointReadout A b K x₀ σ p) := by
    funext p
    have hd : 0≤discount ρ p.1 := (Real.exp_pos _).le
    rw [ENNReal.toReal_ofReal hd,smul_eq_mul]
  rw [he]
  apply (integral_prod _ hWeight).trans
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change (∫ ω, discount ρ t*H (state x₀ σ t ω,control A b K t ω) ∂fullLaw A b)=
      discount ρ t*(∫ ω, H (state x₀ σ t ω,control A b K t ω) ∂fullLaw A b)
    exact integral_const_mul _ _)

omit hK hB hρ in
/-- Literal terminal law belongs to SAME source run. -/
theorem terminal_integral (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ x, φ x ∂terminalLaw A b x₀ σ U)=∫ ω, φ (state x₀ σ U ω) ∂fullLaw A b :=
  integral_map (state_measurable x₀ σ U).aemeasurable hφ.aestronglyMeasurable

/-- Actual original-type discounted Ito output in the CONSTRUCTED joint
occupation/terminal laws. Global boundedness of phi is the original HJB
model condition; the generator is the actual source-derived formula. -/
theorem actual_discounted_occupation (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (C₁ C₂ : ℝ) (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (hb₁ : ∀ x, ‖deriv φ x‖≤C₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖≤C₂)
    (M : ℝ) (hM : ∀ x, ‖φ x‖≤M) :
    discount ρ U*(∫ x, φ x ∂terminalLaw A b x₀ σ U)=φ x₀+
      ∫ z, BrownianControlledC2Source.controlledGenerator σ φ z.1 z.2-ρ*φ z.1 ∂occupation A b K x₀ σ ρ U := by
  let H := fun z : ℝ × ℝ => BrownianControlledC2Source.controlledGenerator σ φ z.1 z.2-ρ*φ z.1
  have hm : Measurable H :=
    (((measurable_const.mul measurable_snd).mul
      ((hφ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞)≤2)).measurable.comp measurable_fst)).add
      (measurable_const.mul ((hφ.continuous_iteratedDeriv' 2).measurable.comp measurable_fst))).sub
      (measurable_const.mul (hφ.continuous.measurable.comp measurable_fst))
  have hb (p : ℝ × (ℝ≥0 → ℝ)) : ‖H (jointReadout A b K x₀ σ p)‖≤
      BrownianControlledDynkinSource.generatorBound K σ C₁ C₂+|ρ| * M := by
    change ‖BrownianControlledC2Source.controlledGenerator σ φ (state x₀ σ p.1 p.2) (control A b K p.1 p.2)-ρ*φ (state x₀ σ p.1 p.2)‖≤_
    apply (norm_sub_le _ _).trans
    apply add_le_add (BrownianControlledDynkinSource.generator_point_bound A b K hK x₀ σ φ C₁ C₂ hb₁ hb₂ _ _)
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg ρ)
  rw [terminal_integral A b x₀ σ U φ hφ.continuous.measurable,
    occupation_integral A b K hK hB x₀ σ ρ hρ U H hm _ hb]
  exact actual_discounted_expectation A b K hK hB x₀ σ φ hφ C₁ C₂ hC₁ hC₂ hb₁ hb₂ ρ U

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledOccupationSource
