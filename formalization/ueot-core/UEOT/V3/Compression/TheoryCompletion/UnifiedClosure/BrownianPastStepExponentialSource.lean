import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianGaussianTiltSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOneStepIntegral
import Mathlib.Probability.Kernel.CondDistrib

/-!
Original commitment: a random START-past coefficient needs actual conditional Esscher normalization, not a true-exponential field.
Existing result: SAME actual Brownian whole-past independent increments and exact Gaussian Esscher law.
Premise reduced: derive actual one-block exponential integrability, conditional mean one and normalized changed measure with unchanged START past.
Model/witness: actual H measurable in original F_a, interval a<=b, SAME I=H*(B_b-B_a); bounded feedback coefficients form the intended next consumer class.
Consumer: one-step random-coefficient joint-past Girsanov shift; finite/simple/general predictable control remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepExponentialSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianGaussianTiltSource BrownianOneStepIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def gaussianStepExp (c : ℝ) (d : ℝ≥0) (z : ℝ) : ℝ := Real.exp (c*z-c^2*(d : ℝ)/2)

private theorem gaussianStepExp_integrable (c : ℝ) (d : ℝ≥0) : Integrable (gaussianStepExp c d) (gaussianReal 0 d) := by
  have he : gaussianStepExp c d = fun z => Real.exp (c*z)*Real.exp (-(c^2*(d : ℝ)/2)) := by
    funext z
    simp only [gaussianStepExp,sub_eq_add_neg,Real.exp_add]
  rw [he]
  exact (integrable_exp_mul_gaussianReal c).mul_const _

private theorem gaussianStepExp_mean_one (c : ℝ) (d : ℝ≥0) :
    (∫ z, gaussianStepExp c d z ∂gaussianReal 0 d)=1 := by
  simp only [gaussianStepExp,sub_eq_add_neg,Real.exp_add,integral_mul_const]
  change mgf id (gaussianReal 0 d) c*Real.exp (-(c^2*(d : ℝ)/2))=1
  rw [mgf_id_gaussianReal,← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

/-- Actual exponent uses the same original one-step integral, coefficient
and elapsed clock; there is no separately returned candidate integral. -/
def stepExponential (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  Real.exp (oneStep H a b ω-H ω^2*((b-a : ℝ≥0) : ℝ)/2)

private theorem increment_condDistrib (a b : ℝ≥0) (hab : a ≤ b) :
    @condDistrib (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance inferInstance inferInstance
      inferInstance (naturalFiltration a) (increment a b) id sourceLaw inferInstance
      =ᵐ[@Measure.map (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) id sourceLaw]
        @Kernel.const (ℝ≥0 → ℝ) ℝ (naturalFiltration a) inferInstance (gaussianReal 0 (b-a)) := by
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) id :=
    measurable_id'' (naturalFiltration.le a)
  have hida : @AEMeasurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) (naturalFiltration a) inferInstance id sourceLaw :=
    ⟨id,hid,Eventually.of_forall (fun _ => rfl)⟩
  have hi : Indep (MeasurableSpace.comap (increment a b) inferInstance) (naturalFiltration a) sourceLaw := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact increment_indep_past a b hab
  have hi' : @IndepFun (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance (naturalFiltration a) inferInstance id (increment a b) sourceLaw := by
    change Indep (MeasurableSpace.comap id (naturalFiltration a)) (MeasurableSpace.comap (increment a b) inferInstance) sourceLaw
    rw [MeasurableSpace.comap_id]
    exact hi.symm
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hid (measurable_increment a b)
  rw [Measure.compProd_const,← (increment_hasLaw a b hab).map_eq]
  exact @IndepFun.map_prod_eq_prod_map_map (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance sourceLaw
    id (increment a b) (naturalFiltration a) inferInstance inferInstance hida (measurable_increment a b).aemeasurable hi'

/-- Actual normalization under the ENTIRE original START past, allowing H
to depend on that past. No independence between H and the past is assumed. -/
theorem stepExponential_condExp (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    Integrable (stepExponential H a b) sourceLaw ∧
      sourceLaw[stepExponential H a b | naturalFiltration a] =ᵐ[sourceLaw] fun _ => 1 := by
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) id :=
    measurable_id'' (naturalFiltration.le a)
  have hida : @AEMeasurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) (naturalFiltration a) inferInstance id sourceLaw :=
    ⟨id,hid,Eventually.of_forall (fun _ => rfl)⟩
  let F : (ℝ≥0 → ℝ) × ℝ → ℝ := fun p => gaussianStepExp (H p.1) (b-a) p.2
  have hF : @StronglyMeasurable ((ℝ≥0 → ℝ) × ℝ) ℝ inferInstance ((naturalFiltration a).prod inferInstance) F := by
    exact (Real.measurable_exp.comp (((hH.measurable.comp measurable_fst).mul measurable_snd).sub
      ((((hH.measurable.comp measurable_fst).pow_const 2).mul measurable_const).div_const 2))).stronglyMeasurable
  let G : ℝ × ℝ → ℝ := fun p => gaussianStepExp p.1 (b-a) p.2
  have hG : StronglyMeasurable G := by unfold G gaussianStepExp; fun_prop
  have hHg : Measurable H := (hH.mono (naturalFiltration.le a)).measurable
  have hnorm (c : ℝ) : (∫ z, ‖G (c,z)‖ ∂gaussianReal 0 (b-a))=1 := by
    have he : (fun z => ‖G (c,z)‖)=gaussianStepExp c (b-a) := by
      funext z
      exact Real.norm_of_nonneg (Real.exp_pos _).le
    rw [he]
    exact gaussianStepExp_mean_one _ _
  have hGp : Integrable G ((sourceLaw.map H).prod (gaussianReal 0 (b-a))) := by
    apply (integrable_prod_iff hG.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun c => gaussianStepExp_integrable c (b-a)),?_⟩
    have he : (fun c => ∫ z, ‖G (c,z)‖ ∂gaussianReal 0 (b-a))=fun _ => (1 : ℝ) := funext hnorm
    rw [he]
    exact integrable_const _
  have hiFs : Indep (naturalFiltration a) (MeasurableSpace.comap (increment a b) inferInstance) sourceLaw := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact (increment_indep_past a b hab).symm
  have hiH : IndepFun H (increment a b) sourceLaw :=
    indep_of_indep_of_le_left hiFs hH.measurable.comap_le
  have hmap : sourceLaw.map (fun ω => (H ω,increment a b ω)) =
      (sourceLaw.map H).prod (gaussianReal 0 (b-a)) := by
    rw [hiH.map_prod_eq_prod_map_map hHg.aemeasurable (measurable_increment a b).aemeasurable,
      (increment_hasLaw a b hab).map_eq]
  have hFi : Integrable (fun ω => F (id ω,increment a b ω)) sourceLaw :=
    (integrable_map_measure hG.aestronglyMeasurable (hHg.prodMk (measurable_increment a b)).aemeasurable).mp (hmap.symm ▸ hGp)
  have he : (fun ω => F (id ω,increment a b ω))=stepExponential H a b := rfl
  have hc := condExp_prod_ae_eq_integral_condDistrib hid (measurable_increment a b).aemeasurable hF hFi
  rw [MeasurableSpace.comap_id,he] at hc
  have hkern := @ae_of_ae_map (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a)
    sourceLaw id hida _ (increment_condDistrib a b hab)
  refine ⟨he ▸ hFi,?_⟩
  filter_upwards [hc,hkern] with ω hc hkern
  rw [hkern] at hc
  exact hc.trans (gaussianStepExp_mean_one (H ω) (b-a))

theorem stepExponential_pos (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    0 < stepExponential H a b ω := Real.exp_pos _

theorem stepExponential_end_past (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    StronglyMeasurable[naturalFiltration b] (stepExponential H a b) := by
  have hh := hH.mono (naturalFiltration.mono hab)
  have hy := (process_stronglyAdapted b).sub ((process_stronglyAdapted a).mono (naturalFiltration.mono hab))
  change StronglyMeasurable[naturalFiltration b] (fun ω => Real.exp (H ω*increment a b ω-H ω^2*((b-a : ℝ≥0) : ℝ)/2))
  simp only [div_eq_mul_inv]
  exact Real.continuous_exp.comp_stronglyMeasurable ((hh.mul hy).sub (((hh.pow 2).mul stronglyMeasurable_const).mul stronglyMeasurable_const))

theorem stepExponential_mean_one (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    (∫ ω, stepExponential H a b ω ∂sourceLaw)=1 := by
  rw [← integral_condExp (naturalFiltration.le a),
    integral_congr_ae (stepExponential_condExp H a b hab hH).2]
  simp

def stepLaw (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) : Measure (ℝ≥0 → ℝ) :=
  sourceLaw.withDensity (fun ω => ENNReal.ofReal (stepExponential H a b ω))

theorem stepLaw_probability (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) : IsProbabilityMeasure (stepLaw H a b) := by
  constructor
  rw [stepLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (stepExponential_condExp H a b hab hH).1
      (Eventually.of_forall (fun ω => (stepExponential_pos H a b ω).le)),stepExponential_mean_one H a b hab hH]
  norm_num

/-- The density changes the actual future increment, while EVERY event in
the original START sigma algebra retains its original probability. -/
theorem stepLaw_agrees_start (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (A : Set (ℝ≥0 → ℝ))
    (hA : MeasurableSet[naturalFiltration a] A) : stepLaw H a b A=sourceLaw A := by
  have hAg : MeasurableSet A := naturalFiltration.le a A hA
  have hi := (stepExponential_condExp H a b hab hH).1
  have hc := (stepExponential_condExp H a b hab hH).2
  have hs : (∫ ω in A,stepExponential H a b ω ∂sourceLaw)=sourceLaw.real A := by
    rw [← setIntegral_condExp (naturalFiltration.le a) hi hA]
    rw [setIntegral_congr_ae hAg (hc.mono (fun _ h _ => h))]
    simp
  rw [stepLaw,withDensity_apply _ hAg,← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (Eventually.of_forall (fun ω => (stepExponential_pos H a b ω).le)),hs]
  exact ENNReal.ofReal_toReal (measure_ne_top sourceLaw A)

/-- In particular the supplied START coefficient itself is not reselected
or filtered by the change of measure. -/
theorem stepLaw_map_coefficient (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) : (stepLaw H a b).map H=sourceLaw.map H := by
  have hg : Measurable H := (hH.mono (naturalFiltration.le a)).measurable
  ext A hA
  rw [Measure.map_apply hg hA,Measure.map_apply hg hA]
  exact stepLaw_agrees_start H a b hab hH _ (hH.measurable hA)

/-- The real one-block energy of a native L2 START coefficient stays
integrable under Q, by its actual preserved law, not by a Q-energy field. -/
theorem stepLaw_square_integrable (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hH₂ : MemLp H 2 sourceLaw) :
    Integrable (fun ω => H ω^2) (stepLaw H a b) := by
  have hg : Measurable H := (hH.mono (naturalFiltration.le a)).measurable
  have hi : Integrable (fun x : ℝ => x^2) (sourceLaw.map H) :=
    (integrable_map_measure (by fun_prop) hg.aemeasurable).2 hH₂.integrable_sq
  rw [← stepLaw_map_coefficient H a b hab hH] at hi
  exact (integrable_map_measure (by fun_prop) hg.aemeasurable).1 hi

/-- The same-time boundary has literal density one, even before using any
START measurability premise. -/
theorem stepLaw_same_time (H : (ℝ≥0 → ℝ) → ℝ) (a : ℝ≥0) : stepLaw H a a=sourceLaw := by
  have he : (fun ω => ENNReal.ofReal (stepExponential H a a ω))=(1 : (ℝ≥0 → ℝ) → ℝ≥0∞) := by
    funext ω
    simp [stepExponential,oneStep,increment]
  rw [stepLaw,he,withDensity_one]

/-- Exact compatibility with the previously constructed constant-control
finite-horizon source, by the same original zero-time Brownian identity. -/
theorem stepLaw_const_zero (u : ℝ) (T : ℝ≥0) : stepLaw (fun _ => u) 0 T=tiltedLaw u T := by
  rw [stepLaw,tiltedLaw]
  apply withDensity_congr_ae
  filter_upwards [process_zero] with ω hω
  change ENNReal.ofReal (Real.exp (u*(process T ω-process 0 ω)-u^2*((T-0 : ℝ≥0) : ℝ)/2)) =
    ENNReal.ofReal (Real.exp (u*process T ω-u^2*(T : ℝ)/2))
  simp only [hω,sub_zero,tsub_zero]

/-- Literal clock-time energy of the SAME coefficient on the one block. -/
def stepEnergy (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∫ _t : ℝ in (a : ℝ)..(b : ℝ), ‖H ω‖^2

theorem stepEnergy_eq (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    stepEnergy H a b ω=(H ω)^2*((b : ℝ)-(a : ℝ)) := by
  simp only [stepEnergy,intervalIntegral.integral_const,smul_eq_mul,Real.norm_eq_abs,sq_abs]
  ring

theorem stepLaw_energy_integrable (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hH₂ : MemLp H 2 sourceLaw) :
    Integrable (stepEnergy H a b) (stepLaw H a b) := by
  have he : stepEnergy H a b=fun ω => (H ω)^2*((b : ℝ)-(a : ℝ)) := funext (stepEnergy_eq H a b)
  rw [he]
  exact (stepLaw_square_integrable H a b hab hH hH₂).mul_const _

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepExponentialSource
