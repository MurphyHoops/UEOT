import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMartingaleSource

/-!
Original commitment: the existing actual OU source needs its transition mechanism derived, not only marginal moments.
Existing result: SAME ouSource/ouClock and actual continuous Brownian source with independent whole-natural-past increments.
Premise reduced: derive actual affine innovation, conditional law and conditional moments from this original source.
Model/witness: k>0, arbitrary real noise/initial state; explicit time-changed filtration F_(ouClock k t), nonzero-noise witness.
Consumer: actual OU conditional transition/semigroup source; original-time driving SDE and general drift/Ito/Girsanov remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUConditionalInnovationSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianContinuousSource OUQuadraticDynkinSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

theorem ouClock_coe (k : ℝ) (hk : 0 < k) (t : ℝ≥0) :
    (ouClock k t : ℝ) = (Real.exp (2*k*(t : ℝ))-1)/(2*k) := by
  apply Real.coe_toNNReal
  exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))) (by positivity)

theorem ouClock_mono (k : ℝ) (hk : 0 < k) : Monotone (ouClock k) := by
  intro s t hst
  apply Real.toNNReal_mono
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2*k)
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (show (s : ℝ) ≤ (t : ℝ) from hst) (by positivity)

/-- The source clock is changed explicitly. There is no claim that the
future original Brownian readout belongs to its earlier original F_t. -/
def ouFiltration (k : ℝ) (hk : 0 < k) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) where
  seq t := naturalFiltration (ouClock k t)
  mono' := fun _ _ h => naturalFiltration.mono (ouClock_mono k hk h)
  le' := fun t => naturalFiltration.le (ouClock k t)

/-- SAME adopted actual process; no replacement law or alternative OU is chosen. -/
def actualOU (k σ x₀ : ℝ) : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := ouSource process k σ x₀

def decay (k : ℝ) (s t : ℝ≥0) : ℝ := Real.exp (-k*((t : ℝ)-(s : ℝ)))

def innovation (k σ : ℝ) (s t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  (Real.exp (-k*(t : ℝ))*σ)*increment (ouClock k s) (ouClock k t) ω

/-- Actual finite-time conditional variance, computed from the original
Brownian clock rather than supplied as a source field. -/
def transitionVariance (k σ : ℝ) (s t : ℝ≥0) : ℝ≥0 :=
  ⟨(Real.exp (-k*(t : ℝ))*σ)^2,sq_nonneg _⟩*
    nndist (ouClock k t : ℝ) (ouClock k s : ℝ)

theorem decay_mul (k : ℝ) (s t : ℝ≥0) :
    decay k s t*Real.exp (-k*(s : ℝ)) = Real.exp (-k*(t : ℝ)) := by
  rw [decay,← Real.exp_add]
  congr 1
  ring

/-- Literal state identity before any expectation or conditional-law argument. -/
theorem actualOU_transition_decomposition (k σ x₀ : ℝ) (s t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    actualOU k σ x₀ t ω = decay k s t*actualOU k σ x₀ s ω+innovation k σ s t ω := by
  unfold actualOU ouSource innovation increment
  rw [mul_add,← mul_assoc,decay_mul]
  rw [← mul_assoc (decay k s t),← mul_assoc (decay k s t),decay_mul]
  ring

theorem actualOU_stronglyAdapted (k σ x₀ : ℝ) (hk : 0 < k) :
    StronglyAdapted (ouFiltration k hk) (actualOU k σ x₀) := by
  intro t
  exact stronglyMeasurable_const.add (stronglyMeasurable_const.mul (process_stronglyAdapted (ouClock k t)))

theorem actualOU_memLp_two (k σ x₀ : ℝ) (t : ℝ≥0) : MemLp (actualOU k σ x₀ t) 2 sourceLaw := by
  change MemLp (fun ω => Real.exp (-k*(t : ℝ))*x₀+(Real.exp (-k*(t : ℝ))*σ)*process (ouClock k t) ω) 2 sourceLaw
  have hg : MemLp (process (ouClock k t)) 2 sourceLaw :=
    (process_isPreBrownian.hasLaw_eval (ouClock k t)).hasGaussianLaw.memLp_two
  exact (memLp_const (Real.exp (-k*(t : ℝ))*x₀)).add (hg.const_mul (Real.exp (-k*(t : ℝ))*σ))

/-- Full original time-changed natural past independence, not independence
only of the single current OU state or of one original Brownian coordinate. -/
theorem innovation_indep_whole_past (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (innovation k σ s t) (fun ω (r : Iic (ouClock k s)) => process r ω) sourceLaw := by
  exact (increment_indep_past (ouClock k s) (ouClock k t) (ouClock_mono k hk hst)).comp
    (measurable_const.mul measurable_id) measurable_id

theorem innovation_hasLaw (k σ : ℝ) (s t : ℝ≥0) :
    HasLaw (innovation k σ s t) (gaussianReal 0 (transitionVariance k σ s t)) sourceLaw := by
  have h := gaussianReal_const_mul (process_isPreBrownian.hasLaw_sub (ouClock k t) (ouClock k s))
    (Real.exp (-k*(t : ℝ))*σ)
  change HasLaw (innovation k σ s t)
    (gaussianReal ((Real.exp (-k*(t : ℝ))*σ)*0) (transitionVariance k σ s t)) sourceLaw at h
  simpa only [mul_zero] using h

/-- Conditional expectation of every measurable innovation transform is its
actual Gaussian expectation under the whole original time-changed past.
Consumers needing ordinary expectations retain their integrability condition. -/
theorem innovation_condExp_transform (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    sourceLaw[fun ω => φ (innovation k σ s t ω) | ouFiltration k hk s] =ᵐ[sourceLaw]
      fun _ => ∫ x, φ x ∂gaussianReal 0 (transitionVariance k σ s t) := by
  have hc := condExp_increment_function (ouClock k s) (ouClock k t) (ouClock_mono k hk hst)
    (fun x => φ ((Real.exp (-k*(t : ℝ))*σ)*x)) (hφ.comp (measurable_const.mul measurable_id))
  change sourceLaw[fun ω => φ (innovation k σ s t ω) | ouFiltration k hk s] =ᵐ[sourceLaw]
    fun _ => ∫ ω, φ (innovation k σ s t ω) ∂sourceLaw at hc
  exact hc.trans (Eventually.of_forall (fun _ => (innovation_hasLaw k σ s t).integral_comp hφ.aestronglyMeasurable))

/-- The same residual is an actual affine function of the same original OU
states; this identifies a conditional transition statement, not just marginals. -/
theorem actualOU_condExp_residual (k σ x₀ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    sourceLaw[fun ω => φ (actualOU k σ x₀ t ω-decay k s t*actualOU k σ x₀ s ω) | ouFiltration k hk s]
      =ᵐ[sourceLaw] fun _ => ∫ x, φ x ∂gaussianReal 0 (transitionVariance k σ s t) := by
  have he : (fun ω => φ (actualOU k σ x₀ t ω-decay k s t*actualOU k σ x₀ s ω)) =
      fun ω => φ (innovation k σ s t ω) := by
    funext ω
    rw [actualOU_transition_decomposition]
    congr 1
    ring
  rw [he]
  exact innovation_condExp_transform k σ hk s t hst φ hφ

/-- The finite-time variance is the genuine OU elapsed-time expression. -/
theorem transitionVariance_coe (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t) :
    (transitionVariance k σ s t : ℝ) = σ^2/(2*k)*(1-Real.exp (-2*k*((t : ℝ)-(s : ℝ)))) := by
  have hclock : (ouClock k s : ℝ) ≤ (ouClock k t : ℝ) := ouClock_mono k hk hst
  have he : Real.exp (-k*(t : ℝ))^2 = Real.exp (-2*k*(t : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have ht : Real.exp (-2*k*(t : ℝ))*Real.exp (2*k*(t : ℝ)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hs : Real.exp (-2*k*(t : ℝ))*Real.exp (2*k*(s : ℝ)) =
      Real.exp (-2*k*((t : ℝ)-(s : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change (Real.exp (-k*(t : ℝ))*σ)^2*(nndist (ouClock k t : ℝ) (ouClock k s : ℝ) : ℝ) = _
  rw [coe_nndist,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hclock),ouClock_coe k hk t,ouClock_coe k hk s,mul_pow,he]
  calc
    _ = σ^2/(2*k)*(Real.exp (-2*k*(t : ℝ))*(Real.exp (2*k*(t : ℝ))-Real.exp (2*k*(s : ℝ)))) := by
      field_simp [ne_of_gt hk]
      ring
    _ = _ := by rw [mul_sub,ht,hs]

theorem innovation_condExp_zero (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[innovation k σ s t | ouFiltration k hk s] =ᵐ[sourceLaw] fun _ => 0 := by
  simpa only [id_eq,integral_id_gaussianReal] using innovation_condExp_transform k σ hk s t hst id measurable_id

theorem innovation_condExp_square (k σ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[fun ω => (innovation k σ s t ω)^2 | ouFiltration k hk s] =ᵐ[sourceLaw]
      fun _ => σ^2/(2*k)*(1-Real.exp (-2*k*((t : ℝ)-(s : ℝ)))) := by
  have hsecond : (∫ x : ℝ, x^2 ∂gaussianReal 0 (transitionVariance k σ s t)) =
      (transitionVariance k σ s t : ℝ) := by
    have h := variance_id_gaussianReal (μ := 0) (v := transitionVariance k σ s t)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simpa only [id_eq,integral_id_gaussianReal,sub_zero] using h
  exact (innovation_condExp_transform k σ hk s t hst (fun x => x^2) (by fun_prop)).trans
    (Eventually.of_forall (fun _ => hsecond.trans (transitionVariance_coe k σ hk s t hst)))

theorem innovation_memLp_two (k σ : ℝ) (s t : ℝ≥0) : MemLp (innovation k σ s t) 2 sourceLaw :=
  (innovation_hasLaw k σ s t).hasGaussianLaw.memLp_two

/-- Actual conditional first moment of the original OU process under its
whole time-changed natural past, not an independently supplied moment. -/
theorem actualOU_condExp_mean (k σ x₀ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[actualOU k σ x₀ t | ouFiltration k hk s] =ᵐ[sourceLaw]
      fun ω => decay k s t*actualOU k σ x₀ s ω := by
  have he : actualOU k σ x₀ t = (fun ω => decay k s t*actualOU k σ x₀ s ω)+innovation k σ s t :=
    funext (actualOU_transition_decomposition k σ x₀ s t)
  rw [he]
  have hp : StronglyMeasurable[ouFiltration k hk s] (fun ω => decay k s t*actualOU k σ x₀ s ω) :=
    stronglyMeasurable_const.mul (actualOU_stronglyAdapted k σ x₀ hk s)
  have hi := ((actualOU_memLp_two k σ x₀ s).integrable (by norm_num)).const_mul (decay k s t)
  have hz := innovation_condExp_zero k σ hk s t hst
  have hc := condExp_of_stronglyMeasurable (ouFiltration k hk |>.le s) hp hi
  apply (condExp_add hi ((innovation_memLp_two k σ s t).integrable (by norm_num)) (ouFiltration k hk s)).trans
  rw [hc]
  filter_upwards [hz] with ω hω
  simp only [Pi.add_apply,hω,add_zero]

/-- Actual conditional centered second moment of the original OU states.
The residual variance depends only on the elapsed physical time. -/
theorem actualOU_condExp_centered_square (k σ x₀ : ℝ) (hk : 0 < k) (s t : ℝ≥0) (hst : s ≤ t) :
    sourceLaw[fun ω => (actualOU k σ x₀ t ω-decay k s t*actualOU k σ x₀ s ω)^2 | ouFiltration k hk s]
      =ᵐ[sourceLaw] fun _ => σ^2/(2*k)*(1-Real.exp (-2*k*((t : ℝ)-(s : ℝ)))) := by
  have he : (fun ω => (actualOU k σ x₀ t ω-decay k s t*actualOU k σ x₀ s ω)^2) =
      fun ω => (innovation k σ s t ω)^2 := by
    funext ω
    rw [actualOU_transition_decomposition]
    ring
  rw [he]
  exact innovation_condExp_square k σ hk s t hst

/-- Strictly positive transition uncertainty is present for every nonzero
noise and positive elapsed clock, not merely in a chosen marginal. -/
theorem transitionVariance_pos (k σ : ℝ) (hk : 0 < k) (hσ : σ ≠ 0) (s t : ℝ≥0) (hst : s < t) :
    0 < (transitionVariance k σ s t : ℝ) := by
  rw [transitionVariance_coe k σ hk s t hst.le]
  apply mul_pos (div_pos (sq_pos_of_ne_zero hσ) (by positivity))
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have ht : (s : ℝ) < (t : ℝ) := hst
  nlinarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUConditionalInnovationSource
