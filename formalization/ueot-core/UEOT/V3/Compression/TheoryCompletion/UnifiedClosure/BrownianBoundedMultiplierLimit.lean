import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableMultiplier

/-!
Original commitment: actual Ito source requires convergence of bounded causal coefficient approximations multiplying SAME original input.
Existing result: original native predictable multiplier, full integration and actual continuous integral output.
Premise reduced: derive actual product-input L2 convergence and actual integral convergence from bounded coefficient AE convergence.
Model/witness: SAME original inputLaw T/sourceLaw/naturalFiltration and fullPredictableL2 f, no L4 or product-output certificate.
Consumer: true left-weighted integral increment limit; concrete sampling coefficient convergence and actual increment binding remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedMultiplierLimit
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralMartingale BrownianIntegralContinuousVersion BrownianPredictableMultiplier
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Ambient integrability is derived from ORIGINAL predictable permission
and original product-source AE bound. -/
theorem boundedCoefficient_memLp (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ)
    (hp : AEStronglyMeasurable[predictableSigma] H (inputLaw T))
    (K : ℝ) (hb : ∀ᵐ p ∂inputLaw T, ‖H p‖ ≤ K) : MemLp H ∞ (inputLaw T) :=
  memLp_top_of_bound (AEStronglyMeasurable.mono predictableSigma_le hp) K hb

def boundedMultiplier (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ)
    (hp : AEStronglyMeasurable[predictableSigma] H (inputLaw T))
    (K : ℝ) (hb : ∀ᵐ p ∂inputLaw T, ‖H p‖ ≤ K) :
    fullPredictableL2 T →L[ℝ] fullPredictableL2 T :=
  inputMultiplier T H (boundedCoefficient_memLp T H hp K hb) hp

theorem boundedMultiplier_coe (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ)
    (hp : AEStronglyMeasurable[predictableSigma] H (inputLaw T))
    (K : ℝ) (hb : ∀ᵐ p ∂inputLaw T, ‖H p‖ ≤ K) (f : fullPredictableL2 T) :
    (boundedMultiplier T H hp K hb f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      fun p => H p*(f : Lp ℝ 2 (inputLaw T)) p := inputMultiplier_coe T H _ hp f

/-- Bounded coefficient convergence is consumed on the SAME original input;
only the integrand's original L2 assumption enters dominated convergence. -/
theorem boundedMultiplier_tendsto (T : ℝ≥0)
    (H : ℕ → ℝ × (ℝ≥0 → ℝ) → ℝ) (G : ℝ × (ℝ≥0 → ℝ) → ℝ)
    (hHp : ∀ n, AEStronglyMeasurable[predictableSigma] (H n) (inputLaw T))
    (hGp : AEStronglyMeasurable[predictableSigma] G (inputLaw T))
    (K : ℝ) (hK : 0 ≤ K)
    (hHb : ∀ n, ∀ᵐ p ∂inputLaw T, ‖H n p‖ ≤ K) (hGb : ∀ᵐ p ∂inputLaw T, ‖G p‖ ≤ K)
    (hlim : ∀ᵐ p ∂inputLaw T, Tendsto (fun n => H n p) atTop (𝓝 (G p)))
    (f : fullPredictableL2 T) :
    Tendsto (fun n => boundedMultiplier T (H n) (hHp n) K (hHb n) f) atTop
      (𝓝 (boundedMultiplier T G hGp K hGb f)) := by
  let F : ℕ → Lp ℝ 2 (inputLaw T) := fun n => boundedMultiplier T (H n) (hHp n) K (hHb n) f
  let g : Lp ℝ 2 (inputLaw T) := boundedMultiplier T G hGp K hGb f
  have hid (n : ℕ) : ‖F n-g‖^2 = ∫ p, ((H n p-G p)*(f : Lp ℝ 2 (inputLaw T)) p)^2 ∂inputLaw T := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F n) g,boundedMultiplier_coe T (H n) (hHp n) K (hHb n) f,
      boundedMultiplier_coe T G hGp K hGb f] with p hd hf hg
    simp only [Pi.sub_apply] at hd
    rw [hd]
    change ((boundedMultiplier T (H n) (hHp n) K (hHb n) f : Lp ℝ 2 (inputLaw T)) p-
      (boundedMultiplier T G hGp K hGb f : Lp ℝ 2 (inputLaw T)) p)^2 = _
    rw [hf,hg]
    ring
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun p => ((H n p-G p)*(f : Lp ℝ 2 (inputLaw T)) p)^2) (inputLaw T) :=
    (((boundedCoefficient_memLp T (H n) (hHp n) K (hHb n)).aestronglyMeasurable.sub
      (boundedCoefficient_memLp T G hGp K hGb).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable (f : Lp ℝ 2 (inputLaw T)))).pow 2
  have hb (n : ℕ) : ∀ᵐ p ∂inputLaw T,
      ‖((H n p-G p)*(f : Lp ℝ 2 (inputLaw T)) p)^2‖ ≤ (2*K)^2*(f : Lp ℝ 2 (inputLaw T)) p^2 := by
    filter_upwards [hHb n,hGb] with p hH hG
    have hd : ‖H n p-G p‖ ≤ 2*K := (norm_sub_le _ _).trans (by linarith)
    rw [norm_pow,norm_mul,mul_pow]
    have hh : ‖H n p-G p‖^2 ≤ (2*K)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
    simpa only [Real.norm_eq_abs,sq_abs] using mul_le_mul_of_nonneg_right hh (sq_nonneg ‖(f : Lp ℝ 2 (inputLaw T)) p‖)
  have hl : ∀ᵐ p ∂inputLaw T, Tendsto
      (fun n => ((H n p-G p)*(f : Lp ℝ 2 (inputLaw T)) p)^2) atTop (𝓝 0) := by
    filter_upwards [hlim] with p hp
    have h := ((hp.sub_const (G p)).mul_const ((f : Lp ℝ 2 (inputLaw T)) p)).pow 2
    simpa only [sub_self,zero_mul,zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
  have hi := ((Lp.memLp (f : Lp ℝ 2 (inputLaw T))).integrable_sq).const_mul ((2*K)^2)
  have hmean : Tendsto (fun n => ‖F n-g‖^2) atTop (𝓝 0) :=
    (tendsto_congr' (Eventually.of_forall hid)).mpr (by
      simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
        (fun p => (2*K)^2*(f : Lp ℝ 2 (inputLaw T)) p^2) hm hi hb hl)
  apply tendsto_subtype_rng.mpr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := Real.continuous_sqrt.tendsto (0 : ℝ) |>.comp hmean
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hs

theorem boundedMultipliedIntegral_tendsto (T : ℝ≥0)
    (H : ℕ → ℝ × (ℝ≥0 → ℝ) → ℝ) (G : ℝ × (ℝ≥0 → ℝ) → ℝ)
    (hHp : ∀ n, AEStronglyMeasurable[predictableSigma] (H n) (inputLaw T))
    (hGp : AEStronglyMeasurable[predictableSigma] G (inputLaw T))
    (K : ℝ) (hK : 0 ≤ K)
    (hHb : ∀ n, ∀ᵐ p ∂inputLaw T, ‖H n p‖ ≤ K) (hGb : ∀ᵐ p ∂inputLaw T, ‖G p‖ ≤ K)
    (hlim : ∀ᵐ p ∂inputLaw T, Tendsto (fun n => H n p) atTop (𝓝 (G p)))
    (f : fullPredictableL2 T) :
    Tendsto (fun n => predictableIntegral T (boundedMultiplier T (H n) (hHp n) K (hHb n) f)) atTop
      (𝓝 (predictableIntegral T (boundedMultiplier T G hGp K hGb f))) :=
  ((predictableIntegral T).continuous.tendsto _).comp (boundedMultiplier_tendsto T H G hHp hGp K hK hHb hGb hlim f)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedMultiplierLimit
