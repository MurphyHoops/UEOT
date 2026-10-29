import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTimeEnergy
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralSquareL1

/-!
Original commitment: general-input quadratic variation must compare the SAME actual time energies at their natural L1 scale.
Existing result: genuine actual timeEnergy/Fubini and original L2-to-square-L1 estimate, with the same cutoff input.
Premise reduced: derive actual time marginal contraction and native L1 continuity of SAME f's timeEnergy.
Model/witness: ONLY original fixed inputLaw T = timeLaw T times sourceLaw; includes T=0 without normalization/division.
Consumer: full-input QV extension and weighted clock/time-energy limits; no L4 or supplied energy transport certificate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralEnergyL1
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralTimeEnergy BrownianIntegralSquareL1
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem lp1_norm_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : Lp ℝ 1 μ) :
    ‖g‖ = ∫ a, ‖g a‖ ∂μ := by
  rw [L1.norm_def,integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable g)]

/-- Actual scalar time marginal, before deriving its native linear bound. -/
private def marginalValue (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw T)) : Lp ℝ 1 sourceLaw :=
  ((L1.integrable_coeFn g).integral_prod_right).toL1 (fun ω => ∫ t, g (t,ω) ∂timeLaw T)

private theorem marginalValue_coe (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw T)) :
    marginalValue T g =ᵐ[sourceLaw] (fun ω => ∫ t, g (t,ω) ∂timeLaw T) :=
  ((L1.integrable_coeFn g).integral_prod_right).coeFn_toL1

private theorem section_eq {g h : ℝ × (ℝ≥0 → ℝ) → ℝ} (he : g =ᵐ[inputLaw T] h) :
    ∀ᵐ ω ∂sourceLaw, (fun t => g (t,ω)) =ᵐ[timeLaw T] fun t => h (t,ω) :=
  Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw T)).quasiMeasurePreserving.ae he)

private def marginalLinear (T : ℝ≥0) : Lp ℝ 1 (inputLaw T) →ₗ[ℝ] Lp ℝ 1 sourceLaw where
  toFun := marginalValue T
  map_add' g h := by
    apply Lp.ext
    have he := section_eq (Lp.coeFn_add g h)
    filter_upwards [marginalValue_coe T (g+h),Lp.coeFn_add (marginalValue T g) (marginalValue T h),
      marginalValue_coe T g,marginalValue_coe T h,he,
      (L1.integrable_coeFn g).prod_left_ae,(L1.integrable_coeFn h).prod_left_ae]
      with ω hm hs hg hh he ig ih
    simp only [Pi.add_apply] at hs he
    rw [hm,hs,hg,hh]
    exact (integral_congr_ae he).trans (integral_add ig ih)
  map_smul' c g := by
    apply Lp.ext
    have he := section_eq (Lp.coeFn_smul c g)
    filter_upwards [marginalValue_coe T (c • g),Lp.coeFn_smul c (marginalValue T g),
      marginalValue_coe T g,he] with ω hm hs hg he
    simp only [Pi.smul_apply,smul_eq_mul] at hs he
    simp only [RingHom.id_apply]
    rw [hm,hs,hg,integral_congr_ae he,integral_const_mul]

private theorem marginalValue_bound (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw T)) : ‖marginalValue T g‖ ≤ ‖g‖ := by
  calc
    _ = ∫ ω, ‖∫ t, g (t,ω) ∂timeLaw T‖ ∂sourceLaw := by
      rw [lp1_norm_integral]
      exact integral_congr_ae ((marginalValue_coe T g).mono (fun _ h => congrArg norm h))
    _ ≤ ∫ ω, ∫ t, ‖g (t,ω)‖ ∂timeLaw T ∂sourceLaw :=
      integral_mono (L1.integrable_coeFn g).integral_prod_right.norm
        (L1.integrable_coeFn g).integral_norm_prod_right (fun _ => norm_integral_le_integral_norm _)
    _ = ∫ p, ‖g p‖ ∂inputLaw T :=
      (integral_prod_symm (fun p => ‖g p‖) (L1.integrable_coeFn g).norm).symm
    _ = _ := (lp1_norm_integral _ _).symm

/-- Native CLM constructed from the actual original-time integral and proved
contraction; no desired marginal/transport certificate is supplied. -/
def timeMarginal (T : ℝ≥0) : Lp ℝ 1 (inputLaw T) →L[ℝ] Lp ℝ 1 sourceLaw :=
  (marginalLinear T).mkContinuous 1 (fun g => by
    change ‖marginalValue T g‖ ≤ 1*‖g‖
    simpa only [one_mul] using marginalValue_bound T g)

theorem timeMarginal_coe (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw T)) :
    timeMarginal T g =ᵐ[sourceLaw] (fun ω => ∫ t, g (t,ω) ∂timeLaw T) := marginalValue_coe T g

theorem timeMarginal_norm_le (T : ℝ≥0) (g : Lp ℝ 1 (inputLaw T)) : ‖timeMarginal T g‖ ≤ ‖g‖ :=
  marginalValue_bound T g

/-- Native source L1 class of the SAME actual timeEnergy process. -/
def energyClass (T s : ℝ≥0) (f : fullPredictableL2 T) : Lp ℝ 1 sourceLaw :=
  (timeEnergy_integrable T s f).toL1 (timeEnergy T f s)

theorem energyClass_coe (T s : ℝ≥0) (f : fullPredictableL2 T) :
    energyClass T s f =ᵐ[sourceLaw] timeEnergy T f s := (timeEnergy_integrable T s f).coeFn_toL1

/-- Actual energy is the actual time marginal of the actual cutoff input
SQUARED in native L1. This identity is derived by original class AE/Fubini. -/
theorem energyClass_eq_marginal_square (T s : ℝ≥0) (f : fullPredictableL2 T) :
    energyClass T s f = timeMarginal T (squareClass (inputLaw T) (truncate T s f : Lp ℝ 2 (inputLaw T))) := by
  have he : (squareClass (inputLaw T) (truncate T s f : Lp ℝ 2 (inputLaw T))) =ᵐ[inputLaw T]
      energyIntegrand T s f := by
    filter_upwards [squareClass_coe (inputLaw T) (truncate T s f : Lp ℝ 2 (inputLaw T)),
      truncate_coe T s f,representative_ae T f] with p hsq htr hf
    rw [hsq,htr]
    by_cases h : p ∈ timeSet T s <;> simp [energyIntegrand,h,hf]
  have hi : (fun ω => ∫ t, squareClass (inputLaw T) (truncate T s f : Lp ℝ 2 (inputLaw T)) (t,ω) ∂timeLaw T) =ᵐ[sourceLaw]
      timeEnergy T f s := (section_eq he).mono (fun _ h => integral_congr_ae h)
  apply Lp.ext
  exact (energyClass_coe T s f).trans
    ((timeMarginal_coe T (squareClass (inputLaw T) (truncate T s f : Lp ℝ 2 (inputLaw T)))).trans hi).symm

/-- Natural-L1 actual time-energy error is controlled by original input L2
error, uniformly in observation time. No L4/bracket-L2 field is inserted. -/
theorem energyClass_sub_norm_le (T s : ℝ≥0) (f g : fullPredictableL2 T) :
    ‖energyClass T s f-energyClass T s g‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  rw [energyClass_eq_marginal_square,energyClass_eq_marginal_square,← map_sub]
  apply (timeMarginal_norm_le T _).trans
  apply (squareClass_sub_norm_le (inputLaw T) (truncate T s f : Lp ℝ 2 (inputLaw T))
    (truncate T s g : Lp ℝ 2 (inputLaw T))).trans
  have hd : ‖(truncate T s f : Lp ℝ 2 (inputLaw T))-(truncate T s g : Lp ℝ 2 (inputLaw T))‖ ≤ ‖f-g‖ := by
    change ‖truncate T s f-truncate T s g‖ ≤ ‖f-g‖
    rw [← map_sub]
    exact truncate_norm_le T s (f-g)
  exact mul_le_mul hd (add_le_add (truncate_norm_le T s f) (truncate_norm_le T s g)) (by positivity) (norm_nonneg _)

/-- Every original full predictable L2 approximation yields ACTUAL timeEnergy
convergence in native source L1, at each observation time. -/
theorem energyClass_tendsto (T s : ℝ≥0) {f : ℕ → fullPredictableL2 T} {g : fullPredictableL2 T}
    (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => energyClass T s (f n)) atTop (𝓝 (energyClass T s g)) := by
  have hc : Tendsto (fun n => (truncate T s (f n) : Lp ℝ 2 (inputLaw T))) atTop
      (𝓝 (truncate T s g : Lp ℝ 2 (inputLaw T))) :=
    tendsto_subtype_rng.mp (((truncate T s).continuous.tendsto g).comp h)
  have hm := ((timeMarginal T).continuous.tendsto _).comp (squareClass_tendsto (inputLaw T) hc)
  simpa only [Function.comp_def,energyClass_eq_marginal_square] using hm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralEnergyL1
