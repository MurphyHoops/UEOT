import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSampledCellIncrement
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVaryingInputQV

/-!
Original commitment: actual scalar Ito needs actual START-weighted QV converging to SAME-source dt H*f squared.
Existing result: actual sampled-input cell identity/cross table binding, original sampled product L2 limit and actual varying-input cross QV.
Premise reduced: derive original weighted square table limit and bind its target to actual original time integral H*f squared.
Model/witness: SAME original fullPredictableL2 T/sourceLaw/naturalFiltration, actual bounded continuous-adapted H and caller computed mesh→0.
Consumer: actual second-order scalar Ito Riemann term; C2 Taylor/remainder and original general source obligations remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralWeightedQV
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralContinuousVersion BrownianIntegralTimeEnergy BrownianIntegralEnergyL1
open BrownianIntegralCrossVariation BrownianVaryingInputQV BrownianSampledCellIncrement
open BrownianContinuousAdaptedInputs BrownianPredictableMultiplier BrownianLeftMultiplierInputs BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual same-time/source integrand, not a desired weighted QV field. -/
def weightedTimeIntegrand (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (f : fullPredictableL2 T)
    (p : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  H (Real.toNNReal p.1) p.2*(representative T f p)^2

theorem weightedTimeIntegrand_integrable (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (K : ℝ) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    Integrable (weightedTimeIntegrand T H f) (inputLaw T) :=
  (memLp_top_of_bound (inputFunction_measurable H hjoint).aestronglyMeasurable K
    (Eventually.of_forall (fun p => hb (Real.toNNReal p.1) p.2))).integrable_mul
      (memLp_one_iff_integrable.mpr (representative_memLp_two T f).integrable_sq)

/-- Literal original timeLaw T integral of actual H times original f squared. -/
def weightedTimeEnergy (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∫ t, weightedTimeIntegrand T H f (t,ω) ∂timeLaw T

def weightedEnergyClass (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (K : ℝ) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    Lp ℝ 1 sourceLaw :=
  ((weightedTimeIntegrand_integrable T H hjoint K hb f).integral_prod_right).toL1 (weightedTimeEnergy T H f)

theorem weightedEnergyClass_coe (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (K : ℝ) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    weightedEnergyClass T H hjoint K hb f =ᵐ[sourceLaw] weightedTimeEnergy T H f :=
  ((weightedTimeIntegrand_integrable T H hjoint K hb f).integral_prod_right).coeFn_toL1

/-- Native actual cross-energy target of f and actual H*f equals actual
original dt integral H*f squared. The target identity is proved by actual
input multiplication and original Fubini, not supplied as a certificate. -/
theorem crossEnergyClass_multiplied_eq_weighted (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    crossEnergyClass T T f (continuousMultiplier T H hjoint hadapt hcont K hK hb f) =
      weightedEnergyClass T H hjoint K hb f := by
  let g := continuousMultiplier T H hjoint hadapt hcont K hK hb f
  have hp : productClass (inputLaw T) (f : Lp ℝ 2 (inputLaw T)) (g : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      weightedTimeIntegrand T H f := by
    filter_upwards [productClass_coe (inputLaw T) (f : Lp ℝ 2 (inputLaw T)) (g : Lp ℝ 2 (inputLaw T)),
      continuousMultiplier_coe T H hjoint hadapt hcont K hK hb f,representative_ae T f] with p hp hg hf
    rw [hp]
    change (f : Lp ℝ 2 (inputLaw T)) p*
      (continuousMultiplier T H hjoint hadapt hcont K hK hb f : Lp ℝ 2 (inputLaw T)) p = _
    rw [hg,hf]
    unfold weightedTimeIntegrand
    ring
  have hsec : ∀ᵐ ω ∂sourceLaw, (fun t => productClass (inputLaw T) (f : Lp ℝ 2 (inputLaw T))
      (g : Lp ℝ 2 (inputLaw T)) (t,ω)) =ᵐ[timeLaw T] fun t => weightedTimeIntegrand T H f (t,ω) :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw T)).quasiMeasurePreserving.ae hp)
  apply Lp.ext
  unfold crossEnergyClass
  rw [truncate_horizon,truncate_horizon]
  filter_upwards [timeMarginal_coe T (productClass (inputLaw T) (f : Lp ℝ 2 (inputLaw T)) (g : Lp ℝ 2 (inputLaw T))),
    weightedEnergyClass_coe T H hjoint K hb f,hsec] with ω hm hw hs
  exact hm.trans ((integral_congr_ae hs).trans hw.symm)

/-- Actual varying sampled-input cross table converges in original source
L1 to actual original dt weighted energy; no L4 or weighted-limit premise. -/
theorem weighted_QV_class_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hjoint : Measurable (Function.uncurry H))
    (hadapt : StronglyAdapted naturalFiltration H) (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    Tendsto (fun m => gridCross T (τ m) f
      (sampledMultiplier T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hK hb f)) atTop
      (𝓝 (weightedEnergyClass T H hjoint K hb f)) := by
  rw [← crossEnergyClass_multiplied_eq_weighted T H hjoint hadapt hcont K hK hb f]
  exact partition_crossVariation_of_input_tendsto T N τ hmono hzero hend hmesh f _ _
    (sampledMultiplier_tendsto T N τ hmono hzero hend hmesh H hjoint hadapt hcont K hK hb f)

/-- EXACT original START-weighted actual square increment tables converge
in source measure to SAME original actual dt integral H*f squared. -/
theorem weighted_QV_tendstoInMeasure (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hjoint : Measurable (Function.uncurry H))
    (hadapt : StronglyAdapted naturalFiltration H) (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    TendstoInMeasure sourceLaw (fun m => weightedSquareSum T (τ m) H f) atTop (weightedTimeEnergy T H f) :=
  TendstoInMeasure.congr (fun m => gridCross_sampled_coe T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hK hb f)
    (weightedEnergyClass_coe T H hjoint K hb f) (tendstoInMeasure_of_tendsto_Lp
      (weighted_QV_class_tendsto T N τ hmono hzero hend hmesh H hjoint hadapt hcont K hK hb f))

/-- Actual nonlinear second-order Ito consumer for any bounded continuous
F(SAME M); use F=phi'' only after proving the actual Taylor remainder step. -/
theorem functionOfIntegral_weighted_QV_tendstoInMeasure (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (f : fullPredictableL2 T) (F : ℝ → ℝ) (hF : Continuous F) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, ‖F x‖ ≤ K) :
    TendstoInMeasure sourceLaw (fun m => weightedSquareSum T (τ m)
      (fun u ω => F (continuousIntegralProcess T f u ω)) f) atTop
      (weightedTimeEnergy T (fun u ω => F (continuousIntegralProcess T f u ω)) f) :=
  weighted_QV_tendstoInMeasure T N τ hmono hzero hend hmesh
    (fun u ω => F (continuousIntegralProcess T f u ω))
    (hF.measurable.comp (continuousIntegralProcess_measurable T f))
    (fun u => hF.comp_stronglyMeasurable (continuousIntegralProcess_stronglyAdapted T f u))
    ((continuousIntegralProcess_continuous T f).mono (fun _ h => hF.comp h)) K hK (fun _ _ => hb _) f

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralWeightedQV
