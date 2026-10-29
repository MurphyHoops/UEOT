import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousAdaptedInputs
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCompensator

/-!
Original commitment: Ito's first derivative must multiply the ORIGINAL integrand and be consumed by the actual source integral.
Existing result: native Holder multiplication and original full predictable integration/continuous source version.
Premise reduced: construct bounded predictable multipliers on SAME original full L2 class and actual I(H*f), deriving permissions for continuous adapted H.
Model/witness: SAME inputLaw T/sourceLaw/naturalFiltration, bounded H at original time, no extra future observation or desired integral source field.
Consumer: original left-weighted integral-increment/Ito bridge; this unit alone does not identify stochastic Riemann sums or prove Ito.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableMultiplier
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs
open BrownianPredictableDensity BrownianIntegralTimeTruncation BrownianIntegralContinuousVersion
open BrownianIntegralTimeEnergy BrownianIntegralCompensator BrownianContinuousAdaptedInputs
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual native Holder multiplication of an actual original bounded
coefficient class by the original integrand class. -/
def ambientMultiplier (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ) (hH : MemLp H ∞ (inputLaw T)) :
    fullPredictableL2 T →L[ℝ] Lp ℝ 2 (inputLaw T) :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL (inputLaw T) ∞ 2 2 (hH.toLp H)).comp (fullPredictableL2 T).subtypeL

theorem ambientMultiplier_coe (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ) (hH : MemLp H ∞ (inputLaw T))
    (f : fullPredictableL2 T) : ambientMultiplier T H hH f =ᵐ[inputLaw T]
      fun p => H p*(f : Lp ℝ 2 (inputLaw T)) p := by
  have hh := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hH.toLp H) (f : Lp ℝ 2 (inputLaw T))
  filter_upwards [hh,hH.coeFn_toLp] with p hh hH
  simp only [ContinuousLinearMap.mul_apply'] at hh
  exact hh.trans (congrArg (fun x : ℝ => x*(f : Lp ℝ 2 (inputLaw T)) p) hH)

theorem ambientMultiplier_predictable (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ)
    (hH : MemLp H ∞ (inputLaw T)) (hpred : AEStronglyMeasurable[predictableSigma] H (inputLaw T))
    (f : fullPredictableL2 T) : ambientMultiplier T H hH f ∈ fullPredictableL2 T := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact (hpred.mul (mem_lpMeas_iff_aestronglyMeasurable.mp f.property)).congr
    (ambientMultiplier_coe T H hH f).symm

/-- Native continuous linear multiplier on the ACTUAL full predictable L2
subspace. Range membership is proved, not stored as a caller's field. -/
def inputMultiplier (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ) (hH : MemLp H ∞ (inputLaw T))
    (hpred : AEStronglyMeasurable[predictableSigma] H (inputLaw T)) :
    fullPredictableL2 T →L[ℝ] fullPredictableL2 T :=
  (ambientMultiplier T H hH).codRestrict (fullPredictableL2 T) (ambientMultiplier_predictable T H hH hpred)

theorem inputMultiplier_coe (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ) (hH : MemLp H ∞ (inputLaw T))
    (hpred : AEStronglyMeasurable[predictableSigma] H (inputLaw T)) (f : fullPredictableL2 T) :
    (inputMultiplier T H hH hpred f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      fun p => H p*(f : Lp ℝ 2 (inputLaw T)) p := ambientMultiplier_coe T H hH f

theorem inputMultiplier_norm_le (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ) (hH : MemLp H ∞ (inputLaw T))
    (hpred : AEStronglyMeasurable[predictableSigma] H (inputLaw T)) (f : fullPredictableL2 T) :
    ‖inputMultiplier T H hH hpred f‖ ≤ ‖hH.toLp H‖*‖f‖ := by
  have hh := (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le (r := 2)
    (hH.toLp H) (f : Lp ℝ 2 (inputLaw T))
  change ‖(ContinuousLinearMap.mul ℝ ℝ).holderL (inputLaw T) ∞ 2 2 (hH.toLp H)
    (f : Lp ℝ 2 (inputLaw T))‖ ≤ _
  exact hh.trans (calc
    _ ≤ 1*‖hH.toLp H‖*‖(f : Lp ℝ 2 (inputLaw T))‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = _ := by simp only [one_mul]; rfl)

/-- Coefficient integrability and original predictable permissions are both
DERIVED for actual bounded continuous adapted source H. -/
def continuousMultiplier (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    fullPredictableL2 T →L[ℝ] fullPredictableL2 T :=
  inputMultiplier T (inputFunction H)
    (memLp_top_of_bound (inputFunction_measurable H hjoint).aestronglyMeasurable K
      (Eventually.of_forall (fun p => hbound (Real.toNNReal p.1) p.2)))
    (inputFunction_predictable T H hjoint hadapt hcont K hK hbound)

theorem continuousMultiplier_coe (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    (continuousMultiplier T H hjoint hadapt hcont K hK hbound f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      fun p => H (Real.toNNReal p.1) p.2*(f : Lp ℝ 2 (inputLaw T)) p :=
  inputMultiplier_coe T (inputFunction H) _ _ f

/-- Actual existing continuous integral consumes the actual SAME H*f class. -/
theorem multipliedIntegral_martingale (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ)
    (hH : MemLp H ∞ (inputLaw T)) (hpred : AEStronglyMeasurable[predictableSigma] H (inputLaw T))
    (f : fullPredictableL2 T) :
    Martingale (continuousIntegralProcess T (inputMultiplier T H hH hpred f)) naturalFiltration sourceLaw :=
  continuousIntegralProcess_martingale T _

theorem multipliedIntegral_compensator (T : ℝ≥0) (H : ℝ × (ℝ≥0 → ℝ) → ℝ)
    (hH : MemLp H ∞ (inputLaw T)) (hpred : AEStronglyMeasurable[predictableSigma] H (inputLaw T))
    (f : fullPredictableL2 T) :
    Martingale (compensatedIntegral T (inputMultiplier T H hH hpred f)) naturalFiltration sourceLaw :=
  compensatedIntegral_martingale T _

/-- Actual bounded continuous function of the SAME continuous integral,
multiplied by its SAME original integrand. For Ito use F = derivative phi;
no derivative/chain rule is assumed by this construction. -/
def functionOfIntegralInput (T : ℝ≥0) (f : fullPredictableL2 T) (F : ℝ → ℝ)
    (hF : Continuous F) (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ x, ‖F x‖ ≤ K) : fullPredictableL2 T :=
  continuousMultiplier T (fun u ω => F (continuousIntegralProcess T f u ω))
    (hF.measurable.comp (continuousIntegralProcess_measurable T f))
    (fun u => hF.comp_stronglyMeasurable (continuousIntegralProcess_stronglyAdapted T f u))
    ((continuousIntegralProcess_continuous T f).mono (fun _ h => hF.comp h))
    K hK (fun _ _ => hbound _) f

theorem functionOfIntegralInput_coe (T : ℝ≥0) (f : fullPredictableL2 T) (F : ℝ → ℝ)
    (hF : Continuous F) (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ x, ‖F x‖ ≤ K) :
    (functionOfIntegralInput T f F hF K hK hbound : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      fun p => F (continuousIntegralProcess T f (Real.toNNReal p.1) p.2)*
        (f : Lp ℝ 2 (inputLaw T)) p :=
  continuousMultiplier_coe T _ _ _ _ K hK (fun _ _ => hbound _) f

theorem functionOfIntegralInput_martingale (T : ℝ≥0) (f : fullPredictableL2 T) (F : ℝ → ℝ)
    (hF : Continuous F) (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ x, ‖F x‖ ≤ K) :
    Martingale (continuousIntegralProcess T (functionOfIntegralInput T f F hF K hK hbound))
      naturalFiltration sourceLaw := continuousIntegralProcess_martingale T _

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableMultiplier
