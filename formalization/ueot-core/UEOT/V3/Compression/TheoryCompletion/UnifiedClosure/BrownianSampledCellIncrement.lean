import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianWeightedIncrementBinding
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCrossVariation

/-!
Original commitment: weighted QV must use actual H_start*(Delta SAME M)^2, not a renamed cross-variation field.
Existing result: actual original sampled product input, source cell disjointness and bounded Fs window output identity.
Premise reduced: prove actual sampled-input integral cell increments equal H_start*Delta SAME M, then bind actual weighted square table.
Model/witness: SAME original T/f/sourceLaw/naturalFiltration/caller monotone 0/T clocks; no L4 or new observation.
Consumer: weighted QV from actual cross variation and actual sampled input L2 convergence; no weighted-limit/Ito hypothesis assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSampledCellIncrement
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralPastLocalization BrownianIntegralContinuousVersion
open BrownianPartitionLeftInputs BrownianLeftMultiplierInputs BrownianBoundedMultiplierLimit BrownianBoundedPastMultiplier
open BrownianIntegralCrossVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem cell_le {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hmono (by exact_mod_cast Nat.le_succ (i : ℕ))
private theorem cell_end {T : ℝ≥0} {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hend : τ (Fin.last n)=T) (i : Fin n) : τ i.succ ≤ T :=
  (hmono (Fin.le_last i.succ)).trans hend.le

/-- Actual cell localization of the original sampled product input is the
original bounded START coefficient on that cell, with no changed permission. -/
theorem localize_sampled_cell (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0=0) (hend : τ (Fin.last n)=T) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ u ω, ‖H u ω‖ ≤ K) (i : Fin n) (f : fullPredictableL2 T) :
    localize T (τ i.castSucc) (τ i.succ) univ MeasurableSet.univ
      (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f) =
      windowMultiplier T (τ i.castSucc) (τ i.succ) (cell_le τ hmono i) (cell_end τ hmono hend i)
        (H (τ i.castSucc)) (hadapt _) K hK (hb _) f := by
  apply Subtype.ext
  apply Lp.ext
  let r := sampleRecord T τ hmono hzero hend H hadapt K hb
  have hs := boundedMultiplier_coe T (recordCoefficient r) (recordCoefficient_predictable r) K
    (Eventually.of_forall (recordCoefficient_bound r K hK (fun j ω => hb (τ j.castSucc) ω))) f
  filter_upwards [localize_coe T (τ i.castSucc) (τ i.succ) univ MeasurableSet.univ
    (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f),hs,
    windowMultiplier_coe T _ _ (cell_le τ hmono i) (cell_end τ hmono hend i)
      (H (τ i.castSucc)) (hadapt _) K hK (hb _) f] with p hl hs hw
  change (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f : Lp ℝ 2 (inputLaw T)) p = _ at hs
  rw [hl,hw]
  have he : p ∈ eventWindow T (τ i.castSucc) (τ i.succ) univ ↔
      p.1 ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) := by
    simp only [eventWindow,min_eq_left (cell_end τ hmono hend i),mem_prod,mem_univ,and_true]
  by_cases h : p.1 ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)
  · rw [Set.indicator_of_mem (he.mpr h),hs]
    change integrand τ (fun j => H (τ j.castSucc)) p*(f : Lp ℝ 2 (inputLaw T)) p = _
    rw [integrand_eq_active τ hmono _ p i h]
    simp only [intervalIntegrand,Set.indicator_of_mem h,one_mul]
  · rw [Set.indicator_of_notMem (fun hp => h (he.mp hp))]
    simp only [intervalIntegrand,Set.indicator_of_notMem h,zero_mul]

/-- Actual continuous integral increments of the SAME sampled product input
are EXACTLY the original START coefficient times SAME original M increments. -/
theorem sampled_cell_increment (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0=0) (hend : τ (Fin.last n)=T) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ u ω, ‖H u ω‖ ≤ K) (i : Fin n) (f : fullPredictableL2 T) :
    (fun ω => continuousIntegralProcess T (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f) (τ i.succ) ω-
      continuousIntegralProcess T (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f) (τ i.castSucc) ω) =ᵐ[sourceLaw]
      fun ω => H (τ i.castSucc) ω*(continuousIntegralProcess T f (τ i.succ) ω-continuousIntegralProcess T f (τ i.castSucc) ω) := by
  have hl := predictableIntegral_localize_coe T (τ i.castSucc) (τ i.succ) (cell_le τ hmono i)
    univ MeasurableSet.univ (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f)
  rw [localize_sampled_cell T τ hmono hzero hend H hadapt K hK hb i f] at hl
  have hr := windowMultiplier_integral_coe T _ _ (cell_le τ hmono i) (cell_end τ hmono hend i)
    (H (τ i.castSucc)) (hadapt _) K hK (hb _) f
  simp only [Set.indicator_univ] at hl
  exact hl.symm.trans hr

/-- Actual original weighted square-increment table. -/
def weightedSquareSum (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin n, H (τ i.castSucc) ω*
    (continuousIntegralProcess T f (τ i.succ) ω-continuousIntegralProcess T f (τ i.castSucc) ω)^2

/-- The native actual cross sum is bound to the EXACT original weighted
square table, via actual sampled-input cell increments; no QV identity input. -/
theorem gridCross_sampled_coe (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0=0) (hend : τ (Fin.last n)=T) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    gridCross T τ f (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f) =ᵐ[sourceLaw]
      weightedSquareSum T τ H f := by
  have hi := ae_all_iff.mpr (fun i : Fin n => sampled_cell_increment T τ hmono hzero hend H hadapt K hK hb i f)
  filter_upwards [gridCross_coe T τ f (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f),hi]
    with ω hs hi
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  ring

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSampledCellIncrement
