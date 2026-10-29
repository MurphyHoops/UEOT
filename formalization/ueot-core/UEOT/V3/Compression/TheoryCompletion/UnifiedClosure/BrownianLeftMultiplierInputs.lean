import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedMultiplierLimit
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPartitionLeftInputs

/-!
Original commitment: Ito requires actual START-sampled coefficients multiplying SAME original input, not a supplied coefficient-limit certificate.
Existing result: actual caller-clock sampleRecord, original predictable input permissions and bounded multiplier dominated convergence.
Premise reduced: derive original left-sampled coefficient bounds/predictability/convergence and actual product-input/integral L2 limits.
Model/witness: SAME T/sourceLaw/inputLaw/naturalFiltration, actual bounded joint measurable adapted AE-continuous H, arbitrary caller mesh→0.
Consumer: next actual sum H_start*(M_end-M_start) binding; this unit does not yet identify that weighted increment sum or prove Ito.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLeftMultiplierInputs
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianContinuousAdaptedInputs BrownianPartitionLeftInputs
open BrownianPredictableMultiplier BrownianBoundedMultiplierLimit BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual original record readout on the original time/product source. -/
def recordCoefficient {T : ℝ≥0} (r : ElementaryInput T) : ℝ × (ℝ≥0 → ℝ) → ℝ :=
  integrand r.clock r.coefficient

theorem recordCoefficient_predictable {T : ℝ≥0} (r : ElementaryInput T) :
    AEStronglyMeasurable[predictableSigma] (recordCoefficient r) (inputLaw T) :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp (literalPredictableInput r).property).congr
    (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp

/-- Literal disjoint monotone clock cells give the actual row, even with
repeated clocks; no extension outside the active intervals is introduced. -/
theorem integrand_eq_active {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) (i : Fin n)
    (hi : p.1 ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) : integrand τ H p = H i p.2 := by
  rw [integrand,Finset.sum_eq_single i]
  · simp only [intervalIntegrand,Set.indicator_of_mem hi,one_mul]
  · intro j _ hji
    have hj : p.1 ∉ Ioc (τ j.castSucc : ℝ) (τ j.succ : ℝ) := by
      intro hj
      rcases lt_or_gt_of_ne hji with h | h
      · have hc : (τ j.succ : ℝ) ≤ (τ i.castSucc : ℝ) := by
          exact_mod_cast hτ (show j.succ ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hj.2.trans hc)) hi.1
      · have hc : (τ i.succ : ℝ) ≤ (τ j.castSucc : ℝ) := by
          exact_mod_cast hτ (show i.succ ≤ j.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hi.2.trans hc)) hj.1
    simp only [intervalIntegrand,Set.indicator_of_notMem hj,zero_mul]
  · simp

theorem recordCoefficient_bound {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ i ω, ‖r.coefficient i ω‖ ≤ K) : ∀ p, ‖recordCoefficient r p‖ ≤ K := by
  intro p
  by_cases hex : ∃ i : Fin r.n, p.1 ∈ Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)
  · obtain ⟨i,hi⟩ := hex
    change ‖integrand r.clock r.coefficient p‖ ≤ K
    rw [integrand_eq_active r.clock r.clock_mono r.coefficient p i hi]
    exact hb i p.2
  · have hz : recordCoefficient r p = 0 := by
      unfold recordCoefficient integrand
      apply Finset.sum_eq_zero
      intro i _
      have hi : p.1 ∉ Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ) := fun hi => hex ⟨i,hi⟩
      simp only [intervalIntegrand,Set.indicator_of_notMem hi,zero_mul]
    rw [hz,norm_zero]
    exact hK

/-- Actual caller START sampler followed by original native product input. -/
def sampledMultiplier (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0=0) (hend : τ (Fin.last n)=T)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hadapt : StronglyAdapted naturalFiltration H)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ u ω, ‖H u ω‖ ≤ K) :
    fullPredictableL2 T →L[ℝ] fullPredictableL2 T :=
  let r := sampleRecord T τ hmono hzero hend H hadapt K hb
  boundedMultiplier T (recordCoefficient r) (recordCoefficient_predictable r) K
    (Eventually.of_forall (recordCoefficient_bound r K hK (fun i ω => hb (τ i.castSucc) ω)))

/-- Concrete left coefficient limit is derived from actual caller clock
cells and actual source path continuity, then multiplied by ORIGINAL f. -/
theorem sampledMultiplier_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hjoint : Measurable (Function.uncurry H))
    (hadapt : StronglyAdapted naturalFiltration H) (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    Tendsto (fun m => sampledMultiplier T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hK hb f)
      atTop (𝓝 (continuousMultiplier T H hjoint hadapt hcont K hK hb f)) := by
  let r (m : ℕ) := sampleRecord T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hb
  exact boundedMultiplier_tendsto T (fun m => recordCoefficient (r m)) (inputFunction H)
    (fun m => recordCoefficient_predictable (r m))
    (inputFunction_predictable T H hjoint hadapt hcont K hK hb) K hK
    (fun m => Eventually.of_forall (recordCoefficient_bound (r m) K hK (fun i ω => hb (τ m i.castSucc) ω)))
    (Eventually.of_forall (fun p => hb (Real.toNNReal p.1) p.2))
    (partition_integrands_tendsto_ae T N τ hmono hzero hend hmesh H hadapt
      (hcont.mono (fun _ h u => (h.continuousAt).continuousWithinAt)) K hb) f

theorem sampledMultipliedIntegral_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hjoint : Measurable (Function.uncurry H))
    (hadapt : StronglyAdapted naturalFiltration H) (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    Tendsto (fun m => predictableIntegral T
      (sampledMultiplier T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hK hb f)) atTop
      (𝓝 (predictableIntegral T (continuousMultiplier T H hjoint hadapt hcont K hK hb f))) :=
  ((predictableIntegral T).continuous.tendsto _).comp
    (sampledMultiplier_tendsto T N τ hmono hzero hend hmesh H hjoint hadapt hcont K hK hb f)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLeftMultiplierInputs
