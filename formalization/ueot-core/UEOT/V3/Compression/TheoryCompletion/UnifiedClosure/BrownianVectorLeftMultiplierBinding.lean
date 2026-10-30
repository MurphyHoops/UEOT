import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPastMultiplierBinding

/-!
Original commitment: state calculus needs actual START sums on SAME observed M_f, not an integral of a different recomputed state.
Existing result: same-input bounded START-window integral identity and native bounded coefficient DCT on original joint source.
Premise reduced: derive actual caller leftCoefficient input convergence and identify its integral with literal observed weighted increments.
Model/witness: bounded original joint-adapted source-AE continuous H, SAME full Euclidean f, deterministic mono0/T caller clocks with mesh→0.
Consumer: actual bounded continuous F(SAME finite state) START sums converge to SAME I(F(state)f); weighted QV/Itô remains separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorLeftMultiplierBinding
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorPredictableInputs BrownianVectorPredictableDensity
open BrownianVectorIntegralContinuousVersion BrownianVectorFiniteStateCrossQV BrownianVectorPredictableMultiplier
open BrownianVectorPastMultiplierBinding FiniteClockLeftApproximation BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Disjoint actual cells give a bound K, including repeated and empty cells. -/
theorem leftCoefficient_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hm : Monotone τ)
    (H : ℝ≥0 → Sample d → ℝ) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ u ω,‖H u ω‖≤K)
    (p : ℝ × Sample d) : ‖leftCoefficient d τ H p‖≤K := by
  rw [leftCoefficient_eq_leftSample]
  by_cases hex : ∃ i : Fin n,p.1∈Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)
  · obtain ⟨i,hi⟩ := hex
    rw [leftSample_eq_cell τ hm _ p.1 i hi]
    exact hb _ _
  · have hz : leftSample τ (fun u=>H u p.2) p.1=0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact Set.indicator_of_notMem (fun hi=>hex ⟨i,hi⟩) _
    rw [hz,norm_zero]
    exact hK

def sampledMultiplier (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hm : Monotone τ)
    (H : ℝ≥0 → Sample d → ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) :
    fullPredictableL2 d T →L[ℝ] fullPredictableL2 d T :=
  boundedMultiplier d T (leftCoefficient d τ H) (leftCoefficient_predictable d τ H hp).aestronglyMeasurable K
    (ae_of_all _ (leftCoefficient_bound d τ hm H K hK hb))

theorem sampledMultiplier_coe (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hm : Monotone τ)
    (H : ℝ≥0 → Sample d → ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f : fullPredictableL2 d T) :
    (sampledMultiplier d T τ hm H hp K hK hb f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      fun p=>leftCoefficient d τ H p • (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p :=
  boundedMultiplier_coe d T _ _ _ _ f

private theorem row_memLp (H : ℝ≥0 → Sample d → ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hb : ∀ u ω,‖H u ω‖≤K) (s : ℝ≥0) : MemLp (H s) ∞ (productLaw d) :=
  memLp_top_of_bound ((hp s).mono ((jointNaturalFiltration d).le s)).aestronglyMeasurable K
    (ae_of_all _ (hb s))

private theorem sampledMultiplier_sum (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hm : Monotone τ)
    (H : ℝ≥0 → Sample d → ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f : fullPredictableL2 d T) :
    sampledMultiplier d T τ hm H hp K hK hb f = ∑ i : Fin n,
      windowMultiplier d T (τ i.castSucc) (τ i.succ) (H (τ i.castSucc)) (hp _) (row_memLp d H hp K hb _) f := by
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  apply Lp.ext
  have hi : ∀ᵐ p ∂inputLaw d T, ∀ i : Fin n,
      (windowMultiplier d T (τ i.castSucc) (τ i.succ) (H (τ i.castSucc)) (hp _) (row_memLp d H hp K hb _) f :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p =
      scalarBlock d (τ i.castSucc) (τ i.succ) (H (τ i.castSucc)) p •
        (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p :=
    ae_all_iff.mpr (fun i=>windowMultiplier_coe d T _ _ _ _ _ f)
  filter_upwards [sampledMultiplier_coe d T τ hm H hp K hK hb f,
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
      (windowMultiplier d T (τ i.castSucc) (τ i.succ) (H (τ i.castSucc)) (hp _) (row_memLp d H hp K hb _) f :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))),hi] with p hs hsum hi
  simp only [Finset.sum_apply] at hsum
  rw [hs,hsum,Finset.sum_congr rfl (fun i _=>hi i)]
  exact Finset.sum_smul

def weightedIncrementSum (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : ℝ≥0 → Sample d → ℝ) (f : fullPredictableL2 d T) (ω : Sample d) : ℝ :=
  ∑ i : Fin n,H (τ i.castSucc) ω*
    (continuousIntegralProcess d T f (τ i.succ) ω-continuousIntegralProcess d T f (τ i.castSucc) ω)

/-- Integral returns the literal START sums on the original supplied M_f.
Only finite AE intersections and proven bounded START-window identities enter. -/
theorem sampledMultiplier_integral_coe (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hm : Monotone τ)
    (H : ℝ≥0 → Sample d → ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f : fullPredictableL2 d T) :
    (predictableIntegral d T (sampledMultiplier d T τ hm H hp K hK hb f) : Sample d → ℝ) =ᵐ[productLaw d]
      weightedIncrementSum d T τ H f := by
  rw [sampledMultiplier_sum,map_sum]
  have hi : ∀ᵐ ω ∂productLaw d,∀ i : Fin n,
      (predictableIntegral d T (windowMultiplier d T (τ i.castSucc) (τ i.succ) (H (τ i.castSucc))
        (hp _) (row_memLp d H hp K hb _) f) : Sample d→ℝ) ω =
      H (τ i.castSucc) ω*(continuousIntegralProcess d T f (τ i.succ) ω-continuousIntegralProcess d T f (τ i.castSucc) ω) :=
    ae_all_iff.mpr (fun i=>windowMultiplier_integral_coe d T _ _ (hm (by exact_mod_cast Nat.le_succ (i : ℕ))) _ _ _ f)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
    predictableIntegral d T (windowMultiplier d T (τ i.castSucc) (τ i.succ) (H (τ i.castSucc))
      (hp _) (row_memLp d H hp K hb _) f)),hi] with ω hs hi
  simp only [Finset.sum_apply] at hs
  exact hs.trans (Finset.sum_congr rfl (fun i _=>hi i))

variable (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
  (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
  (hmesh : Tendsto (fun n=>(mesh (τ n) : ℝ)) atTop (𝓝 0))
include hm h0 hT hmesh

theorem leftCoefficient_tendsto_ae (H : ℝ≥0→Sample d→ℝ)
    (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω)) :
    ∀ᵐ p ∂inputLaw d T,Tendsto (fun n=>leftCoefficient d (τ n) H p) atTop
      (𝓝 (H (Real.toNNReal p.1) p.2)) := by
  have hcp : ∀ᵐ p ∂inputLaw d T,Continuous (fun u=>H u p.2) := Measure.quasiMeasurePreserving_snd.ae hc
  filter_upwards [time_support_ae d T,hcp] with p ht hc
  exact leftSample_tendsto T N τ hm h0 hT hmesh (fun u=>H u p.2) p.1 ht.1 ht.2 hc.continuousWithinAt

/-- SAME supplied f and SAME original source readout H, without recomputing
H from an approximate state or conditioning on a selected clock. -/
theorem sampledMultiplier_tendsto (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω))
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f : fullPredictableL2 d T) :
    Tendsto (fun n=>sampledMultiplier d T (τ n) (hm n) H hp K hK hb f) atTop
      (𝓝 (continuousMultiplier d T H hj hp hc K hb f)) := by
  apply boundedMultiplier_tendsto d T (fun n=>leftCoefficient d (τ n) H)
    (fun p=>H (Real.toNNReal p.1) p.2)
    (fun n=>(leftCoefficient_predictable d (τ n) H hp).aestronglyMeasurable)
    (continuousReadout_predictable d T H hp hc) K hK
    (fun n=>ae_of_all _ (leftCoefficient_bound d (τ n) (hm n) H K hK hb))
    (ae_of_all _ (fun _=>hb _ _))
    (leftCoefficient_tendsto_ae d T N τ hm h0 hT hmesh H hc) f

theorem sampledIntegral_tendsto (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω))
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f : fullPredictableL2 d T) :
    Tendsto (fun n=>predictableIntegral d T (sampledMultiplier d T (τ n) (hm n) H hp K hK hb f)) atTop
      (𝓝 (predictableIntegral d T (continuousMultiplier d T H hj hp hc K hb f))) :=
  ((predictableIntegral d T).continuous.tendsto _).comp
    (sampledMultiplier_tendsto d T N τ hm h0 hT hmesh H hj hp hc K hK hb f)

/-- Actual observed START sums converge to the SAME original actual integral
of H*f. This is not an asserted output field or state Itô formula. -/
theorem weightedIncrementSum_tendstoInMeasure (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω))
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f : fullPredictableL2 d T) :
    TendstoInMeasure (productLaw d) (fun n=>weightedIncrementSum d T (τ n) H f) atTop
      (continuousIntegralProcess d T (continuousMultiplier d T H hj hp hc K hb f) T) :=
  TendstoInMeasure.congr (fun n=>sampledMultiplier_integral_coe d T (τ n) (hm n) H hp K hK hb f)
    (continuousIntegralProcess_horizon d T _).symm
    (tendstoInMeasure_of_tendsto_Lp (sampledIntegral_tendsto d T N τ hm h0 hT hmesh H hj hp hc K hK hb f))

/-- Actual bounded continuous F of the SAME finite state at every caller
START is consumed by the SAME original product-source integral. -/
theorem functionOfState_startSums_tendstoInMeasure {m : ℕ}
    (family : Fin m→fullPredictableL2 d T) (F : EuclideanSpace ℝ (Fin m)→ℝ) (hF : Continuous F)
    (K : ℝ) (hb : ∀ x,‖F x‖≤K) (f : fullPredictableL2 d T) :
    TendstoInMeasure (productLaw d)
      (fun n=>weightedIncrementSum d T (τ n) (fun u ω=>F (stateProcess d T family u ω)) f) atTop
      (continuousIntegralProcess d T (functionOfStateInput d T family F hF K hb f) T) :=
  weightedIncrementSum_tendstoInMeasure d T N τ hm h0 hT hmesh (fun u ω=>F (stateProcess d T family u ω))
    (hF.measurable.comp (stateProcess_measurable d T family))
    (fun u=>hF.comp_stronglyMeasurable (stateProcess_stronglyAdapted d T family u))
    ((stateProcess_continuous d T family).mono (fun _ h=>hF.comp h))
    K ((norm_nonneg (F 0)).trans (hb 0)) (fun _ _=>hb _) f

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorLeftMultiplierBinding
