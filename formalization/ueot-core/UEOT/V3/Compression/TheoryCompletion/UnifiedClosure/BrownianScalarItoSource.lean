import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTaylorLimit

/-!
Original commitment: actual scalar Ito must be a SAME-source identity, not a desired stochastic source field.
Existing result: SAME actual first/second weighted increment limits and actual C2 finite remainder sum→0.
Premise reduced: derive actual terminal C2 Ito identity from literal finite telescope and native AE subsequences.
Model/witness: SAME original fullPredictableL2 T/sourceLaw/naturalFiltration/continuous M; explicit globally bounded first/second derivatives, no L4/third derivative.
Consumer: actual nonzero-noise shifted Brownian Dynkin source; arbitrary C2 localization/drift/filtered/vector/Girsanov remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianScalarItoSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianPredictableInputs BrownianIntegralContinuousVersion
open BrownianQuadraticVariation BrownianPredictableMultiplier BrownianWeightedIncrementBinding
open BrownianSampledCellIncrement BrownianIntegralWeightedQV BrownianIntegralTaylorLimit BrownianScalarTaylorRemainder
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Literal finite Taylor identity, valid before any stochastic limit. -/
theorem finite_taylor_telescope (φ : ℝ → ℝ) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (X : ℝ≥0 → ℝ) :
    φ (X (τ (Fin.last n)))-φ (X (τ 0)) =
      (∑ i : Fin n, deriv φ (X (τ i.castSucc))*(X (τ i.succ)-X (τ i.castSucc)))+
      (1/2 : ℝ)*(∑ i : Fin n, iteratedDeriv 2 φ (X (τ i.castSucc))*(X (τ i.succ)-X (τ i.castSucc))^2)+
      remainderSum φ τ X := by
  have h0 := Fin.sum_univ_succ (fun j : Fin (n+1) => φ (X (τ j)))
  have hN := Fin.sum_univ_castSucc (fun j : Fin (n+1) => φ (X (τ j)))
  have htel : (∑ i : Fin n, (φ (X (τ i.succ))-φ (X (τ i.castSucc)))) =
      φ (X (τ (Fin.last n)))-φ (X (τ 0)) := by
    rw [Finset.sum_sub_distrib]
    linarith
  symm
  unfold remainderSum
  rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin n, (φ (X (τ i.succ))-φ (X (τ i.castSucc))) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold secondRemainder
      ring
    _ = _ := htel

/-- ACTUAL first-order input generated from the original derivative and
SAME original continuous integral, consumed by original predictableIntegral. -/
def itoInput (T : ℝ≥0) (f : fullPredictableL2 T) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, ‖deriv φ x‖ ≤ K) : fullPredictableL2 T :=
  functionOfIntegralInput T f (deriv φ) (hφ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) K hK hb

/-- ACTUAL original time integral of second derivative times SAME f squared. -/
def itoSecondEnergy (T : ℝ≥0) (f : fullPredictableL2 T) (φ : ℝ → ℝ) : (ℝ≥0 → ℝ) → ℝ :=
  weightedTimeEnergy T (fun u ω => iteratedDeriv 2 φ (continuousIntegralProcess T f u ω)) f

/-- Real scalar C2 Ito on the actual original source and actual returned
integral input, with explicit bounded derivative regularity. No source/Ito,
compensator, remainder or chosen alternative stochastic output is assumed. -/
theorem actual_scalar_ito (T : ℝ≥0) (f : fullPredictableL2 T) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hb₁ : ∀ x, ‖deriv φ x‖ ≤ K₁) (hb₂ : ∀ x, ‖iteratedDeriv 2 φ x‖ ≤ K₂) :
    (fun ω => φ (continuousIntegralProcess T f T ω)) =ᵐ[sourceLaw] fun ω =>
      φ 0+continuousIntegralProcess T (itoInput T f φ hφ K₁ hK₁ hb₁) T ω+(1/2 : ℝ)*itoSecondEnergy T f φ ω := by
  have hfirst := functionOfIntegral_weightedIncrement_tendstoInMeasure T (fun n => n+1) (uniformClock T)
    (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
    f (deriv φ) (hφ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) K₁ hK₁ hb₁
  have hsecond := functionOfIntegral_weighted_QV_tendstoInMeasure T (fun n => n+1) (uniformClock T)
    (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
    f (iteratedDeriv 2 φ) (hφ.continuous_iteratedDeriv' 2) K₂ hK₂ hb₂
  have hrem := actual_remainderSum_tendstoInMeasure φ hφ T (fun n => n+1) (uniformClock T)
    (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) f
  obtain ⟨ns,hns,hFa⟩ := hfirst.exists_seq_tendsto_ae
  obtain ⟨ms,hms,hSa⟩ := (hsecond.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks,hks,hRa⟩ := (hrem.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hFa,hSa,hRa,continuousIntegralProcess_zero T f] with ω hf hs hr hz
  have hf' := hf.comp (hms.tendsto_atTop.comp hks.tendsto_atTop)
  have hs' := hs.comp hks.tendsto_atTop
  have htotal := (hf'.add (hs'.const_mul (1/2 : ℝ))).add hr
  have he (i : ℕ) :
      (weightedIncrementSum T (uniformClock T (ns (ms (ks i))))
        (fun u ω => deriv φ (continuousIntegralProcess T f u ω)) f ω+
      (1/2 : ℝ)*weightedSquareSum T (uniformClock T (ns (ms (ks i))))
        (fun u ω => iteratedDeriv 2 φ (continuousIntegralProcess T f u ω)) f ω)+
      remainderSum φ (uniformClock T (ns (ms (ks i)))) (fun u => continuousIntegralProcess T f u ω) =
      φ (continuousIntegralProcess T f T ω)-φ 0 := by
    have ht := finite_taylor_telescope φ (uniformClock T (ns (ms (ks i))))
      (fun u => continuousIntegralProcess T f u ω)
    rw [uniformClock_end,uniformClock_zero,hz] at ht
    exact ht.symm
  have hsame := (tendsto_congr' (Eventually.of_forall he)).mp htotal
  have hid := tendsto_nhds_unique hsame (tendsto_const_nhds (x := φ (continuousIntegralProcess T f T ω)-φ 0))
  change ((continuousIntegralProcess T (itoInput T f φ hφ K₁ hK₁ hb₁) T ω+
    (1/2 : ℝ)*itoSecondEnergy T f φ ω)+0) = _ at hid
  linarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianScalarItoSource
