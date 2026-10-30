import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftSource

/-!
Original commitment: the actual state Ito drift term must use the actual supplied drift on the same state and source.
Existing result: a bounded original joint-predictable beta has the literal dt primitive and actual finite-variation increments.
Premise reduced: derive convergence of actual START-weighted primitive increments to the actual weighted Lebesgue integral.
Model/witness: arbitrary deterministic monotone0/T clocks of computed mesh tending to zero; beta may jump and only the weight is continuous.
Consumer: gradients of the SAME actual state Y in drift Ito; beta is never replaced by its possibly invalid START samples.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftRiemann
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorPredictableInputs BrownianFiniteStateDriftSource
open FiniteClockLeftApproximation
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ) {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

private theorem leftSample_bound (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (h0 : τ 0=0) (hT : τ (Fin.last n)=T) (H : ℝ≥0→ℝ) (K : ℝ≥0) (hb : ∀ u,‖H u‖≤K) (t : ℝ) :
    ‖leftSample τ H t‖≤K := by
  classical
  by_cases ht : t∈Ioc (0 : ℝ) (T : ℝ)
  · obtain ⟨i,hi⟩:=exists_clock_cell τ t (by simpa only [h0,NNReal.coe_zero] using ht.1)
      (by simpa only [hT] using ht.2)
    rw [leftSample_eq_cell τ hm H t i hi]
    exact hb _
  · have hi (i : Fin n) : t∉Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) := by
      intro hi
      apply ht
      refine ⟨lt_of_le_of_lt ?_ hi.1,hi.2.trans ?_⟩
      · exact (τ i.castSucc).coe_nonneg
      · exact_mod_cast (hm (Fin.le_last _)).trans hT.le
    simp only [leftSample,Set.indicator_of_notMem (hi _),Finset.sum_const_zero,norm_zero,K.coe_nonneg]

private theorem leftSample_measurable {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (H : ℝ≥0→ℝ) :
    Measurable (leftSample τ H) :=
  Finset.measurable_sum _ (fun _ _=>measurable_const.indicator measurableSet_Ioc)

private theorem bounded_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ→F) (hm : StronglyMeasurable f) (C : ℝ) (hb : ∀ t,‖f t‖≤C) (T : ℝ≥0) :
    Integrable f (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) :=
  (MemLp.of_bound (p := ∞) hm.aestronglyMeasurable C (ae_of_all _ hb)).integrable (by norm_num)

def weightedDriftSum (T : ℝ≥0) (β : ℝ×Sample d→E) {n : ℕ} (τ : Fin (n+1)→ℝ≥0)
    (H : ℝ≥0→ℝ) (ω : Sample d) : E :=
  ∑ i : Fin n,H (τ i.castSucc) • (drift d T β (τ i.succ) ω-drift d T β (τ i.castSucc) ω)

/-- Each actual primitive-increment sum is literally the Lebesgue integral
of the sampled WEIGHT against the original beta, not a sampled beta. -/
theorem weightedDriftSum_integral (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (hT : τ (Fin.last n)=T) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (H : ℝ≥0→ℝ) (ω : Sample d) :
    weightedDriftSum d T β τ H ω=∫ t in (0 : ℝ)..(T : ℝ),leftSample τ H t • β (t,ω) := by
  classical
  have hβ : StronglyMeasurable (fun t=>β (t,ω)) :=
    (hp.mono (predictableSigma_le d)).comp_measurable (measurable_id.prodMk measurable_const)
  have hi (i : Fin n) : Integrable
      (fun t=>(Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator (fun _=>H (τ i.castSucc)) t • β (t,ω))
      (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) := by
    have hs : StronglyMeasurable ((Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
        (fun _=>H (τ i.castSucc))) := stronglyMeasurable_const.indicator measurableSet_Ioc
    refine bounded_integrable _ (hs.smul hβ) (‖H (τ i.castSucc)‖*(B : ℝ)) ?_ T
    intro t
    change ‖(Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
      (fun _=>H (τ i.castSucc)) t • β (t,ω)‖≤_
    rw [norm_smul]
    gcongr
    exact norm_indicator_le_norm_self _ _
    exact hb _
  rw [weightedDriftSum,intervalIntegral.integral_of_le T.coe_nonneg]
  simp_rw [leftSample,Finset.sum_smul]
  rw [integral_finsetSum _ (fun i _=>hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have ho : τ i.castSucc≤τ i.succ := hm (by exact_mod_cast Nat.le_succ (i : ℕ))
  have hsub : Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)⊆Ioc (0 : ℝ) (T : ℝ) := by
    intro t ht
    refine ⟨lt_of_le_of_lt (τ i.castSucc).coe_nonneg ht.1,ht.2.trans ?_⟩
    exact_mod_cast (hm (Fin.le_last _)).trans hT.le
  rw [drift_increment d T _ _ ho ((hm (Fin.le_last _)).trans hT.le) β hp B hb,
    ← intervalIntegral.integral_smul,intervalIntegral.integral_of_le (by exact_mod_cast ho)]
  have he : (fun t=>(Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
      (fun _=>H (τ i.castSucc)) t • β (t,ω))=
      (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator (fun t=>H (τ i.castSucc) • β (t,ω)) := by
    ext t
    by_cases ht : t∈Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)
    · simp only [Set.indicator_of_mem ht]
    · simp only [Set.indicator_of_notMem ht,zero_smul]
  rw [he,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr hsub]

/-- Ordinary dominated convergence of actual weighted primitive increments.
The original drift is merely bounded predictable; its time paths need not
be continuous or Riemann integrable. -/
theorem weightedDriftSum_tendsto (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (H : ℝ≥0→ℝ) (hc : Continuous H)
    (K : ℝ≥0) (hH : ∀ u,‖H u‖≤K) (ω : Sample d) :
    Tendsto (fun n=>weightedDriftSum d T β (τ n) H ω) atTop
      (𝓝 (∫ t in (0 : ℝ)..(T : ℝ),H (Real.toNNReal t) • β (t,ω))) := by
  simp_rw [weightedDriftSum_integral d T _ (hm _) (hT _) β hp B hb]
  simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
  have hβ : StronglyMeasurable (fun t=>β (t,ω)) :=
    (hp.mono (predictableSigma_le d)).comp_measurable (measurable_id.prodMk measurable_const)
  apply tendsto_integral_of_dominated_convergence (fun _=>(K : ℝ)*(B : ℝ))
  · intro n
    exact ((leftSample_measurable (τ n) H).stronglyMeasurable.smul hβ).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun t=>by
      rw [norm_smul]
      exact mul_le_mul (leftSample_bound T (τ n) (hm n) (h0 n) (hT n) H K hH t) (hb (t,ω))
        (norm_nonneg _) K.coe_nonneg)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (leftSample_tendsto T N τ hm h0 hT hmesh H t ht.1 ht.2 hc.continuousWithinAt).smul tendsto_const_nhds

/-- Source-a.e. continuity of the actual weight suffices; there is no
all-time modification of beta or change of the underlying source law. -/
theorem actual_weightedDriftSum_tendsto (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (H : ℝ≥0→Sample d→ℝ)
    (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω)) (K : ℝ≥0) (hH : ∀ u ω,‖H u ω‖≤K) :
    ∀ᵐ ω ∂productLaw d,Tendsto (fun n=>weightedDriftSum d T β (τ n) (fun u=>H u ω) ω) atTop
      (𝓝 (∫ t in (0 : ℝ)..(T : ℝ),H (Real.toNNReal t) ω • β (t,ω))) :=
  hc.mono (fun ω h=>weightedDriftSum_tendsto d T N τ hm h0 hT hmesh β hp B hb _ h K (fun u=>hH u ω) ω)

/-- The weight is evaluated on the SAME actual initial-state/drift/noise
process, before the actual dt integration. -/
theorem functionOfState_weightedDriftSum_tendsto (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (x0 : E) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (family : Fin m→BrownianVectorPredictableInputs.fullPredictableL2 d T)
    (F : E→ℝ) (hF : Continuous F) (K : ℝ≥0) (hK : ∀ x,‖F x‖≤K) :
    ∀ᵐ ω ∂productLaw d,Tendsto
      (fun n=>weightedDriftSum d T β (τ n) (fun u=>F (state d T x0 β family u ω)) ω) atTop
      (𝓝 (∫ t in (0 : ℝ)..(T : ℝ),F (state d T x0 β family (Real.toNNReal t) ω) • β (t,ω))) :=
  actual_weightedDriftSum_tendsto d T N τ hm h0 hT hmesh β hp B hb _
    ((state_continuous d T x0 β hp B hb family).mono (fun _ h=>hF.comp h)) K (fun _ _=>hK _)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftRiemann
