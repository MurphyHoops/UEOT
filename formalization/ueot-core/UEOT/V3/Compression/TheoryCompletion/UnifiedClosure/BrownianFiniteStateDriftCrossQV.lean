import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftRiemann

/-!
Original commitment: initial-state/drift Ito needs actual quadratic variation of the SAME full physical state.
Existing result: actual original-noise weighted cross QV and computed-mesh finite-variation quadratic bounds.
Premise reduced: derive disappearance of actual bounded-drift squared and mixed increments, without a supplied bracket or fourth moment.
Model/witness: SAME joint product source, actual x0+Lebesgue beta+original M, deterministic caller partitions; bounded arbitrary actual START weights.
Consumer: actual state-Hessian weighted QV and Taylor remainder for drift Ito; no stopping/random partitions or implicit SDE assertion.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftCrossQV
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorPredictableInputs BrownianFiniteStateDriftSource
open BrownianVectorFiniteStateCrossQV BrownianFiniteStateTaylorRemainder
open BrownianVectorIntegralContinuousVersion BrownianVectorWeightedCrossQV
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

private theorem cross_cell_bound (D M : E) (j k : Fin m) :
    ‖(D j+M j)*(D k+M k)-M j*M k‖≤‖D‖^2+2*‖D‖*‖M‖ := by
  have he : (D j+M j)*(D k+M k)-M j*M k=D j*D k+D j*M k+M j*D k := by ring
  rw [he]
  calc
    _ ≤ ‖D j*D k‖+‖D j*M k‖+‖M j*D k‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ‖D‖*‖D‖+‖D‖*‖M‖+‖M‖*‖D‖ := by
      simp only [norm_mul]
      gcongr <;> exact PiLp.norm_apply_le _ _
    _ = _ := by ring

private theorem weighted_cross_difference_bound {ι : Type*} [Fintype ι] (D M : ι→E) (H : ι→ℝ)
    (K : ℝ≥0) (hH : ∀ i,‖H i‖≤K) (j k : Fin m) :
    ‖∑ i,H i*((D i j+M i j)*(D i k+M i k)-M i j*M i k)‖≤
      (K : ℝ)*((∑ i,‖D i‖^2)+2*Real.sqrt (∑ i,‖D i‖^2)*Real.sqrt (∑ i,‖M i‖^2)) := by
  classical
  calc
    _ ≤ ∑ i,‖H i*((D i j+M i j)*(D i k+M i k)-M i j*M i k)‖ := norm_sum_le _ _
    _ ≤ ∑ i,(K : ℝ)*(‖D i‖^2+2*‖D i‖*‖M i‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (hH i) (cross_cell_bound (D i) (M i) j k) (norm_nonneg _) K.coe_nonneg
    _ = (K : ℝ)*((∑ i,‖D i‖^2)+2*(∑ i,‖D i‖*‖M i‖)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add,mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
      apply add_le_add le_rfl
      calc
        2*(∑ i,‖D i‖*‖M i‖) ≤ 2*(Real.sqrt (∑ i,‖D i‖^2)*Real.sqrt (∑ i,‖M i‖^2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i=>‖D i‖) (fun i=>‖M i‖)) (by norm_num)
        _ = _ := by ring

/-- A pure actual-source subsequence criterion: an error bounded by a
vanishing deterministic coefficient times one plus a tight actual QV
quantity vanishes in measure. The original QV limit is not an input field
of the physical source. -/
private theorem tendstoInMeasure_of_tight_domination {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (R Q : ℕ→Ω→ℝ) (A : Ω→ℝ) (q : ℕ→Ω→ℝ)
    (hR : ∀ n,AEStronglyMeasurable (R n) μ) (hq : ∀ᵐ ω ∂μ,Tendsto (fun n=>q n ω) atTop (𝓝 0))
    (hQ : TendstoInMeasure μ Q atTop A) (hb : ∀ n ω,‖R n ω‖≤q n ω*(1+‖Q n ω‖)) :
    TendstoInMeasure μ R atTop (fun _=>(0 : ℝ)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hR).mpr
  intro ns hns
  obtain ⟨ms,hms,hQa⟩ := (hQ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hq,hQa] with ω hq hQa
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have he := (hq.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add hQa.norm)
  simp only [zero_mul] at he
  exact squeeze_zero (fun _=>norm_nonneg _) (fun _=>hb _ _) he

variable (d : ℕ) (T : ℝ≥0)

def weightedStateCrossSum {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (H : ℝ≥0→Sample d→ℝ)
    (x0 : E) (β : ℝ×Sample d→E) (family : Fin m→fullPredictableL2 d T) (j k : Fin m) (ω : Sample d) : ℝ :=
  ∑ i : Fin n,H (τ i.castSucc) ω*
    (state d T x0 β family (τ i.succ) ω j-state d T x0 β family (τ i.castSucc) ω j)*
    (state d T x0 β family (τ i.succ) ω k-state d T x0 β family (τ i.castSucc) ω k)

def crossDriftError {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (H : ℝ≥0→Sample d→ℝ)
    (x0 : E) (β : ℝ×Sample d→E) (family : Fin m→fullPredictableL2 d T) (j k : Fin m) (ω : Sample d) : ℝ :=
  weightedStateCrossSum d T τ H x0 β family j k ω-weightedCrossSum d T τ H (family j) (family k) ω

private theorem crossDriftError_bound {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (h0 : τ 0=0) (hT : τ (Fin.last n)=T) (H : ℝ≥0→Sample d→ℝ) (K : ℝ≥0) (hH : ∀ u ω,‖H u ω‖≤K)
    (x0 : E) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (family : Fin m→fullPredictableL2 d T) (j k : Fin m) (ω : Sample d) :
    let a:=(B : ℝ)^2*(BrownianQuadraticVariation.mesh τ : ℝ)*(T : ℝ)
    ‖crossDriftError d T τ H x0 β family j k ω‖≤(K : ℝ)*(a+2*Real.sqrt a)*
      (1+‖stateSquareSum d T family τ ω‖) := by
  let D (i : Fin n) : E:=drift d T β (τ i.succ) ω-drift d T β (τ i.castSucc) ω
  let M (i : Fin n) : E:=stateProcess d T family (τ i.succ) ω-stateProcess d T family (τ i.castSucc) ω
  let A : ℝ:=∑ i,‖D i‖^2
  let Q : ℝ:=∑ i,‖M i‖^2
  let a : ℝ:=(B : ℝ)^2*(BrownianQuadraticVariation.mesh τ : ℝ)*(T : ℝ)
  have hA : 0≤A := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hQ : 0≤Q := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have ha : 0≤a := by positivity
  have hAa : A≤a := driftSquareSum_mesh_bound d T τ hm h0 hT β hp B hb ω
  have he : crossDriftError d T τ H x0 β family j k ω=
      ∑ i,H (τ i.castSucc) ω*((D i j+M i j)*(D i k+M i k)-M i j*M i k) := by
    simp only [crossDriftError,weightedStateCrossSum,weightedCrossSum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [state,stateProcess_apply,D,M,PiLp.add_apply,PiLp.sub_apply]
    ring
  rw [he]
  have he' := weighted_cross_difference_bound D M (fun i=>H (τ i.castSucc) ω) K (fun i=>hH _ _) j k
  have hs : Real.sqrt Q≤1+Q := by
    nlinarith [Real.sq_sqrt hQ,Real.sqrt_nonneg Q,sq_nonneg (Real.sqrt Q-1)]
  have hsA : Real.sqrt A≤Real.sqrt a := Real.sqrt_le_sqrt hAa
  change _ ≤(K : ℝ)*(a+2*Real.sqrt a)*(1+‖Q‖)
  have hQnorm : ‖Q‖=Q := Real.norm_of_nonneg hQ
  rw [hQnorm]
  calc
    _ ≤ (K : ℝ)*(A+2*Real.sqrt A*Real.sqrt Q) := he'
    _ ≤ (K : ℝ)*(a+2*Real.sqrt a*(1+Q)) := by gcongr
    _ ≤ _ := by
      have hmul := mul_nonneg ha hQ
      nlinarith [K.coe_nonneg]

/-- Actual bounded-drift mixed and squared contributions vanish on the
SAME original state/noise/partitions. Original input L2 suffices. -/
theorem crossDriftError_tendstoInMeasure (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (H : ℝ≥0→Sample d→ℝ) (hH : ∀ u,Measurable (H u)) (K : ℝ≥0) (hbH : ∀ u ω,‖H u ω‖≤K)
    (x0 : E) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (family : Fin m→fullPredictableL2 d T) (j k : Fin m) :
    TendstoInMeasure (productLaw d) (fun n=>crossDriftError d T (τ n) H x0 β family j k) atTop (fun _=>0) := by
  let a (n : ℕ) : ℝ:=(B : ℝ)^2*(BrownianQuadraticVariation.mesh (τ n) : ℝ)*(T : ℝ)
  apply tendstoInMeasure_of_tight_domination (productLaw d) _
    (fun n=>stateSquareSum d T family (τ n)) (fun ω=>∑ j,BrownianVectorIntegralTimeEnergy.timeEnergy d T (family j) T ω)
    (fun n _=>(K : ℝ)*(a n+2*Real.sqrt (a n)))
  · intro n
    have hS (u : ℝ≥0) : Measurable (state d T x0 β family u) :=
      ((state_stronglyAdapted d T x0 β hp family u).mono ((jointNaturalFiltration d).le u)).measurable
    have hM (u : ℝ≥0) (i : Fin m) : Measurable (fun ω=>continuousIntegralProcess d T (family i) u ω) :=
      (continuousIntegralProcess_stronglyAdapted d T (family i) u).mono ((jointNaturalFiltration d).le u) |>.measurable
    have hC (u : ℝ≥0) (i : Fin m) : Measurable (fun ω=>state d T x0 β family u ω i) :=
      (PiLp.continuous_apply 2 _ i).measurable.comp (hS u)
    exact ((Finset.measurable_fun_sum _ (fun i _=>((hH _).mul ((hC _ j).sub (hC _ j))).mul ((hC _ k).sub (hC _ k)))).sub
      (Finset.measurable_fun_sum _ (fun i _=>((hH _).mul ((hM _ j).sub (hM _ j))).mul ((hM _ k).sub (hM _ k))))).aestronglyMeasurable
  · have ha : Tendsto a atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using (hmesh.const_mul ((B : ℝ)^2)).mul_const (T : ℝ)
    apply ae_of_all
    intro ω
    simpa only [Real.sqrt_zero,mul_zero,zero_add] using (ha.add (ha.sqrt.const_mul 2)).const_mul (K : ℝ)
  · exact stateSquareSum_tendstoInMeasure d T family N τ hm h0 hT hmesh
  · exact fun n ω=>crossDriftError_bound d T (τ n) (hm n) (h0 n) (hT n) H K hbH x0 β hp B hb family j k ω

private theorem weightedStateCrossSum_measurable {n : ℕ} (τ : Fin (n+1)→ℝ≥0)
    (H : ℝ≥0→Sample d→ℝ) (hH : ∀ u,Measurable (H u))
    (x0 : E) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (family : Fin m→fullPredictableL2 d T) (j k : Fin m) :
    Measurable (weightedStateCrossSum d T τ H x0 β family j k) := by
  have hc (u : ℝ≥0) (i : Fin m) : Measurable (fun ω=>state d T x0 β family u ω i) :=
    (PiLp.continuous_apply 2 _ i).measurable.comp
      (((state_stronglyAdapted d T x0 β hp family u).mono ((jointNaturalFiltration d).le u)).measurable)
  exact Finset.measurable_fun_sum _ (fun i _=>((hH _).mul ((hc _ j).sub (hc _ j))).mul ((hc _ k).sub (hc _ k)))

/-- Actual START-weighted cross QV of Y=x0+actual drift+original M has
EXACTLY the original-noise dt energy with the SAME supplied weight H. -/
theorem weightedStateCross_QV_tendstoInMeasure (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (H : ℝ≥0→Sample d→ℝ) (hj : Measurable (Function.uncurry H))
    (hH : StronglyAdapted (jointNaturalFiltration d) H) (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω))
    (K : ℝ≥0) (hbH : ∀ u ω,‖H u ω‖≤K)
    (x0 : E) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (family : Fin m→fullPredictableL2 d T) (j k : Fin m) :
    TendstoInMeasure (productLaw d) (fun n=>weightedStateCrossSum d T (τ n) H x0 β family j k) atTop
      (weightedTimeEnergy d T H (family j) (family k)) := by
  have hHs (u : ℝ≥0) : Measurable (H u) := ((hH u).mono ((jointNaturalFiltration d).le u)).measurable
  have hM := weightedCross_QV_tendstoInMeasure d T N τ hm h0 hT hmesh H hj hH hc K K.coe_nonneg hbH (family j) (family k)
  have hE := crossDriftError_tendstoInMeasure d T N τ hm h0 hT hmesh H hHs K hbH x0 β hp B hb family j k
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n=>(weightedStateCrossSum_measurable d T (τ n) H hHs x0 β hp family j k).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms,hms,hMa⟩ := (hM.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks,hks,hEa⟩ := (hE.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks,hms.comp hks,?_⟩
  filter_upwards [hMa,hEa] with ω hMa hEa
  have he := hEa.add (hMa.comp hks.tendsto_atTop)
  simp only [zero_add] at he
  convert he using 1
  ext n
  simp only [Function.comp_apply,crossDriftError]
  ring

private theorem stateSquare_bound {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (h0 : τ 0=0) (hT : τ (Fin.last n)=T) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (ω : Sample d) :
    (∑ i : Fin n,‖state d T x0 β family (τ i.succ) ω-state d T x0 β family (τ i.castSucc) ω‖^2)≤
      2*((B : ℝ)^2*(BrownianQuadraticVariation.mesh τ : ℝ)*(T : ℝ)+1)*
        (1+‖stateSquareSum d T family τ ω‖) := by
  let D (i : Fin n) : E:=drift d T β (τ i.succ) ω-drift d T β (τ i.castSucc) ω
  let M (i : Fin n) : E:=stateProcess d T family (τ i.succ) ω-stateProcess d T family (τ i.castSucc) ω
  have he (i : Fin n) : state d T x0 β family (τ i.succ) ω-state d T x0 β family (τ i.castSucc) ω=D i+M i := by
    simp only [state,D,M]; abel
  simp_rw [he]
  have hc (i : Fin n) : ‖D i+M i‖^2≤2*‖D i‖^2+2*‖M i‖^2 := by
    have h:=norm_add_le (D i) (M i)
    have hs:=(sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
    nlinarith [sq_nonneg (‖D i‖-‖M i‖)]
  have hs:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hc i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hd:=driftSquareSum_mesh_bound d T τ hm h0 hT β hp B hb ω
  have hQ : 0≤stateSquareSum d T family τ ω := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have ha : 0≤(B : ℝ)^2*(BrownianQuadraticVariation.mesh τ : ℝ)*(T : ℝ) := by positivity
  have hQnorm : ‖stateSquareSum d T family τ ω‖=stateSquareSum d T family τ ω := Real.norm_of_nonneg hQ
  rw [hQnorm]
  change (∑ i,‖D i+M i‖^2)≤_ 
  change (∑ i,‖D i‖^2)≤_ at hd
  change (∑ i,‖D i+M i‖^2)≤2*(∑ i,‖D i‖^2)+2*stateSquareSum d T family τ ω at hs
  nlinarith [mul_nonneg ha hQ]

/-- Actual C2 Taylor remainders on the SAME physical drift state vanish.
Only original input L2, bounded measurable beta and continuous actual Y
enter; no beta time continuity, input L4 or third derivative is supplied. -/
theorem actual_drift_remainder_tendstoInMeasure (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (x0 : E) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (family : Fin m→fullPredictableL2 d T)
    (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) :
    TendstoInMeasure (productLaw d) (fun n ω=>remainderSum φ (τ n) (fun u=>state d T x0 β family u ω)) atTop
      (fun _=>0) := by
  let a (n : ℕ) : ℝ:=(B : ℝ)^2*(BrownianQuadraticVariation.mesh (τ n) : ℝ)*(T : ℝ)
  apply tendstoInMeasure_of_tight_domination (productLaw d) _
    (fun n=>stateSquareSum d T family (τ n)) (fun ω=>∑ j,BrownianVectorIntegralTimeEnergy.timeEnergy d T (family j) T ω)
    (fun n ω=>(gridRatio φ (τ n) (fun u=>state d T x0 β family u ω) : ℝ)*(2*(a n+1)))
  · intro n
    exact (remainderSum_measurable φ hφ (τ n) (state d T x0 β family)
      (fun u=>((state_stronglyAdapted d T x0 β hp family u).mono ((jointNaturalFiltration d).le u)).measurable)).aestronglyMeasurable
  · have ha : Tendsto a atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using (hmesh.const_mul ((B : ℝ)^2)).mul_const (T : ℝ)
    filter_upwards [state_continuous d T x0 β hp B hb family] with ω hc
    have hq:=gridRatio_tendsto φ hφ T N τ hm hT hmesh _ hc
    have he:=hq.mul (((ha.add_const 1).const_mul 2))
    simpa only [zero_add,zero_mul] using he
  · exact stateSquareSum_tendstoInMeasure d T family N τ hm h0 hT hmesh
  · intro n ω
    calc
      _ ≤ (gridRatio φ (τ n) (fun u=>state d T x0 β family u ω) : ℝ)*
          (∑ i : Fin (N n),‖state d T x0 β family (τ n i.succ) ω-state d T x0 β family (τ n i.castSucc) ω‖^2) :=
        remainderSum_norm_le φ (τ n) _
      _ ≤ (gridRatio φ (τ n) (fun u=>state d T x0 β family u ω) : ℝ)*
          (2*(a n+1)*(1+‖stateSquareSum d T family (τ n) ω‖)) :=
        mul_le_mul_of_nonneg_left (stateSquare_bound d T (τ n) (hm n) (h0 n) (hT n) x0 β hp B hb family ω)
          (gridRatio φ (τ n) (fun u=>state d T x0 β family u ω)).coe_nonneg
      _ = _ := by ring

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftCrossQV
