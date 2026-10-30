import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftCrossQV

/-!
Original commitment: physical finite-state Ito includes its declared initial state and actual finite-variation drift with the original noise.
Existing result: actual bounded predictable drift, SAME-state weighted primitive sums/cross QV and C2 Taylor remainder are derived.
Premise reduced: assemble the actual derivative-generated original stochastic input, actual beta dt and Hessian energy into one SAME-state identity.
Model/witness: Y=x0+actual Lebesgue beta+original M_family, finite m/d, bounded genuine joint-predictable beta, C2/global native derivative bounds.
Consumer: actual state/control calculus; this explicitly constructed process is not an assumed solution of an arbitrary implicit SDE.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftItoSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorPredictableInputs BrownianVectorPredictableDensity
open BrownianVectorFiniteStateCrossQV
open BrownianVectorIntegralContinuousVersion BrownianVectorPredictableMultiplier BrownianVectorLeftMultiplierBinding
open BrownianVectorWeightedCrossQV BrownianFiniteStateTaylorRemainder BrownianFiniteStateItoSource
open BrownianFiniteStateDriftSource BrownianFiniteStateDriftRiemann BrownianFiniteStateDriftCrossQV BrownianQuadraticVariation
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
set_option maxHeartbeats 1000000
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

private theorem add_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : ℕ→Ω→ℝ) (f g : Ω→ℝ)
    (hF : ∀ n,AEStronglyMeasurable (F n) μ) (hG : ∀ n,AEStronglyMeasurable (G n) μ)
    (hf : TendstoInMeasure μ F atTop f) (hg : TendstoInMeasure μ G atTop g) :
    TendstoInMeasure μ (fun n ω=>F n ω+G n ω) atTop (fun ω=>f ω+g ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n=>(hF n).add (hG n))).mpr
  intro ns hns
  obtain ⟨ms,hms,hFa⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks,hks,hGa⟩ := (hg.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks,hms.comp hks,?_⟩
  filter_upwards [hFa,hGa] with ω hFa hGa
  exact (hFa.comp hks.tendsto_atTop).add hGa

private theorem sum_tendstoInMeasure {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Finset ι) (F : ι→ℕ→Ω→ℝ) (f : ι→Ω→ℝ)
    (hF : ∀ i∈s,∀ n,AEStronglyMeasurable (F i n) μ)
    (hf : ∀ i∈s,TendstoInMeasure μ (F i) atTop (f i)) :
    TendstoInMeasure μ (fun n ω=>∑ i∈s,F i n ω) atTop (fun ω=>∑ i∈s,f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact tendstoInMeasure_of_tendsto_ae (fun _=>aestronglyMeasurable_const) (ae_of_all _ (fun _=>tendsto_const_nhds))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    apply add_tendstoInMeasure μ _ _ _ _ (hF i (Finset.mem_insert_self i s))
      (fun n=>Finset.aestronglyMeasurable_fun_sum _ (fun j hj=>hF j (Finset.mem_insert_of_mem hj) n))
      (hf i (Finset.mem_insert_self i s))
    exact ih (fun j hj=>hF j (Finset.mem_insert_of_mem hj)) (fun j hj=>hf j (Finset.mem_insert_of_mem hj))


private def physicalReadout (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (family : Fin m→fullPredictableL2 d T) (F : E→ℝ) (u : ℝ≥0) (ω : Sample d) : ℝ := F (state d T x0 β family u ω)


private theorem physicalReadout_measurable (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (F : E→ℝ) (hF : Continuous F) :
    Measurable (Function.uncurry (physicalReadout d T x0 β family F)) :=
  hF.measurable.comp (state_measurable d T x0 β hp B hb family)

private theorem physicalReadout_adapted (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (family : Fin m→fullPredictableL2 d T) (F : E→ℝ) (hF : Continuous F) :
    StronglyAdapted (jointNaturalFiltration d) (physicalReadout d T x0 β family F) :=
  fun u=>hF.comp_stronglyMeasurable (state_stronglyAdapted d T x0 β hp family u)

private theorem physicalReadout_continuous (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (F : E→ℝ) (hF : Continuous F) :
    ∀ᵐ ω ∂productLaw d,Continuous (fun u=>physicalReadout d T x0 β family F u ω) :=
  (state_continuous d T x0 β hp B hb family).mono (fun _ h=>hF.comp h)

/-- ONE original input, literally computed from the gradient on SAME Y and
same original noise inputs. There is no desired stochastic output field. -/
def driftItoInput (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (K : ℝ≥0) (hK : ∀ x,‖fderiv ℝ φ x‖≤K) :
    fullPredictableL2 d T :=
  ∑ j,continuousMultiplier d T (physicalReadout d T x0 β family (gradientEntry φ j))
    (physicalReadout_measurable d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j))
    (physicalReadout_adapted d T x0 β hp family _ (gradientEntry_continuous φ hφ j))
    (physicalReadout_continuous d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j))
    K (fun _ _=>gradientEntry_bound φ K hK j _) (family j)

theorem driftItoInput_coe (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (K : ℝ≥0) (hK : ∀ x,‖fderiv ℝ φ x‖≤K) :
    (driftItoInput d T x0 β hp B hb family φ hφ K hK : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      fun p=>∑ j,gradientEntry φ j (state d T x0 β family (Real.toNNReal p.1) p.2) •
        (family j : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p := by
  let V (j : Fin m) := continuousMultiplier d T (physicalReadout d T x0 β family (gradientEntry φ j))
    (physicalReadout_measurable d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j))
    (physicalReadout_adapted d T x0 β hp family _ (gradientEntry_continuous φ hφ j))
    (physicalReadout_continuous d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j))
    K (fun _ _=>gradientEntry_bound φ K hK j _) (family j)
  change (∑ j,V j : fullPredictableL2 d T).val =ᵐ[inputLaw d T] _
  simp only [Submodule.coe_sum]
  have hi : ∀ᵐ p ∂inputLaw d T,∀ j,(V j : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p=
      gradientEntry φ j (state d T x0 β family (Real.toNNReal p.1) p.2) •
        (family j : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p :=
    ae_all_iff.mpr (fun j=>continuousMultiplier_coe d T _ _ _ _ K _ (family j))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j=>(V j : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))),hi]
    with p hs hi
  simp only [Finset.sum_apply] at hs
  exact hs.trans (Finset.sum_congr rfl (fun j _=>hi j))

/-- Actual ordinary drift energy, retaining beta's literal time integral. -/
def driftFirstEnergy (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (ω : Sample d) : ℝ :=
  ∑ j,(∫ t in (0 : ℝ)..(T : ℝ),
    gradientEntry φ j (state d T x0 β family (Real.toNNReal t) ω) • β (t,ω)) j

def driftSecondEnergy (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (ω : Sample d) : ℝ :=
  ∑ j,∑ k,weightedTimeEnergy d T
    (physicalReadout d T x0 β family (hessianEntry φ j k)) (family j) (family k) ω

private def noiseFirstSum (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (ω : Sample d) : ℝ :=
  ∑ j,weightedIncrementSum d T τ (physicalReadout d T x0 β family (gradientEntry φ j)) (family j) ω

private def driftFirstSum (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (ω : Sample d) : ℝ :=
  ∑ j,(weightedDriftSum d T β τ (fun u=>gradientEntry φ j (state d T x0 β family u ω)) ω) j

private theorem drift_first_decomposition (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (ω : Sample d) :
    firstSum φ τ (fun u=>state d T x0 β family u ω)=
      noiseFirstSum d T x0 β family φ τ ω+driftFirstSum d T x0 β family φ τ ω := by
  simp only [firstSum,noiseFirstSum,driftFirstSum,weightedIncrementSum,weightedDriftSum,physicalReadout,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ i : Fin n,gradientEntry φ j (state d T x0 β family (τ i.castSucc) ω) •
      (drift d T β (τ i.succ) ω-drift d T β (τ i.castSucc) ω)) j=
      ∑ i : Fin n,gradientEntry φ j (state d T x0 β family (τ i.castSucc) ω)*
        (drift d T β (τ i.succ) ω j-drift d T β (τ i.castSucc) ω j) := by
    change (EuclideanSpace.proj (𝕜:=ℝ) j) _=_
    rw [map_sum]
    rfl
  rw [he,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [state,PiLp.add_apply,stateProcess_apply]
  ring

private theorem noiseFirstSum_measurable (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) :
    Measurable (noiseFirstSum d T x0 β family φ τ) := by
  have hs (u : ℝ≥0) : Measurable (state d T x0 β family u) :=
    ((state_stronglyAdapted d T x0 β hp family u).mono ((jointNaturalFiltration d).le u)).measurable
  have hM (j : Fin m) (u : ℝ≥0) : Measurable (continuousIntegralProcess d T (family j) u) :=
    ((continuousIntegralProcess_stronglyAdapted d T (family j) u).mono ((jointNaturalFiltration d).le u)).measurable
  exact Finset.measurable_fun_sum _ (fun j _=>Finset.measurable_fun_sum _ (fun i _=>
    (((gradientEntry_continuous φ hφ j).measurable.comp (hs _)).mul ((hM j _).sub (hM j _)))))

private theorem driftFirstSum_measurable (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) :
    Measurable (driftFirstSum d T x0 β family φ τ) := by
  have hs (u : ℝ≥0) : Measurable (state d T x0 β family u) :=
    ((state_stronglyAdapted d T x0 β hp family u).mono ((jointNaturalFiltration d).le u)).measurable
  have hD (u : ℝ≥0) : Measurable (drift d T β u) :=
    ((drift_stronglyAdapted d T β hp u).mono ((jointNaturalFiltration d).le u)).measurable
  apply Finset.measurable_fun_sum
  intro j _
  apply (PiLp.continuous_apply 2 (fun _ : Fin m=>ℝ) j).measurable.comp
  exact Finset.measurable_fun_sum _ (fun i _=>
    (((gradientEntry_continuous φ hφ j).measurable.comp (hs _)).smul ((hD _).sub (hD _))))

private theorem noiseFirstSum_limit (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (K : ℝ≥0) (hK : ∀ x,‖fderiv ℝ φ x‖≤K)
    (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0) (hm : ∀ n,Monotone (τ n))
    (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(mesh (τ n) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure (productLaw d) (fun n=>noiseFirstSum d T x0 β family φ (τ n)) atTop
      (continuousIntegralProcess d T (driftItoInput d T x0 β hp B hb family φ hφ K hK) T) := by
  let H (j : Fin m) := physicalReadout d T x0 β family (gradientEntry φ j)
  let g (j : Fin m) := continuousMultiplier d T (H j)
    (physicalReadout_measurable d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j))
    (physicalReadout_adapted d T x0 β hp family _ (gradientEntry_continuous φ hφ j))
    (physicalReadout_continuous d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j))
    K (fun u ω=>by simpa only [H,physicalReadout] using gradientEntry_bound φ K hK j (state d T x0 β family u ω)) (family j)
  have hj (j : Fin m) := weightedIncrementSum_tendstoInMeasure d T N τ hm h0 hT hmesh (H j)
    (physicalReadout_measurable d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j))
    (physicalReadout_adapted d T x0 β hp family _ (gradientEntry_continuous φ hφ j))
    (physicalReadout_continuous d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j))
    K K.coe_nonneg (fun u ω=>by simpa only [H,physicalReadout] using gradientEntry_bound φ K hK j (state d T x0 β family u ω)) (family j)
  have hsum : TendstoInMeasure (productLaw d)
      (fun n ω=>∑ j,weightedIncrementSum d T (τ n) (H j) (family j) ω) atTop
      (fun ω=>∑ j,continuousIntegralProcess d T (g j) T ω) := by
    apply sum_tendstoInMeasure
    · intro j _ n
      have hH (u : ℝ≥0) : Measurable (H j u) :=
        (((physicalReadout_adapted d T x0 β hp family _ (gradientEntry_continuous φ hφ j)) u).mono
          ((jointNaturalFiltration d).le u)).measurable
      have hM (u : ℝ≥0) : Measurable (continuousIntegralProcess d T (family j) u) :=
        ((continuousIntegralProcess_stronglyAdapted d T (family j) u).mono ((jointNaturalFiltration d).le u)).measurable
      exact (Finset.measurable_fun_sum _ (fun i _=>(hH _).mul ((hM _).sub (hM _)))).aestronglyMeasurable
    · exact fun j _=>hj j
  apply hsum.congr_right
  have hi : ∀ᵐ ω ∂productLaw d,∀ j,(BrownianVectorPredictableDensity.predictableIntegral d T (g j) : Sample d→ℝ) ω=
      continuousIntegralProcess d T (g j) T ω :=
    ae_all_iff.mpr (fun j=>(continuousIntegralProcess_horizon d T (g j)).symm)
  have hs : BrownianVectorPredictableDensity.predictableIntegral d T (∑ j,g j)=ᵐ[productLaw d]
      fun ω=>∑ j,(BrownianVectorPredictableDensity.predictableIntegral d T (g j) : Sample d→ℝ) ω := by
    rw [map_sum]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j=>BrownianVectorPredictableDensity.predictableIntegral d T (g j))] with ω hs
    simpa only [Finset.sum_apply] using hs
  filter_upwards [hi,hs,continuousIntegralProcess_horizon d T (∑ j,g j)] with ω hi hs hh
  exact (Finset.sum_congr rfl (fun j _=>(hi j).symm)).trans (hs.symm.trans hh.symm)

private theorem driftFirstSum_limit (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (K : ℝ≥0) (hK : ∀ x,‖fderiv ℝ φ x‖≤K)
    (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0) (hm : ∀ n,Monotone (τ n))
    (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(mesh (τ n) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure (productLaw d) (fun n=>driftFirstSum d T x0 β family φ (τ n)) atTop
      (driftFirstEnergy d T x0 β family φ) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun n=>(driftFirstSum_measurable d T x0 β hp family φ hφ (τ n)).aestronglyMeasurable)
  have hi : ∀ᵐ ω ∂productLaw d,∀ j : Fin m,Tendsto
      (fun n=>weightedDriftSum d T β (τ n) (fun u=>gradientEntry φ j (state d T x0 β family u ω)) ω) atTop
      (𝓝 (∫ t in (0 : ℝ)..(T : ℝ),gradientEntry φ j (state d T x0 β family (Real.toNNReal t) ω) • β (t,ω))) :=
    ae_all_iff.mpr (fun j=>functionOfState_weightedDriftSum_tendsto d T N τ hm h0 hT hmesh x0 β hp B hb family
      (gradientEntry φ j) (gradientEntry_continuous φ hφ j) K (gradientEntry_bound φ K hK j))
  filter_upwards [hi] with ω hi
  apply tendsto_finsetSum
  intro j _
  exact ((PiLp.continuous_apply 2 (fun _ : Fin m=>ℝ) j).tendsto _).comp (hi j)

private theorem secondSum_limit (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (K : ℝ≥0) (hK : ∀ x,‖hessian φ x‖≤K)
    (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0) (hm : ∀ n,Monotone (τ n))
    (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(mesh (τ n) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure (productLaw d) (fun n ω=>secondSum φ (τ n) (fun u=>state d T x0 β family u ω)) atTop
      (driftSecondEnergy d T x0 β family φ) := by
  have hs (u : ℝ≥0) : Measurable (state d T x0 β family u) :=
    ((state_stronglyAdapted d T x0 β hp family u).mono ((jointNaturalFiltration d).le u)).measurable
  have hc (u : ℝ≥0) (j : Fin m) : Measurable (fun ω=>state d T x0 β family u ω j) :=
    (PiLp.continuous_apply 2 _ j).measurable.comp (hs u)
  have he (j k : Fin m) (n : ℕ) : Measurable
      (weightedStateCrossSum d T (τ n) (physicalReadout d T x0 β family (hessianEntry φ j k)) x0 β family j k) :=
    Finset.measurable_fun_sum _ (fun i _=>
      ((((hessianEntry_continuous φ hφ j k).measurable.comp (hs _)).mul ((hc _ j).sub (hc _ j))).mul ((hc _ k).sub (hc _ k))))
  change TendstoInMeasure (productLaw d)
    (fun n ω=>∑ j,∑ k,weightedStateCrossSum d T (τ n)
      (physicalReadout d T x0 β family (hessianEntry φ j k)) x0 β family j k ω) atTop _
  apply sum_tendstoInMeasure
  · intro j _ n
    exact Finset.aestronglyMeasurable_fun_sum _ (fun k _=>(he j k n).aestronglyMeasurable)
  · intro j _
    apply sum_tendstoInMeasure
    · intro k _ n
      exact (he j k n).aestronglyMeasurable
    · intro k _
      exact weightedStateCross_QV_tendstoInMeasure d T N τ hm h0 hT hmesh
        (physicalReadout d T x0 β family (hessianEntry φ j k))
        (physicalReadout_measurable d T x0 β hp B hb family _ (hessianEntry_continuous φ hφ j k))
        (physicalReadout_adapted d T x0 β hp family _ (hessianEntry_continuous φ hφ j k))
        (physicalReadout_continuous d T x0 β hp B hb family _ (hessianEntry_continuous φ hφ j k))
        K (fun _ _=>hessianEntry_bound φ K hK j k _) x0 β hp B hb family j k

/-- Actual initial-state/bounded-drift finite-state C2 Ito identity. The
ordinary beta dt term, original gradient-generated stochastic input and
original Hessian time energy are all computed on SAME Y and SAME source.
This constructs a process from beta; it does not solve an implicit SDE. -/
theorem actual_drift_state_ito (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₁ K₂ : ℝ≥0) (hb₁ : ∀ x,‖fderiv ℝ φ x‖≤K₁) (hb₂ : ∀ x,‖hessian φ x‖≤K₂) :
    (fun ω=>φ (state d T x0 β family T ω))=ᵐ[productLaw d] fun ω=>φ x0+
      continuousIntegralProcess d T (driftItoInput d T x0 β hp B hb family φ hφ K₁ hb₁) T ω+
      driftFirstEnergy d T x0 β family φ ω+(1/2 : ℝ)*driftSecondEnergy d T x0 β family φ ω := by
  have hF:=noiseFirstSum_limit d T x0 β hp B hb family φ hφ K₁ hb₁
    (fun n=>n+1) (uniformClock T) (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
  have hD:=driftFirstSum_limit d T x0 β hp B hb family φ hφ K₁ hb₁
    (fun n=>n+1) (uniformClock T) (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
  have hS:=secondSum_limit d T x0 β hp B hb family φ hφ K₂ hb₂
    (fun n=>n+1) (uniformClock T) (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
  have hR:=actual_drift_remainder_tendstoInMeasure d T (fun n=>n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) x0 β hp B hb family φ hφ
  obtain ⟨ns,hns,hFa⟩:=hF.exists_seq_tendsto_ae
  obtain ⟨ms,hms,hDa⟩:=(hD.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks,hks,hSa⟩:=(hS.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  obtain ⟨ls,hls,hRa⟩:=(hR.comp (hns.tendsto_atTop.comp (hms.tendsto_atTop.comp hks.tendsto_atTop))).exists_seq_tendsto_ae
  filter_upwards [hFa,hDa,hSa,hRa,state_initial d T x0 β family] with ω hf hd hs hr hz
  have hf':=hf.comp (hms.tendsto_atTop.comp (hks.tendsto_atTop.comp hls.tendsto_atTop))
  have hd':=hd.comp (hks.tendsto_atTop.comp hls.tendsto_atTop)
  have hs':=hs.comp hls.tendsto_atTop
  have htotal:=((hf'.add hd').add (hs'.const_mul (1/2 : ℝ))).add hr
  have he (i : ℕ) :
      noiseFirstSum d T x0 β family φ (uniformClock T (ns (ms (ks (ls i))))) ω+
      driftFirstSum d T x0 β family φ (uniformClock T (ns (ms (ks (ls i))))) ω+
      (1/2 : ℝ)*secondSum φ (uniformClock T (ns (ms (ks (ls i))))) (fun u=>state d T x0 β family u ω)+
      remainderSum φ (uniformClock T (ns (ms (ks (ls i))))) (fun u=>state d T x0 β family u ω)=
      φ (state d T x0 β family T ω)-φ x0 := by
    rw [←drift_first_decomposition d T x0 β family]
    have ht:=finite_taylor_telescope φ (uniformClock T (ns (ms (ks (ls i))))) (fun u=>state d T x0 β family u ω)
    rw [uniformClock_end,uniformClock_zero,hz] at ht
    exact ht.symm
  have hsame:=(tendsto_congr' (Eventually.of_forall he)).mp htotal
  have heq : continuousIntegralProcess d T (driftItoInput d T x0 β hp B hb family φ hφ K₁ hb₁) T ω+
      driftFirstEnergy d T x0 β family φ ω+(1/2 : ℝ)*driftSecondEnergy d T x0 β family φ ω=
      φ (state d T x0 β family T ω)-φ x0 :=
    tendsto_nhds_unique (by simpa only [add_zero] using hsame) tendsto_const_nhds
  linarith

/-- The coordinate-assembled drift term is EXACTLY the native original
Frechet derivative against the actual beta dt. This is every raw sample,
not a Riemann sum of point-sampled beta. -/
theorem driftFirstEnergy_eq_integral (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (K : ℝ≥0)
    (hK : ∀ x,‖fderiv ℝ φ x‖≤K) (ω : Sample d) :
    driftFirstEnergy d T x0 β family φ ω=
      ∫ t in (0 : ℝ)..(T : ℝ),fderiv ℝ φ (state d T x0 β family (Real.toNNReal t) ω) (β (t,ω)) := by
  let G (j : Fin m) (t : ℝ) : E:=gradientEntry φ j (state d T x0 β family (Real.toNNReal t) ω) • β (t,ω)
  let L (j : Fin m) : E→L[ℝ] ℝ:=EuclideanSpace.proj (𝕜:=ℝ) j
  have hβ : StronglyMeasurable (fun t=>β (t,ω)) :=
    (hp.mono (predictableSigma_le d)).comp_measurable (measurable_id.prodMk measurable_const)
  have hG (j : Fin m) : IntervalIntegrable (G j) volume 0 T := by
    have hH : StronglyMeasurable (fun t=>gradientEntry φ j (state d T x0 β family (Real.toNNReal t) ω)) :=
      ((physicalReadout_measurable d T x0 β hp B hb family _ (gradientEntry_continuous φ hφ j)).comp
        (measurable_id.real_toNNReal.prodMk measurable_const)).stronglyMeasurable
    have hi : MemLp (G j) ∞ (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) :=
      MemLp.of_bound (hH.smul hβ).aestronglyMeasurable ((K : ℝ)*(B : ℝ)) (ae_of_all _ (fun t=>by
        dsimp only [G]
        rw [norm_smul]
        exact mul_le_mul (gradientEntry_bound φ K hK j _) (hb (t,ω)) (norm_nonneg _) K.coe_nonneg))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr (hi.integrable (by norm_num))
  have hL (j : Fin m) : IntervalIntegrable (fun t=>L j (G j t)) volume 0 T :=
    ⟨(L j).integrable_comp (hG j).1,(L j).integrable_comp (hG j).2⟩
  calc
    _ = ∑ j,∫ t in (0 : ℝ)..(T : ℝ),L j (G j t) := by
      apply Finset.sum_congr rfl
      intro j _
      exact ((L j).intervalIntegral_comp_comm (hG j)).symm
    _ = ∫ t in (0 : ℝ)..(T : ℝ),∑ j,L j (G j t) :=
      (intervalIntegral.integral_finsetSum (fun j _=>hL j)).symm
    _ = _ := by
      congr 1
      ext t
      simp only [G,L,map_smul,smul_eq_mul,derivative_coordinates]
      rfl

/-- Displayed actual drift Ito: the returned original input, actual ordinary
Frechet drift integral and original weighted Hessian energy share exactly
one state/source. Global derivative bounds remain explicit permissions. -/
theorem actual_drift_state_ito_integral (d : ℕ) (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B)
    (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₁ K₂ : ℝ≥0) (hb₁ : ∀ x,‖fderiv ℝ φ x‖≤K₁) (hb₂ : ∀ x,‖hessian φ x‖≤K₂) :
    (fun ω=>φ (state d T x0 β family T ω))=ᵐ[productLaw d] fun ω=>φ x0+
      continuousIntegralProcess d T (driftItoInput d T x0 β hp B hb family φ hφ K₁ hb₁) T ω+
      (∫ t in (0 : ℝ)..(T : ℝ),fderiv ℝ φ (state d T x0 β family (Real.toNNReal t) ω) (β (t,ω)))+
      (1/2 : ℝ)*driftSecondEnergy d T x0 β family φ ω := by
  filter_upwards [actual_drift_state_ito d T x0 β hp B hb family φ hφ K₁ K₂ hb₁ hb₂] with ω h
  exact h.trans (by rw [driftFirstEnergy_eq_integral d T x0 β hp B hb family φ hφ K₁ hb₁])

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftItoSource
