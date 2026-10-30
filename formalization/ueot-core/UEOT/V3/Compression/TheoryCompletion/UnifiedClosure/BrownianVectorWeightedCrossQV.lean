import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorLeftMultiplierBinding

/-!
Original commitment: state Itô needs actual time/state-dependent START-weighted cross-QV of SAME observed state inputs.
Existing result: SAME full-input cross-QV, native grid stability, actual sampled-input convergence and bounded START-window return.
Premise reduced: identify sampled-input cell increments with H_START times ORIGINAL M_g increments, then derive actual weighted cross-QV target.
Model/witness: original joint product source/full Euclidean f,g, bounded joint-adapted AE-continuous H, deterministic same caller mono0/T clocks/mesh→0.
Consumer: bounded continuous F(SAME actual finite state) Hessian-type terms; state Taylor remainder and state Itô remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorWeightedCrossQV
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorPredictableInputs BrownianVectorPredictableDensity
open BrownianVectorIntegralTimeSource BrownianVectorIntegralContinuousVersion BrownianVectorIntegralTimeEnergy
open BrownianVectorIntegralGridL1 BrownianVectorIntegralEnergyL1 BrownianVectorPartitionQV BrownianVectorCrossPartitionQV
open BrownianVectorFiniteStateCrossQV BrownianVectorPredictableMultiplier BrownianVectorPastMultiplierBinding
open BrownianVectorLeftMultiplierBinding FiniteClockLeftApproximation BrownianQuadraticVariation
open BrownianTimeIntegrand (timeLaw)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Same actual caller clocks, actual varying original inputs. L2 input
convergence is consumed through the proved grid-uniform L1 bound. -/
theorem partition_QV_of_input_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (g : ℕ → fullPredictableL2 d T) (f : fullPredictableL2 d T) (hg : Tendsto g atTop (𝓝 f)) :
    Tendsto (fun m => gridSquares d T (τ m) (g m)) atTop (𝓝 (energyClass d T T f)) := by
  have hB : Tendsto (fun m => ‖g m-f‖*(‖g m‖+‖f‖)) atTop (𝓝 0) := by
    have hd : Tendsto (fun m => ‖g m-f‖) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero] using (hg.sub (tendsto_const_nhds (x := f))).norm
    simpa only [zero_mul] using hd.mul (hg.norm.add (tendsto_const_nhds (x := ‖f‖)))
  have hE : Tendsto (fun m => gridSquares d T (τ m) (g m)-gridSquares d T (τ m) f) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun m => gridSquares_sub_norm_le d T (τ m) (hmono m) (hzero m) (hend m) (g m) f) hB
  simpa only [sub_add_cancel,zero_add] using hE.add (fullInput_partition_QV d T N τ hmono hzero hend hmesh f)

/-- Actual varying-input cross variation in original L1 scale; this feeds
sampled coefficient products without any new source/QV assumption. -/
theorem partition_crossVariation_of_input_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (f : fullPredictableL2 d T) (g : ℕ → fullPredictableL2 d T) (h : fullPredictableL2 d T)
    (hg : Tendsto g atTop (𝓝 h)) :
    Tendsto (fun m => gridCross d T (τ m) f (g m)) atTop (𝓝 (crossEnergyClass d T T f h)) := by
  simp_rw [gridCross_polarization,crossEnergyClass_polarization]
  exact ((partition_QV_of_input_tendsto d T N τ hmono hzero hend hmesh (fun m => f+g m) (f+h)
    ((tendsto_const_nhds (x := f)).add hg)).sub
    (partition_QV_of_input_tendsto d T N τ hmono hzero hend hmesh (fun m => f-g m) (f-h)
      ((tendsto_const_nhds (x := f)).sub hg))).const_smul (1/4 : ℝ)

private theorem row_memLp (H : ℝ≥0→Sample d→ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hb : ∀ u ω,‖H u ω‖≤K) (s : ℝ≥0) : MemLp (H s) ∞ (productLaw d) :=
  memLp_top_of_bound ((hp s).mono ((jointNaturalFiltration d).le s)).aestronglyMeasurable K
    (ae_of_all _ (hb s))

/-- A unit window on the actual sampled input is the ORIGINAL row window
on g. The active-cell equality is used only where that cell is nonempty. -/
private theorem window_sampled_cell (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (H : ℝ≥0→Sample d→ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (g : fullPredictableL2 d T) (i : Fin n) :
    windowMultiplier d T (τ i.castSucc) (τ i.succ) (fun _=>1) stronglyMeasurable_const (memLp_top_const 1)
      (sampledMultiplier d T τ hm H hp K hK hb g) =
    windowMultiplier d T (τ i.castSucc) (τ i.succ) (H (τ i.castSucc)) (hp _)
      (row_memLp d H hp K hb _) g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [windowMultiplier_coe d T _ _ (fun _=>1) stronglyMeasurable_const (memLp_top_const 1)
      (sampledMultiplier d T τ hm H hp K hK hb g),
    sampledMultiplier_coe d T τ hm H hp K hK hb g,
    windowMultiplier_coe d T _ _ (H (τ i.castSucc)) (hp _) (row_memLp d H hp K hb _) g]
      with p hw hs hr
  rw [hw,hs,hr]
  by_cases ht : p.1∈Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)
  · rw [leftCoefficient_eq_leftSample,leftSample_eq_cell τ hm _ p.1 i ht]
    simp only [scalarBlock,Set.indicator_of_mem ht,one_smul]
  · simp only [scalarBlock,Set.indicator_of_notMem ht,zero_smul]

/-- Actual increments of the constructed sampled input are the literal
START coefficient times SAME original M_g increments, not another process. -/
theorem sampledProcess_cell_increment (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (H : ℝ≥0→Sample d→ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (g : fullPredictableL2 d T) (i : Fin n) :
    (fun ω=>continuousIntegralProcess d T (sampledMultiplier d T τ hm H hp K hK hb g) (τ i.succ) ω-
      continuousIntegralProcess d T (sampledMultiplier d T τ hm H hp K hK hb g) (τ i.castSucc) ω) =ᵐ[productLaw d]
      fun ω=>H (τ i.castSucc) ω*(continuousIntegralProcess d T g (τ i.succ) ω-continuousIntegralProcess d T g (τ i.castSucc) ω) := by
  have hst := hm (show i.castSucc ≤ i.succ by exact_mod_cast Nat.le_succ (i : ℕ))
  have h1 := windowMultiplier_integral_coe d T _ _ hst (fun _=>1) stronglyMeasurable_const (memLp_top_const 1)
    (sampledMultiplier d T τ hm H hp K hK hb g)
  rw [window_sampled_cell] at h1
  simp only [one_mul] at h1
  exact h1.symm.trans (windowMultiplier_integral_coe d T _ _ hst (H (τ i.castSucc)) (hp _) (row_memLp d H hp K hb _) g)

/-- Literal weighted cross increments of the two supplied original outputs. -/
def weightedCrossSum (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0)
    (H : ℝ≥0→Sample d→ℝ) (f g : fullPredictableL2 d T) (ω : Sample d) : ℝ :=
  ∑ i : Fin n,H (τ i.castSucc) ω*
    (continuousIntegralProcess d T f (τ i.succ) ω-continuousIntegralProcess d T f (τ i.castSucc) ω)*
    (continuousIntegralProcess d T g (τ i.succ) ω-continuousIntegralProcess d T g (τ i.castSucc) ω)

theorem gridCross_sampled_coe (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (H : ℝ≥0→Sample d→ℝ) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f g : fullPredictableL2 d T) :
    gridCross d T τ f (sampledMultiplier d T τ hm H hp K hK hb g) =ᵐ[productLaw d]
      weightedCrossSum d T τ H f g := by
  have hi : ∀ᵐ ω ∂productLaw d,∀ i : Fin n,
      continuousIntegralProcess d T (sampledMultiplier d T τ hm H hp K hK hb g) (τ i.succ) ω-
      continuousIntegralProcess d T (sampledMultiplier d T τ hm H hp K hK hb g) (τ i.castSucc) ω =
      H (τ i.castSucc) ω*(continuousIntegralProcess d T g (τ i.succ) ω-continuousIntegralProcess d T g (τ i.castSucc) ω) :=
    ae_all_iff.mpr (fun i=>sampledProcess_cell_increment d T τ hm H hp K hK hb g i)
  filter_upwards [gridCross_coe d T τ f (sampledMultiplier d T τ hm H hp K hK hb g),hi] with ω hc hi
  rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  ring

/-- Actual original-time bilinear energy with real source weight H. -/
def weightedTimeIntegrand (T : ℝ≥0) (H : ℝ≥0→Sample d→ℝ) (f g : fullPredictableL2 d T)
    (p : ℝ×Sample d) : ℝ :=
  H (Real.toNNReal p.1) p.2 * inner ℝ (representative d T f p) (representative d T g p)

theorem weightedTimeIntegrand_integrable (T : ℝ≥0) (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (K : ℝ) (hb : ∀ u ω,‖H u ω‖≤K)
    (f g : fullPredictableL2 d T) : Integrable (weightedTimeIntegrand d T H f g) (inputLaw d T) :=
  (memLp_top_of_bound
    (hj.comp ((measurable_fst.real_toNNReal).prodMk measurable_snd)).aestronglyMeasurable K
    (ae_of_all _ (fun _=>hb _ _))).integrable_mul
      (memLp_one_iff_integrable.mpr (representative_inner_integrable d T f g))

def weightedTimeEnergy (T : ℝ≥0) (H : ℝ≥0→Sample d→ℝ) (f g : fullPredictableL2 d T)
    (ω : Sample d) : ℝ := ∫ t,weightedTimeIntegrand d T H f g (t,ω) ∂timeLaw T

def weightedEnergyClass (T : ℝ≥0) (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (K : ℝ) (hb : ∀ u ω,‖H u ω‖≤K)
    (f g : fullPredictableL2 d T) : Lp ℝ 1 (productLaw d) :=
  ((weightedTimeIntegrand_integrable d T H hj K hb f g).integral_prod_right).toL1
    (weightedTimeEnergy d T H f g)

theorem weightedEnergyClass_coe (T : ℝ≥0) (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (K : ℝ) (hb : ∀ u ω,‖H u ω‖≤K)
    (f g : fullPredictableL2 d T) :
    weightedEnergyClass d T H hj K hb f g =ᵐ[productLaw d] weightedTimeEnergy d T H f g :=
  ((weightedTimeIntegrand_integrable d T H hj K hb f g).integral_prod_right).coeFn_toL1

/-- Original native inner/time marginal actually equals the original dt
weighted inner energy; no bracket or factorized target field is supplied. -/
theorem crossEnergyClass_multiplied_eq_weighted (T : ℝ≥0) (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω))
    (K : ℝ) (hb : ∀ u ω,‖H u ω‖≤K) (f g : fullPredictableL2 d T) :
    crossEnergyClass d T T f (continuousMultiplier d T H hj hp hc K hb g) =
      weightedEnergyClass d T H hj K hb f g := by
  let v := continuousMultiplier d T H hj hp hc K hb g
  have hi : innerClass (inputLaw d T) (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
      (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      weightedTimeIntegrand d T H f g := by
    filter_upwards [innerClass_coe (inputLaw d T) (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
      (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)),continuousMultiplier_coe d T H hj hp hc K hb g,
      representative_ae d T f,representative_ae d T g] with p hi hv hf hg
    rw [hi]
    change inner ℝ ((f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p)
      ((continuousMultiplier d T H hj hp hc K hb g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p) = _
    rw [hv,hf,hg,real_inner_smul_right]
    rfl
  have hs : ∀ᵐ ω ∂productLaw d,
      (fun t=>innerClass (inputLaw d T) (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
        (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (t,ω)) =ᵐ[timeLaw T]
      fun t=>weightedTimeIntegrand d T H f g (t,ω) :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := productLaw d) (ν := timeLaw T)).quasiMeasurePreserving.ae hi)
  apply Lp.ext
  unfold crossEnergyClass
  rw [truncate_horizon,truncate_horizon]
  filter_upwards [timeMarginal_coe d T (innerClass (inputLaw d T)
    (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))),
    weightedEnergyClass_coe d T H hj K hb f g,hs] with ω hm hw hs
  exact hm.trans ((integral_congr_ae hs).trans hw.symm)

variable (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
  (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
  (hmesh : Tendsto (fun n=>(mesh (τ n) : ℝ)) atTop (𝓝 0))
include hm h0 hT hmesh

/-- The weighted limit passes through actual sampled input convergence;
unweighted convergence is not substituted for this input argument. -/
theorem weightedCross_QV_class_tendsto (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω))
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f g : fullPredictableL2 d T) :
    Tendsto (fun n=>gridCross d T (τ n) f (sampledMultiplier d T (τ n) (hm n) H hp K hK hb g)) atTop
      (𝓝 (weightedEnergyClass d T H hj K hb f g)) := by
  rw [← crossEnergyClass_multiplied_eq_weighted d T H hj hp hc K hb f g]
  exact partition_crossVariation_of_input_tendsto d T N τ hm h0 hT hmesh f _ _
    (sampledMultiplier_tendsto d T N τ hm h0 hT hmesh H hj hp hc K hK hb g)

/-- EXACT actual H_START weighted cross increments of the two SAME supplied
continuous outputs converge to their SAME-source actual dt weighted inner. -/
theorem weightedCross_QV_tendstoInMeasure (H : ℝ≥0→Sample d→ℝ)
    (hj : Measurable (Function.uncurry H)) (hp : StronglyAdapted (jointNaturalFiltration d) H)
    (hc : ∀ᵐ ω ∂productLaw d,Continuous (fun u=>H u ω))
    (K : ℝ) (hK : 0≤K) (hb : ∀ u ω,‖H u ω‖≤K) (f g : fullPredictableL2 d T) :
    TendstoInMeasure (productLaw d) (fun n=>weightedCrossSum d T (τ n) H f g) atTop
      (weightedTimeEnergy d T H f g) :=
  TendstoInMeasure.congr (fun n=>gridCross_sampled_coe d T (τ n) (hm n) H hp K hK hb f g)
    (weightedEnergyClass_coe d T H hj K hb f g)
    (tendstoInMeasure_of_tendsto_Lp (weightedCross_QV_class_tendsto d T N τ hm h0 hT hmesh H hj hp hc K hK hb f g))

/-- Genuine state-dependent Hessian-entry-style consumer, computed on the
SAME original finite state at each START, without approximate state replacement. -/
theorem functionOfState_weightedCross_QV_tendstoInMeasure {m : ℕ}
    (family : Fin m→fullPredictableL2 d T) (F : EuclideanSpace ℝ (Fin m)→ℝ) (hF : Continuous F)
    (K : ℝ) (hb : ∀ x,‖F x‖≤K) (f g : fullPredictableL2 d T) :
    TendstoInMeasure (productLaw d)
      (fun n=>weightedCrossSum d T (τ n) (fun u ω=>F (stateProcess d T family u ω)) f g) atTop
      (weightedTimeEnergy d T (fun u ω=>F (stateProcess d T family u ω)) f g) :=
  weightedCross_QV_tendstoInMeasure d T N τ hm h0 hT hmesh (fun u ω=>F (stateProcess d T family u ω))
    (hF.measurable.comp (stateProcess_measurable d T family))
    (fun u=>hF.comp_stronglyMeasurable (stateProcess_stronglyAdapted d T family u))
    ((stateProcess_continuous d T family).mono (fun _ h=>hF.comp h))
    K ((norm_nonneg (F 0)).trans (hb 0)) (fun _ _=>hb _) f g

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorWeightedCrossQV
