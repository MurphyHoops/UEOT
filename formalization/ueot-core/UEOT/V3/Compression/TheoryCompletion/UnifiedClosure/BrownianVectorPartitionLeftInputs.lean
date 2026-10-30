import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorFiniteSpanLeftInputs

/-!
Original commitment: fixed-input vector-noise QV requires actual same-source START samples converging to the ORIGINAL input.
Existing result: exact original span input has a current-joint-past, Ioc-left, globally bounded trace derived from source-AE coefficients.
Premise reduced: construct real permitted sample records on caller clocks and prove their native Euclidean L2 input convergence.
Model: original productLaw/inputLaw/jointNaturalFiltration, deterministic mono0/T computedmesh→0, d0/T0/repeats; no future coefficient reads.
Consumer: fixed original finite-span QV then original full predictable density; no desired approximation/QV law field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPartitionLeftInputs
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralFinitePaths
open BrownianVectorFiniteSpanLeftInputs FiniteClockLeftApproximation
open BrownianQuadraticVariation (mesh)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Actual finite program reads each coefficient at its ORIGINAL row START. -/
def sampleRecord (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0=0) (hend : τ (Fin.last n)=T) (H : ℝ≥0→Fin d→Sample d→ℝ)
    (hadapt : ∀ k,StronglyAdapted (jointNaturalFiltration d) (fun u ω=>H u k ω))
    (K : ℝ) (hbound : ∀ u k ω,‖H u k ω‖≤K) : ElementaryInput d T where
  n:=n
  clock:=τ
  coefficient:=fun i=>H (τ i.castSucc)
  clock_mono:=hmono
  clock_zero:=hzero
  clock_end:=hend
  coefficient_past:=fun _i k=>hadapt k _
  coefficient_bounded:=fun _i k=>MemLp.of_bound
    ((hadapt k _).mono ((jointNaturalFiltration d).le _)).aestronglyMeasurable K
      (Eventually.of_forall (hbound _ k))

/-- Honest Euclidean bound from coordinate bounds; no sup norm is renamed. -/
theorem coefficient_norm_bound (H : Fin d→Sample d→ℝ) (ω : Sample d) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ k,‖H k ω‖≤K) : ‖coefficient d H ω‖≤((d : ℝ)+1)*K := by
  have hs : ‖coefficient d H ω‖^2≤(d : ℝ)*K^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _k : Fin d,K^2 := Finset.sum_le_sum (fun k _=>by
        simpa only [coefficient_apply,Real.norm_eq_abs,sq_abs] using
          (sq_le_sq₀ (norm_nonneg _) hK).mpr (hbound k))
      _ = _ := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hK)).mp
  have hd : (d : ℝ)≤((d : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hm:=mul_le_mul_of_nonneg_right hd (sq_nonneg K)
  nlinarith

/-- Sample record integrand is EXACT pure-clock Euclidean leftSample of SAME
source coefficient values; stochastic permissions stay in sampleRecord fields. -/
theorem sample_integrand_eq_leftSample (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0=0) (hend : τ (Fin.last n)=T) (H : ℝ≥0→Fin d→Sample d→ℝ)
    (hadapt : ∀ k,StronglyAdapted (jointNaturalFiltration d) (fun u ω=>H u k ω))
    (K : ℝ) (hbound : ∀ u k ω,‖H u k ω‖≤K) (p : ℝ×Sample d) :
    integrand d (sampleRecord d T τ hmono hzero hend H hadapt K hbound).clock
      (sampleRecord d T τ hmono hzero hend H hadapt K hbound).coefficient p=
        leftSample τ (fun u=>coefficient d (H u) p.2) p.1 := by
  apply Finset.sum_congr rfl
  intro i _
  change (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator (fun _=>(1 : ℝ)) p.1 •
    coefficient d (H (τ i.castSucc)) p.2=
      (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator (fun _=>coefficient d (H (τ i.castSucc)) p.2) p.1
  by_cases hp : p.1∈Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp,one_smul]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,zero_smul]

private theorem leftSample_norm_bound {E : Type*} [SeminormedAddCommGroup E] {n : ℕ}
    (τ : Fin (n+1)→ℝ≥0) (hmono : Monotone τ) (F : ℝ≥0→E) (C : ℝ) (hC : 0≤C)
    (hF : ∀ u,‖F u‖≤C) (x : ℝ) : ‖leftSample τ F x‖≤C := by
  classical
  by_cases he : ∃ i : Fin n,x∈Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)
  · obtain ⟨i,hi⟩:=he
    rw [leftSample_eq_cell τ hmono F x i hi]
    exact hF _
  · have hz : leftSample τ F x=0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact Set.indicator_of_notMem (fun h=>he ⟨i,h⟩) _
    rw [hz,norm_zero]
    exact hC

theorem inputFunction_measurable (H : ℝ≥0→Fin d→Sample d→ℝ)
    (hjoint : ∀ k,Measurable (Function.uncurry (fun u ω=>H u k ω))) :
    Measurable (inputFunction d H) := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp
  apply measurable_pi_lambda
  intro k
  exact (hjoint k).comp ((measurable_fst.real_toNNReal).prodMk measurable_snd)

theorem inputFunction_memLp_two (T : ℝ≥0) (H : ℝ≥0→Fin d→Sample d→ℝ)
    (hjoint : ∀ k,Measurable (Function.uncurry (fun u ω=>H u k ω)))
    (K : ℝ) (hK : 0≤K) (hbound : ∀ u k ω,‖H u k ω‖≤K) :
    MemLp (inputFunction d H) 2 (inputLaw d T) := by
  apply MemLp.of_bound (inputFunction_measurable d H hjoint).aestronglyMeasurable (((d : ℝ)+1)*K)
  exact Eventually.of_forall (fun p=>coefficient_norm_bound d _ _ K hK (fun k=>hbound _ k _))

section Clock
variable (T : ℝ≥0) (N : ℕ→ℕ) (τ : (m : ℕ)→Fin (N m+1)→ℝ≥0)
  (hmono : ∀ m,Monotone (τ m)) (hzero : ∀ m,τ m 0=0) (hend : ∀ m,τ m (Fin.last (N m))=T)
  (hmesh : Tendsto (fun m=>(mesh (τ m) : ℝ)) atTop (𝓝 0))
include hmono hzero hend hmesh

/-- Actual same-source left samples converge on the original time/product
law; only the original one full-event left regularity and time support enter. -/
theorem partition_integrands_tendsto_ae (H : ℝ≥0→Fin d→Sample d→ℝ)
    (hadapt : ∀ k,StronglyAdapted (jointNaturalFiltration d) (fun u ω=>H u k ω))
    (hleft : ∀ᵐ ω ∂productLaw d,∀ u k,ContinuousWithinAt (fun v=>H v k ω) (Iic u) u)
    (K : ℝ) (hbound : ∀ u k ω,‖H u k ω‖≤K) :
    ∀ᵐ p ∂inputLaw d T,Tendsto (fun m=>integrand d
      (sampleRecord d T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hbound).clock
      (sampleRecord d T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hbound).coefficient p)
        atTop (𝓝 (inputFunction d H p)) := by
  have hc : ∀ᵐ p ∂inputLaw d T,∀ u k,ContinuousWithinAt (fun v=>H v k p.2) (Iic u) u :=
    Measure.quasiMeasurePreserving_snd.ae hleft
  filter_upwards [time_support_ae d T,hc] with p hp hc
  have hl : ContinuousWithinAt (fun v=>coefficient d (H v) p.2)
      (Iic (Real.toNNReal p.1)) (Real.toNNReal p.1) :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_pi.mpr (fun k=>hc _ k))
  have h := leftSample_tendsto T N τ hmono hzero hend hmesh
    (fun u=>coefficient d (H u) p.2) p.1 hp.1 hp.2 hl
  exact (tendsto_congr' (Eventually.of_forall (fun m=>sample_integrand_eq_leftSample d T
    (τ m) (hmono m) (hzero m) (hend m) H hadapt K hbound p))).mpr h

/-- Native L2 convergence is to the declared ORIGINAL class g, whose literal
readout equality must actually be proved by the caller, not assumed sufficiency. -/
theorem partition_inputValue_tendsto (H : ℝ≥0→Fin d→Sample d→ℝ)
    (hadapt : ∀ k,StronglyAdapted (jointNaturalFiltration d) (fun u ω=>H u k ω))
    (hleft : ∀ᵐ ω ∂productLaw d,∀ u k,ContinuousWithinAt (fun v=>H v k ω) (Iic u) u)
    (K : ℝ) (hK : 0≤K) (hbound : ∀ u k ω,‖H u k ω‖≤K)
    (g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (hg : g=ᵐ[inputLaw d T] inputFunction d H) :
    Tendsto (fun m=>inputValue (sampleRecord d T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hbound))
      atTop (𝓝 g) := by
  let r (m : ℕ):=sampleRecord d T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hbound
  let F (m : ℕ):=integrand d (r m).clock (r m).coefficient
  let C:=((d : ℝ)+1)*K
  have hC : 0≤C := mul_nonneg (by positivity) hK
  have hF (m : ℕ) (p : ℝ×Sample d) : ‖F m p‖≤C := by
    rw [show F m p=leftSample (τ m) (fun u=>coefficient d (H u) p.2) p.1 from
      sample_integrand_eq_leftSample d T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hbound p]
    exact leftSample_norm_bound (τ m) (hmono m) _ C hC
      (fun u=>coefficient_norm_bound d (H u) p.2 K hK (fun k=>hbound u k p.2)) p.1
  have hm (m : ℕ) : AEStronglyMeasurable (fun p=>‖F m p-g p‖^2) (inputLaw d T) :=
    (((integrand_memLp_two T (r m).clock (r m).coefficient (r m).coefficient_bounded).aestronglyMeasurable.sub
      (Lp.aestronglyMeasurable g)).norm.pow 2)
  have hb (m : ℕ) : ∀ᵐ p ∂inputLaw d T,‖‖F m p-g p‖^2‖≤(2*C)^2 := by
    filter_upwards [hg] with p hgp
    have hgn : ‖g p‖≤C := by
      rw [hgp]
      exact coefficient_norm_bound d _ _ K hK (fun k=>hbound _ k _)
    have hn : ‖F m p-g p‖≤2*C := (norm_sub_le _ _).trans (by linarith [hF m p])
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖F m p-g p‖)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*C)).mpr hn
  have hl : ∀ᵐ p ∂inputLaw d T,Tendsto (fun m=>‖F m p-g p‖^2) atTop (𝓝 0) := by
    filter_upwards [partition_integrands_tendsto_ae d T N τ hmono hzero hend hmesh H hadapt hleft K hbound,hg]
      with p hp hgp
    have h := ((hp.sub_const (g p)).norm).pow 2
    simpa only [← hgp,sub_self,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)] using h
  have hI : Tendsto (fun m=>∫ p,‖F m p-g p‖^2 ∂inputLaw d T) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : ℝ×Sample d=>(2*C)^2) hm
      (integrable_const _) hb hl
    simpa only [integral_zero] using h
  have he (m : ℕ) : ‖inputValue (r m)-g‖^2=∫ p,‖F m p-g p‖^2 ∂inputLaw d T := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (inputValue (r m)) g,
      (integrand_memLp_two T (r m).clock (r m).coefficient (r m).coefficient_bounded).coeFn_toLp] with p hs hr
    change inputValue (r m) p=F m p at hr
    simp only [Pi.sub_apply] at hs
    rw [hs,hr]
  have hs : Tendsto (fun m=>‖inputValue (r m)-g‖^2) atTop (𝓝 0) :=
    (tendsto_congr' (Eventually.of_forall he)).mpr hI
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hroot

/-- Required dense-original-input consumer: these permitted actual samples
converge to the SAME original spanInput in its genuine joint-predictable domain. -/
theorem finiteSpan_partition_input_tendsto (a : ElementaryInput d T→₀ℝ) :
    Tendsto (fun m=>literalPredictableInput d (sampleRecord d T (τ m) (hmono m) (hzero m) (hend m)
      (clippedTrace d T a) (clippedTrace_adapted d T a) (spanBound d T a) (clippedTrace_bound d T a)))
        atTop (𝓝 (spanInput d T a)) := by
  apply tendsto_subtype_rng.mpr
  exact partition_inputValue_tendsto d T N τ hmono hzero hend hmesh (clippedTrace d T a)
    (clippedTrace_adapted d T a) (Eventually.of_forall (fun ω u k=>clippedTrace_left d T a u k ω))
    (spanBound d T a) (spanBound_nonneg d T a) (clippedTrace_bound d T a) _
    (spanInput_coe_clippedTrace d T a)
end Clock

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPartitionLeftInputs
