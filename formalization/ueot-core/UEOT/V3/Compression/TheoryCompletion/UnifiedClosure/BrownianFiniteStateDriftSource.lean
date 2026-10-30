import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateItoSource

/-!
Original commitment: actual state Itô must include the physical initial state and genuine finite-variation drift with the original noise.
Existing result: original joint-source finite integral state and actual weighted/Taylor/Itô identities for its pure martingale part.
Premise reduced: construct the actual ordinary time integral of a bounded original joint-predictable drift, deriving its permissions/continuity/increment bounds.
Model/witness: SAME productLaw d/joint Fs, state dimension m independent of d, given bounded predictable beta, deterministic x0 and original supplied inputs.
Consumer: Y=x0+actual dt beta+original M, for actual drift Riemann and FV/noise cross estimates; no implicit SDE existence is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorPredictableInputs
open BrownianVectorIntegralTimeSource BrownianVectorIntegralContinuousVersion BrownianVectorFiniteStateCrossQV
open BrownianTimeIntegrand (timeLaw)
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ) {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

private theorem real_embedding_predictable :
    @Measurable (ℝ≥0×Sample d) (ℝ×Sample d) (jointNaturalFiltration d).predictable (predictableSigma d)
      (fun p=>((p.1 : ℝ),p.2)) := by
  apply measurable_iff_comap_le.mpr
  change MeasurableSpace.comap (fun p : ℝ≥0×Sample d=>((p.1 : ℝ),p.2))
    (MeasurableSpace.comap (timeReadout d) (jointNaturalFiltration d).predictable)≤_
  rw [MeasurableSpace.comap_comp]
  have he : timeReadout d ∘ (fun p : ℝ≥0×Sample d=>((p.1 : ℝ),p.2))=id := by
    ext p <;> simp [timeReadout]
  rw [he,MeasurableSpace.comap_id]

/-- Input is an ordinary genuine predictable function, not a field asserting
any Ito or SDE conclusion. Jumps in its time paths are permitted. -/
theorem beta_native_predictable (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β) :
    IsStronglyPredictable (jointNaturalFiltration d) (fun u ω=>β ((u : ℝ),ω)) :=
  hp.comp_measurable (real_embedding_predictable d)

def driftIntegrand (T u : ℝ≥0) (β : ℝ×Sample d→E) : ℝ×Sample d→E := (timeSet d T u).indicator β

def drift (T : ℝ≥0) (β : ℝ×Sample d→E) (u : ℝ≥0) (ω : Sample d) : E :=
  ∫ t,driftIntegrand d T u β (t,ω) ∂timeLaw T

theorem driftIntegrand_past (T u : ℝ≥0) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β) :
    StronglyMeasurable[MeasurableSpace.prod inferInstance (jointNaturalFiltration d u)] (driftIntegrand d T u β) := by
  let : MeasurableSpace (Sample d) := jointNaturalFiltration d u
  let c (t : ℝ) : Iic u := ⟨min (Real.toNNReal t) (min u T),
    (min_le_right (Real.toNNReal t) (min u T)).trans (min_le_left u T)⟩
  have hc : Measurable c := (measurable_id.real_toNNReal.min measurable_const).subtype_mk
  have hm : StronglyMeasurable (fun p : ℝ×Sample d=>β (((c p.1 : ℝ≥0) : ℝ),p.2)) :=
    ((beta_native_predictable d β hp).isStronglyProgressive u).comp_measurable
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have ht : MeasurableSet (timeSet d T u) := measurableSet_Ioc.prod MeasurableSet.univ
  have he : driftIntegrand d T u β=(timeSet d T u).indicator
      (fun p : ℝ×Sample d=>β (((c p.1 : ℝ≥0) : ℝ),p.2)) := by
    ext p
    by_cases h : p∈timeSet d T u
    · rw [driftIntegrand,Set.indicator_of_mem h,Set.indicator_of_mem h]
      have hn : Real.toNNReal p.1≤min u T := Real.toNNReal_le_iff_le_coe.mpr h.1.2
      have hx : ((c p.1 : ℝ≥0) : ℝ)=p.1 := by
        change ((min (Real.toNNReal p.1) (min u T) : ℝ≥0) : ℝ)=p.1
        rw [min_eq_left hn,Real.coe_toNNReal _ h.1.1.le]
      rw [hx]
    · simp only [driftIntegrand,Set.indicator_of_notMem h]
  rw [he]
  exact hm.indicator ht

theorem drift_stronglyAdapted (T : ℝ≥0) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β) :
    StronglyAdapted (jointNaturalFiltration d) (drift d T β) := by
  intro u
  let : MeasurableSpace (Sample d) := jointNaturalFiltration d u
  exact (driftIntegrand_past d T u β hp).integral_prod_left'

theorem beta_intervalIntegrable (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (ω : Sample d) (a b : ℝ) :
    IntervalIntegrable (fun t=>β (t,ω)) volume a b := by
  have hm : StronglyMeasurable (fun t=>β (t,ω)) :=
    (hp.mono (predictableSigma_le d)).comp_measurable (measurable_id.prodMk measurable_const)
  let _ : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min a b) (max a b)))
    infer_instance
  have hi : MemLp (fun t=>β (t,ω)) ∞ (volume.restrict (uIoc a b)) :=
    MemLp.of_bound hm.aestronglyMeasurable (B : ℝ) (ae_of_all _ (fun t=>hb (t,ω)))
  rw [intervalIntegrable_iff]
  exact hi.integrable (by norm_num)

/-- Literal ordinary Lebesgue primitive on the original time support. -/
theorem drift_primitive (T u : ℝ≥0) (β : ℝ×Sample d→E) (ω : Sample d) :
    drift d T β u ω=∫ t in (0 : ℝ)..(min u T : ℝ≥0),β (t,ω) := by
  have he : (fun t=>driftIntegrand d T u β (t,ω))=
      (Ioc (0 : ℝ) (min u T : ℝ≥0)).indicator (fun t=>β (t,ω)) := by
    ext t
    have ht : (t,ω)∈timeSet d T u ↔ t∈Ioc (0 : ℝ) (min u T : ℝ≥0) := by
      simp only [timeSet,mem_prod,mem_univ,and_true]
    by_cases h : t∈Ioc (0 : ℝ) (min u T : ℝ≥0)
    · rw [driftIntegrand,Set.indicator_of_mem (ht.mpr h),Set.indicator_of_mem h]
    · rw [driftIntegrand,Set.indicator_of_notMem (fun h'=>h (ht.mp h')),Set.indicator_of_notMem h]
  have hsub : Ioc (0 : ℝ) (min u T : ℝ≥0)⊆Icc (0 : ℝ) (T : ℝ) := by
    intro t ht
    exact ⟨ht.1.le,ht.2.trans (by exact_mod_cast min_le_right u T)⟩
  rw [drift,he,timeLaw,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hsub,← intervalIntegral.integral_of_le (min u T).coe_nonneg]

theorem drift_continuous (T : ℝ≥0) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (ω : Sample d) : Continuous (fun u=>drift d T β u ω) := by
  simp_rw [drift_primitive]
  exact (intervalIntegral.continuous_primitive (beta_intervalIntegrable d β hp B hb ω) 0).comp
    (continuous_subtype_val.comp (continuous_id.min continuous_const))

theorem drift_measurable (T : ℝ≥0) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) : Measurable (Function.uncurry (drift d T β)) :=
  (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (drift_continuous d T β hp B hb)
    (fun u=>(drift_stronglyAdapted d T β hp u).mono ((jointNaturalFiltration d).le u))).measurable

theorem drift_zero (T : ℝ≥0) (β : ℝ×Sample d→E) : drift d T β 0=0 := by
  ext ω
  rw [drift_primitive]
  simp

/-- Actual drift increments, at the natural finite-variation scale. -/
theorem drift_increment (T a b : ℝ≥0) (hab : a≤b) (hbT : b≤T)
    (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (ω : Sample d) :
    drift d T β b ω-drift d T β a ω=∫ t in (a : ℝ)..(b : ℝ),β (t,ω) := by
  rw [drift_primitive,drift_primitive,min_eq_left hbT,min_eq_left (hab.trans hbT)]
  exact intervalIntegral.integral_interval_sub_left (beta_intervalIntegrable d β hp B hb ω 0 b)
    (beta_intervalIntegrable d β hp B hb ω 0 a)

theorem drift_increment_norm_le (T a b : ℝ≥0) (hab : a≤b) (hbT : b≤T)
    (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (ω : Sample d) :
    ‖drift d T β b ω-drift d T β a ω‖≤(B : ℝ)*((b : ℝ)-(a : ℝ)) := by
  rw [drift_increment d T a b hab hbT β hp B hb]
  have habR : (a : ℝ)≤(b : ℝ) := by exact_mod_cast hab
  simpa only [abs_of_nonneg (sub_nonneg.mpr habR)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := (a : ℝ)) (b := (b : ℝ)) (C := (B : ℝ))
      (fun t _=>hb (t,ω)))

private theorem sum_clock_gaps {n : ℕ} (τ : Fin (n+1)→ℝ≥0) :
    (∑ i : Fin n,((τ i.succ : ℝ)-(τ i.castSucc : ℝ)))=(τ (Fin.last n) : ℝ)-(τ 0 : ℝ) := by
  rw [Finset.sum_sub_distrib]
  have h0:=Fin.sum_univ_succ (fun i=>(τ i : ℝ))
  have hn:=Fin.sum_univ_castSucc (fun i=>(τ i : ℝ))
  linarith

/-- Genuine finite variation bound for ALL caller clocks on the horizon. -/
theorem drift_grid_variation_le (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (h0 : τ 0=0) (hT : τ (Fin.last n)=T) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (ω : Sample d) :
    (∑ i : Fin n,‖drift d T β (τ i.succ) ω-drift d T β (τ i.castSucc) ω‖)≤(B : ℝ)*(T : ℝ) := by
  calc
    _ ≤ ∑ i : Fin n,(B : ℝ)*((τ i.succ : ℝ)-(τ i.castSucc : ℝ)) :=
      Finset.sum_le_sum (fun i _=>drift_increment_norm_le d T _ _
        (hm (by exact_mod_cast Nat.le_succ (i : ℕ))) ((hm (Fin.le_last _)).trans hT.le) β hp B hb ω)
    _ = _ := by rw [← Finset.mul_sum,sum_clock_gaps,h0,hT,NNReal.coe_zero,sub_zero]

def driftSquareSum (T : ℝ≥0) (β : ℝ×Sample d→E) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (ω : Sample d) : ℝ :=
  ∑ i : Fin n,‖drift d T β (τ i.succ) ω-drift d T β (τ i.castSucc) ω‖^2

/-- Actual finite-variation quadratic sums have a uniform computed-mesh
bound, including repeated/empty cells; no stochastic fourth moment. -/
theorem driftSquareSum_mesh_bound (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ)
    (h0 : τ 0=0) (hT : τ (Fin.last n)=T) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (ω : Sample d) :
    driftSquareSum d T β τ ω≤(B : ℝ)^2*(BrownianQuadraticVariation.mesh τ : ℝ)*(T : ℝ) := by
  have hi (i : Fin n) : ‖drift d T β (τ i.succ) ω-drift d T β (τ i.castSucc) ω‖^2≤
      (B : ℝ)^2*(BrownianQuadraticVariation.mesh τ : ℝ)*((τ i.succ : ℝ)-(τ i.castSucc : ℝ)) := by
    have ho : τ i.castSucc≤τ i.succ := hm (by exact_mod_cast Nat.le_succ (i : ℕ))
    have hr : (τ i.castSucc : ℝ)≤(τ i.succ : ℝ) := by exact_mod_cast ho
    have hg : 0≤(τ i.succ : ℝ)-(τ i.castSucc : ℝ) := sub_nonneg.mpr hr
    have hd := drift_increment_norm_le d T _ _ ho ((hm (Fin.le_last _)).trans hT.le) β hp B hb ω
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg B.coe_nonneg hg)).mpr hd
    have hm' := BrownianScalarTaylorRemainder.clockIncrement_dist_le_mesh τ hm i
    rw [NNReal.dist_eq,abs_of_nonneg hg] at hm'
    have hp' := mul_le_mul_of_nonneg_right hm' hg
    calc
      _ ≤ (B : ℝ)^2*((τ i.succ : ℝ)-(τ i.castSucc : ℝ))^2 := by simpa only [mul_pow] using hs
      _ ≤ (B : ℝ)^2*((BrownianQuadraticVariation.mesh τ : ℝ)*((τ i.succ : ℝ)-(τ i.castSucc : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith
      _ = _ := by ring
  calc
    _ ≤ ∑ i : Fin n,(B : ℝ)^2*(BrownianQuadraticVariation.mesh τ : ℝ)*((τ i.succ : ℝ)-(τ i.castSucc : ℝ)) :=
      Finset.sum_le_sum (fun i _=>hi i)
    _ = _ := by rw [← Finset.mul_sum,sum_clock_gaps,h0,hT,NNReal.coe_zero,sub_zero]

theorem driftSquareSum_tendsto (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (ω : Sample d) :
    Tendsto (fun n=>driftSquareSum d T β (τ n) ω) atTop (𝓝 0) :=
  squeeze_zero (fun n=>Finset.sum_nonneg (fun _ _=>sq_nonneg _))
    (fun n=>driftSquareSum_mesh_bound d T (τ n) (hm n) (h0 n) (hT n) β hp B hb ω)
    (by simpa only [mul_zero,zero_mul] using (hmesh.const_mul ((B : ℝ)^2)).mul_const (T : ℝ))

/-- Explicit physical state from the declared drift input, initial x0 and
original actual integral state; this is not an implicit SDE solution field. -/
def state (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E) (family : Fin m→fullPredictableL2 d T)
    (u : ℝ≥0) (ω : Sample d) : E := x0+drift d T β u ω+stateProcess d T family u ω

theorem state_stronglyAdapted (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E)
    (hp : StronglyMeasurable[predictableSigma d] β) (family : Fin m→fullPredictableL2 d T) :
    StronglyAdapted (jointNaturalFiltration d) (state d T x0 β family) :=
  fun u=>(stronglyMeasurable_const.add (drift_stronglyAdapted d T β hp u)).add (stateProcess_stronglyAdapted d T family u)

theorem state_continuous (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (family : Fin m→fullPredictableL2 d T) :
    ∀ᵐ ω ∂productLaw d,Continuous (fun u=>state d T x0 β family u ω) :=
  (stateProcess_continuous d T family).mono (fun ω hc=>(continuous_const.add (drift_continuous d T β hp B hb ω)).add hc)

theorem state_measurable (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E) (hp : StronglyMeasurable[predictableSigma d] β)
    (B : ℝ≥0) (hb : ∀ p,‖β p‖≤B) (family : Fin m→fullPredictableL2 d T) :
    Measurable (Function.uncurry (state d T x0 β family)) :=
  (measurable_const.add (drift_measurable d T β hp B hb)).add (stateProcess_measurable d T family)

theorem state_initial (T : ℝ≥0) (x0 : E) (β : ℝ×Sample d→E) (family : Fin m→fullPredictableL2 d T) :
    state d T x0 β family 0=ᵐ[productLaw d] fun _=>x0 := by
  have hi : ∀ᵐ ω ∂productLaw d,∀ j,continuousIntegralProcess d T (family j) 0 ω=0 :=
    ae_all_iff.mpr (fun j=>continuousIntegralProcess_zero d T (family j))
  filter_upwards [hi] with ω hi
  have hm : stateProcess d T family 0 ω=0 := by ext j; exact hi j
  simp only [state,drift_zero,Pi.zero_apply,add_zero,hm]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftSource
