import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralContinuousVersion

/-!
Original commitment: actual integral quadratic variation/Ito need literal past-left-sampled approximants of their actual source processes.
Existing result: actual uniformClock, full predictable L2 closure/isometry, and actual continuous source integral/time-energy.
Premise reduced: derive predictable input membership and same-source stochastic Riemann limits from bounded continuous adapted data.
Model/witness: SAME fixed inputLaw T/sourceLaw, original naturalFiltration; joint measurable H, ae continuous paths, uniform bound K.
Consumer: bounded integral QV and C2 Brownian chain rule; arbitrary full-L2 QV/general Ito/vector sources are NOT assumed complete.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousAdaptedInputs
open MeasureTheory ProbabilityTheory Set Filter
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianIntegralContinuousVersion
open BrownianPredictableInputs BrownianPredictableDensity BrownianSimplePredictableIntegral BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem exists_clock_cell {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (x : ℝ)
    (hx0 : (τ 0 : ℝ) < x) (hxT : x ≤ (τ (Fin.last n) : ℝ)) :
    ∃ i : Fin n, x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) := by
  classical
  let q : Fin (n+1) → Prop := fun j => x ≤ (τ j : ℝ)
  have hex : ∃ j, q j := ⟨Fin.last n,hxT⟩
  let j := Fin.find q hex
  have hpos : 0 < (j : ℕ) := by
    by_contra hn
    have hj : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have hq : q j := Fin.find_spec hex
    change x ≤ (τ j : ℝ) at hq
    rw [hj] at hq
    exact (not_le_of_gt hx0) hq
  let i : Fin n := ⟨(j : ℕ)-1,by have := j.is_lt; omega⟩
  have his : i.succ = j := Fin.ext (by simp only [i,Fin.val_succ]; omega)
  have hij : i.castSucc < j := by
    change (i : ℕ) < (j : ℕ)
    simp only [i]
    omega
  refine ⟨i,lt_of_not_ge (Fin.find_min hex hij),?_⟩
  rw [his]
  exact Fin.find_spec hex

private theorem integrand_eq_cell {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) (i : Fin n)
    (hi : p.1 ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) :
    integrand τ H p = H i p.2 := by
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

/-- The actual unaltered source process, read on the original real time axis. -/
def inputFunction (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  H (Real.toNNReal p.1) p.2

theorem inputFunction_measurable (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hjoint : Measurable (Function.uncurry H)) :
    Measurable (inputFunction H) :=
  hjoint.comp ((measurable_fst.real_toNNReal).prodMk measurable_snd)

theorem inputFunction_memLp_two (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (K : ℝ) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    MemLp (inputFunction H) 2 (inputLaw T) :=
  MemLp.of_bound (inputFunction_measurable H hjoint).aestronglyMeasurable K
    (Eventually.of_forall (fun p => hbound (Real.toNNReal p.1) p.2))

/-- Original deterministic uniform-clock record with coefficients sampled
ONLY at the original interval START; no integrator or output field is stored. -/
def leftRecord (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hadapt : StronglyAdapted naturalFiltration H)
    (K : ℝ) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) (n : ℕ) : ElementaryInput T where
  n := n+1
  clock := uniformClock T n
  coefficient := fun i => H (uniformClock T n i.castSucc)
  clock_mono := uniformClock_mono T n
  clock_zero := uniformClock_zero T n
  clock_end := uniformClock_end T n
  coefficient_past := fun i => hadapt (uniformClock T n i.castSucc)
  coefficient_bounded := fun i => memLp_top_of_bound
    ((hadapt (uniformClock T n i.castSucc)).mono (naturalFiltration.le _)).aestronglyMeasurable K
    (Eventually.of_forall (fun ω => hbound (uniformClock T n i.castSucc) ω))

/-- Each ACTUAL input step function converges on the ORIGINAL product source
support, using source path continuity and its computed same-clock mesh. -/
theorem left_integrands_tendsto_ae (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    ∀ᵐ p ∂inputLaw T, Tendsto (fun n => integrand (leftRecord T H hadapt K hbound n).clock
      (leftRecord T H hadapt K hbound n).coefficient p) atTop (𝓝 (inputFunction H p)) := by
  have hc : ∀ᵐ p ∂inputLaw T, Continuous (fun u => H u p.2) :=
    Measure.quasiMeasurePreserving_snd.ae hcont
  filter_upwards [time_support_ae T,hc] with p hp hc
  have he (n : ℕ) : ∃ i : Fin (n+1), p.1 ∈ Ioc (uniformClock T n i.castSucc : ℝ) (uniformClock T n i.succ : ℝ) := by
    apply exists_clock_cell
    · simpa only [uniformClock_zero,NNReal.coe_zero] using hp.1
    · simpa only [uniformClock_end] using hp.2
  choose i hi using he
  have happrox : Tendsto (fun n => uniformClock T n (i n).castSucc) atTop (𝓝 (Real.toNNReal p.1)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hp0 : 0 ≤ p.1 := hp.1.le
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => ?_) (uniformClock_mesh_tendsto T)
    have hgap : (uniformClock T n (i n).succ : ℝ)-(uniformClock T n (i n).castSucc : ℝ) ≤
        (mesh (uniformClock T n) : ℝ) := by
      have hm := Finset.le_sup (f := fun j : Fin (n+1) => uniformClock T n j.succ-uniformClock T n j.castSucc) (Finset.mem_univ (i n))
      have hco := NNReal.coe_le_coe.mpr hm
      rw [NNReal.coe_sub ((uniformClock_mono T n) (show (i n).castSucc ≤ (i n).succ by exact_mod_cast Nat.le_succ (i n : ℕ)))] at hco
      exact hco
    rw [NNReal.dist_eq,Real.coe_toNNReal _ hp0,abs_of_nonpos (sub_nonpos.mpr (hi n).1.le)]
    linarith [(hi n).2]
  have heq (n : ℕ) : integrand (leftRecord T H hadapt K hbound n).clock
      (leftRecord T H hadapt K hbound n).coefficient p = H (uniformClock T n (i n).castSucc) p.2 :=
    integrand_eq_cell _ (uniformClock_mono T n) _ p (i n) (hi n)
  exact (tendsto_congr' (Eventually.of_forall heq)).mpr ((hc.tendsto _).comp happrox)

theorem left_integrands_meanSquare_tendsto (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Tendsto (fun n => ∫ p, (integrand (leftRecord T H hadapt K hbound n).clock
      (leftRecord T H hadapt K hbound n).coefficient p-inputFunction H p)^2 ∂inputLaw T) atTop (𝓝 0) := by
  let F (n : ℕ) := integrand (leftRecord T H hadapt K hbound n).clock (leftRecord T H hadapt K hbound n).coefficient
  have hFm (n : ℕ) : MemLp (F n) 2 (inputLaw T) :=
    integrand_memLp_two T _ _ (leftRecord T H hadapt K hbound n).coefficient_bounded
  have hHm := inputFunction_memLp_two T H hjoint K hbound
  have hm (n : ℕ) : AEStronglyMeasurable (fun p => (F n p-inputFunction H p)^2) (inputLaw T) :=
    ((hFm n).aestronglyMeasurable.sub hHm.aestronglyMeasurable).pow 2
  have hb (n : ℕ) : ∀ᵐ p ∂inputLaw T, ‖(F n p-inputFunction H p)^2‖ ≤ (2*K)^2 := by
    filter_upwards [time_support_ae T] with p hp
    obtain ⟨i,hi⟩ : ∃ i : Fin (n+1), p.1 ∈ Ioc (uniformClock T n i.castSucc : ℝ) (uniformClock T n i.succ : ℝ) := by
      apply exists_clock_cell
      · simpa only [uniformClock_zero,NNReal.coe_zero] using hp.1
      · simpa only [uniformClock_end] using hp.2
    have he : F n p = H (uniformClock T n i.castSucc) p.2 :=
      integrand_eq_cell _ (uniformClock_mono T n) _ p i hi
    have hd : ‖F n p-inputFunction H p‖ ≤ 2*K := by
      rw [he]
      have hbTarget : ‖inputFunction H p‖ ≤ K := hbound (Real.toNNReal p.1) p.2
      exact (norm_sub_le _ _).trans (by linarith [hbound (uniformClock T n i.castSucc) p.2,hbTarget])
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
  have hl : ∀ᵐ p ∂inputLaw T, Tendsto (fun n => (F n p-inputFunction H p)^2) atTop (𝓝 0) := by
    filter_upwards [left_integrands_tendsto_ae T H hadapt hcont K hbound] with p hp
    have h : Tendsto (fun n => F n p-inputFunction H p) atTop (𝓝 0) := by
      simpa only [sub_self] using hp.sub (tendsto_const_nhds (x := inputFunction H p))
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using h.pow 2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence (fun _ => (2*K)^2)
    hm (integrable_const _) hb hl

/-- Original L2 class of the ACTUAL H source, before proving predictability. -/
def continuousInputClass (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (K : ℝ) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Lp ℝ 2 (inputLaw T) :=
  (inputFunction_memLp_two T H hjoint K hbound).toLp (inputFunction H)

theorem left_inputClass_tendsto (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Tendsto (fun n => inputValue (leftRecord T H hadapt K hbound n)) atTop
      (𝓝 (continuousInputClass T H hjoint K hbound)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (n : ℕ) : ‖inputValue (leftRecord T H hadapt K hbound n)-continuousInputClass T H hjoint K hbound‖^2 =
      ∫ p, (integrand (leftRecord T H hadapt K hbound n).clock
        (leftRecord T H hadapt K hbound n).coefficient p-inputFunction H p)^2 ∂inputLaw T := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (inputValue (leftRecord T H hadapt K hbound n)) (continuousInputClass T H hjoint K hbound),
      (integrand_memLp_two T _ _ (leftRecord T H hadapt K hbound n).coefficient_bounded).coeFn_toLp,
      (inputFunction_memLp_two T H hjoint K hbound).coeFn_toLp] with p hs hr hf
    simp only [Pi.sub_apply] at hs
    rw [hs]
    change (((integrand_memLp_two T _ _ (leftRecord T H hadapt K hbound n).coefficient_bounded).toLp
      (integrand (leftRecord T H hadapt K hbound n).clock (leftRecord T H hadapt K hbound n).coefficient)) p-
      ((inputFunction_memLp_two T H hjoint K hbound).toLp (inputFunction H)) p)^2 = _
    rw [hr,hf]
  have hs : Tendsto (fun n => ‖inputValue (leftRecord T H hadapt K hbound n)-continuousInputClass T H hjoint K hbound‖^2)
      atTop (𝓝 0) := (tendsto_congr' (Eventually.of_forall he)).mpr
    (left_integrands_meanSquare_tendsto T H hjoint hadapt hcont K hK hbound)
  have hr := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hr

/-- Genuine predictable membership is DERIVED by the original closed native
subspace and actual causal left-input convergence, never supplied as a field. -/
theorem continuousInputClass_predictable (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    continuousInputClass T H hjoint K hbound ∈ fullPredictableL2 T :=
  (fullPredictableL2_closed T).mem_of_tendsto (left_inputClass_tendsto T H hjoint hadapt hcont K hK hbound)
    (Eventually.of_forall (fun n => elementary_input_predictable (leftRecord T H hadapt K hbound n)))

/-- ACTUAL source H as genuine predictable L2 input, using the membership
just derived from actual left samples rather than a caller's certificate. -/
def continuousPredictableInput (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) : fullPredictableL2 T :=
  ⟨continuousInputClass T H hjoint K hbound,continuousInputClass_predictable T H hjoint hadapt hcont K hK hbound⟩

/-- Literal SAME-source stochastic Riemann sums with the original allowed
left coefficients converge in native source L2 to the ACTUAL full integral. -/
theorem left_outputs_tendsto (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Tendsto (fun n => outputValue (leftRecord T H hadapt K hbound n)) atTop
      (𝓝 (predictableIntegral T (continuousPredictableInput T H hjoint hadapt hcont K hK hbound))) := by
  have h : Tendsto (fun n => literalPredictableInput (leftRecord T H hadapt K hbound n)) atTop
      (𝓝 (continuousPredictableInput T H hjoint hadapt hcont K hK hbound)) :=
    tendsto_subtype_rng.mpr (left_inputClass_tendsto T H hjoint hadapt hcont K hK hbound)
  simpa only [Function.comp_def,predictableIntegral_returns_literal] using ((predictableIntegral T).continuous.tendsto _).comp h

/-- The actual derived predictable input is still the SAME original process
readout in the original product measure. -/
theorem continuousPredictableInput_coe (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    (continuousPredictableInput T H hjoint hadapt hcont K hK hbound : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      inputFunction H := (inputFunction_memLp_two T H hjoint K hbound).coeFn_toLp

/-- In particular the actual process READOUT is genuinely predictable a.e,
which the later bounded multiplier uses without an external input hypothesis. -/
theorem inputFunction_predictable (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    AEStronglyMeasurable[predictableSigma] (inputFunction H) (inputLaw T) :=
  (mem_lpMeas_iff_aestronglyMeasurable.mp
    (continuousPredictableInput T H hjoint hadapt hcont K hK hbound).property).congr
      (continuousPredictableInput_coe T H hjoint hadapt hcont K hK hbound)

/-- Concrete source class needed for the Ito first/second derivatives: EVERY
continuous bounded function of the SAME actual Brownian state is constructed
as a true predictable input, rather than receiving its input certificate. -/
def brownianFunctionInput (T : ℝ≥0) (F : ℝ → ℝ) (hF : Continuous F) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x, ‖F x‖ ≤ K) : fullPredictableL2 T :=
  continuousPredictableInput T (fun u ω => F (process u ω))
    (hF.measurable.comp measurable_joint_process)
    (fun u => hF.comp_stronglyMeasurable (process_stronglyAdapted u))
    (Eventually.of_forall (fun ω => hF.comp (process_continuous ω))) K hK (fun _ _ => hbound _)

/-- Fixed bounded clipping, used to derive inputs from the actual general
integral itself without granting any new temporal observation permission. -/
def clip (K x : ℝ) : ℝ := max (-K) (min K x)

private theorem continuous_clip (K : ℝ) : Continuous (clip K) :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem clip_bound (K : ℝ) (hK : 0 ≤ K) (x : ℝ) : ‖clip K x‖ ≤ K := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

/-- Actual bounded clipping of the SAME general integral is itself a genuine
predictable input, derived even though its paths are only source-AE continuous. -/
def actualClippedInput (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0 ≤ K) : fullPredictableL2 T :=
  continuousPredictableInput T (fun u ω => clip K (continuousIntegralProcess T f u ω))
    ((continuous_clip K).measurable.comp (continuousIntegralProcess_measurable T f))
    (fun u => (continuous_clip K).comp_stronglyMeasurable (continuousIntegralProcess_stronglyAdapted T f u))
    ((continuousIntegralProcess_continuous T f).mono (fun _ h => (continuous_clip K).comp h))
    K hK (fun _ _ => clip_bound K hK _)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousAdaptedInputs
