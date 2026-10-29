import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianProjectiveSource
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Original commitment: the realized stochastic source needs continuous paths, not only finite laws.
Existing result: the canonical source is actual all-time pre-Brownian with Gaussian increments.
Premise reduced: construct a continuous modification from source-derived dyadic increment bounds.
Model/witness: the SAME source law, zero start and nonzero noise; no continuity certificate is input.
Consumer: actual IsBrownianReal and the original OU continuous-source endpoint; general Ito/Girsanov remain open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource
open scoped ENNReal NNReal Topology
noncomputable section

private theorem gaussian_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) = 3*(v : ℝ)^2 := by
  let a : ℝ := v
  let F : ℝ → ℝ := fun t => Real.exp (a*t^2/2)
  have hF (t : ℝ) : HasDerivAt F (a*t*F t) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul a).div_const 2).exp using 1
    dsimp [F]
    ring
  have h0 : deriv F = fun t => a*t*F t := by
    funext t
    exact (hF t).deriv
  have h1 : deriv (fun t => a*t*F t) = fun t => (a+a^2*t^2)*F t := by
    funext t
    convert! (((hasDerivAt_id t).const_mul a).mul (hF t)).deriv using 1
    dsimp
    ring
  have h2 : deriv (fun t => (a+a^2*t^2)*F t) = fun t => (3*a^2*t+a^3*t^3)*F t := by
    funext t
    convert! (((hasDerivAt_const t a).add
      (((hasDerivAt_id t).pow 2).const_mul (a^2))).mul (hF t)).deriv using 1
    dsimp
    ring
  have h3 : deriv (fun t => (3*a^2*t+a^3*t^3)*F t) =
      fun t => (3*a^2+6*a^3*t^2+a^4*t^4)*F t := by
    funext t
    convert! ((((hasDerivAt_id t).const_mul (3*a^2)).add
      (((hasDerivAt_id t).pow 3).const_mul (a^3))).mul (hF t)).deriv using 1
    dsimp
    ring
  have hm := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by simp) 4
  rw [mgf_id_gaussianReal] at hm
  simp only [zero_mul,zero_add] at hm
  change iteratedDeriv 4 F 0 = _ at hm
  change (∫ x : ℝ, (id^4) x ∂gaussianReal 0 v) = _
  rw [← hm]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [h0,h1,h2,h3]
  simp [F,a]

/-- The actual realized source has the precise Gaussian fourth increment moment. -/
theorem source_increment_fourth_moment (s t : ℝ≥0) :
    (∫ ω, (ω s - ω t)^4 ∂sourceLaw) = 3*(nndist s t : ℝ)^2 := by
  have h := source_isPreBrownian.hasLaw_sub s t
  calc
    _ = ∫ x : ℝ, x^4 ∂gaussianReal 0 (nndist s t) := h.integral_comp (by fun_prop)
    _ = _ := gaussian_fourth_moment _

private theorem increment_fourth_integrable (s t : ℝ≥0) :
    Integrable (fun ω : ℝ≥0 → ℝ => (ω s - ω t)^4) sourceLaw := by
  have hm : MemLp (fun ω : ℝ≥0 → ℝ => ω s - ω t) 4 sourceLaw :=
    (source_isPreBrownian.hasLaw_sub s t).hasGaussianLaw.memLp (by norm_num)
  simpa only [Real.norm_eq_abs,Even.pow_abs (by decide : Even (4 : ℕ))] using
    hm.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0)

/-- Fourth-moment Markov bound for the actual source, with no tail certificate. -/
theorem source_increment_tail (s t : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    sourceLaw {ω | r ≤ |ω s - ω t|} ≤ ENNReal.ofReal (3*(nndist s t : ℝ)^2/r^4) := by
  have hsub : {ω : ℝ≥0 → ℝ | r ≤ |ω s - ω t|} ⊆ {ω | r^4 ≤ (ω s - ω t)^4} := by
    intro ω hω
    have h := pow_le_pow_left₀ hr.le hω 4
    simpa only [Set.mem_ofPred_eq,Even.pow_abs (by decide : Even (4 : ℕ))] using h
  have hnonneg : 0 ≤ᵐ[sourceLaw] (fun ω : ℝ≥0 → ℝ => (ω s - ω t)^4) :=
    ae_of_all sourceLaw (fun ω => by positivity)
  have hM := mul_meas_ge_le_integral_of_nonneg hnonneg (increment_fourth_integrable s t) (r^4)
  rw [source_increment_fourth_moment] at hM
  have hb : sourceLaw.real {ω | r ≤ |ω s - ω t|} ≤ 3*(nndist s t : ℝ)^2/r^4 :=
    (measureReal_mono hsub).trans ((le_div_iff₀ (pow_pos hr 4)).mpr (by nlinarith [hM]))
  calc
    _ = ENNReal.ofReal (sourceLaw.real {ω | r ≤ |ω s - ω t|}) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb

/-- A subsequence of dyadic grids. Base32 and threshold2^-n give a geometric
bad-event sum while keeping all deterministic estimates in rational powers. -/
private def grid (n k : ℕ) : ℝ≥0 := (k : ℝ≥0)/(32 : ℝ≥0)^n
private def index (n : ℕ) (t : ℝ≥0) : ℕ := ⌊(t : ℝ)*(32 : ℝ)^n⌋₊
private def approximateTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 := grid n (index n t)
private def step (n : ℕ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := ω (approximateTime n t)

@[simp] private theorem grid_coe (n k : ℕ) : (grid n k : ℝ) = (k : ℝ)/(32 : ℝ)^n := by
  simp [grid]

private theorem grid_adjacent_dist (n k : ℕ) :
    (nndist (grid n (k+1)) (grid n k) : ℝ) = 1/(32 : ℝ)^n := by
  change dist (grid n (k+1)) (grid n k) = _
  rw [NNReal.dist_eq,grid_coe,grid_coe]
  have h : ((k+1 : ℕ) : ℝ)/(32 : ℝ)^n-(k : ℝ)/(32 : ℝ)^n = 1/(32 : ℝ)^n := by
    push_cast
    ring
  rw [h,abs_of_pos (by positivity)]

private theorem approximateTime_le (n : ℕ) (t : ℝ≥0) : approximateTime n t ≤ t := by
  have h := Nat.floor_le (by positivity : 0 ≤ (t : ℝ)*(32 : ℝ)^n)
  change (grid n (index n t) : ℝ≥0) ≤ t
  rw [← NNReal.coe_le_coe,grid_coe]
  exact (div_le_iff₀ (by positivity : 0 < (32 : ℝ)^n)).mpr h

private theorem approximateTime_gap (n : ℕ) (t : ℝ≥0) :
    (t : ℝ)-(approximateTime n t : ℝ) < 1/(32 : ℝ)^n := by
  have h := Nat.lt_floor_add_one ((t : ℝ)*(32 : ℝ)^n)
  change (t : ℝ)-(grid n (index n t) : ℝ) < _
  rw [grid_coe]
  apply (lt_div_iff₀ (by positivity : 0 < (32 : ℝ)^n)).mpr
  dsimp only [index] at *
  field_simp
  nlinarith

private theorem index_bound (n N : ℕ) (t : ℝ≥0) (ht : t ≤ N) : index n t ≤ N*32^n := by
  have hf := Nat.floor_le (by positivity : 0 ≤ (t : ℝ)*(32 : ℝ)^n)
  have ht' : (t : ℝ) ≤ N := by exact_mod_cast ht
  have h : (index n t : ℝ) ≤ (N : ℝ)*(32 : ℝ)^n :=
    hf.trans (mul_le_mul_of_nonneg_right ht' (by positivity))
  exact_mod_cast h

private theorem grid_refinement (n k : ℕ) : grid (n+1) (32*k) = grid n k := by
  apply NNReal.coe_injective
  simp only [grid_coe,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

private theorem index_refinement (n : ℕ) (t : ℝ≥0) :
    32*index n t ≤ index (n+1) t ∧ index (n+1) t < 32*index n t+32 := by
  have hl := Nat.floor_le (by positivity : 0 ≤ (t : ℝ)*(32 : ℝ)^n)
  have hu := Nat.lt_floor_add_one ((t : ℝ)*(32 : ℝ)^n)
  constructor
  · apply Nat.le_floor
    dsimp only [index]
    push_cast
    rw [pow_succ]
    nlinarith
  · apply (Nat.floor_lt' (by omega : 32*index n t+32 ≠ 0)).mpr
    dsimp only [index] at *
    push_cast
    rw [pow_succ]
    nlinarith

private def bad (N n : ℕ) : Set (ℝ≥0 → ℝ) :=
  ⋃ k : Fin (N*32^n+1), {ω | (1/2 : ℝ)^n < |ω (grid n (k+1)) - ω (grid n k)|}

private theorem measurableSet_bad (N n : ℕ) : MeasurableSet (bad N n) := by
  apply MeasurableSet.iUnion
  intro k
  have h : Measurable (fun ω : ℝ≥0 → ℝ =>
      |ω (grid n ((k : ℕ)+1)) - ω (grid n k)|) :=
    ((measurable_pi_apply (grid n ((k : ℕ)+1))).sub (measurable_pi_apply (grid n k))).abs
  exact measurableSet_lt measurable_const h

private theorem grid_increment_tail (n k : ℕ) :
    sourceLaw {ω | (1/2 : ℝ)^n < |ω (grid n (k+1)) - ω (grid n k)|} ≤
      ENNReal.ofReal (3*(1/64 : ℝ)^n) := by
  have h := source_increment_tail (grid n (k+1)) (grid n k) ((1/2 : ℝ)^n) (by positivity)
  rw [grid_adjacent_dist] at h
  have halg : 3*(1/(32 : ℝ)^n)^2/((1/2 : ℝ)^n)^4 = 3*(1/64 : ℝ)^n := by
    have hi : 1/(32 : ℝ)^n = (1/32 : ℝ)^n := by simp
    rw [hi,pow_right_comm (1/32 : ℝ) n 2,pow_right_comm (1/2 : ℝ) n 4,mul_div_assoc,← div_pow]
    norm_num
  rw [halg] at h
  have hsub : {ω : ℝ≥0 → ℝ | (1/2 : ℝ)^n < |ω (grid n (k+1)) - ω (grid n k)|} ⊆
      {ω | (1/2 : ℝ)^n ≤ |ω (grid n (k+1)) - ω (grid n k)|} := by
    intro ω hω
    change (1/2 : ℝ)^n < |ω (grid n (k+1)) - ω (grid n k)| at hω
    change (1/2 : ℝ)^n ≤ |ω (grid n (k+1)) - ω (grid n k)|
    exact hω.le
  exact (measure_mono hsub).trans h

private theorem bad_probability_bound (N n : ℕ) :
    sourceLaw (bad N n) ≤ ENNReal.ofReal (3*((N : ℝ)+1)*(1/2 : ℝ)^n) := by
  calc
    _ ≤ ∑ k : Fin (N*32^n+1),
        sourceLaw {ω | (1/2 : ℝ)^n < |ω (grid n (k+1)) - ω (grid n k)|} :=
      measure_iUnion_fintype_le sourceLaw _
    _ ≤ ∑ _k : Fin (N*32^n+1), ENNReal.ofReal (3*(1/64 : ℝ)^n) :=
      Finset.sum_le_sum (fun k _ => grid_increment_tail n k)
    _ = ENNReal.ofReal (((N*32^n+1 : ℕ) : ℝ)*(3*(1/64 : ℝ)^n)) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hp : 1 ≤ (32 : ℝ)^n := one_le_pow₀ (by norm_num)
      have hc : ((N*32^n+1 : ℕ) : ℝ) ≤ ((N : ℝ)+1)*(32 : ℝ)^n := by
        push_cast
        nlinarith
      have hpow : (32 : ℝ)^n*(1/64 : ℝ)^n = (1/2 : ℝ)^n := by
        rw [← mul_pow]
        norm_num
      calc
        _ ≤ (((N : ℝ)+1)*(32 : ℝ)^n)*(3*(1/64 : ℝ)^n) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by rw [← hpow]; ring

private theorem bad_summable (N : ℕ) : (∑' n, sourceLaw (bad N n)) ≠ ∞ := by
  have h : Summable (fun n : ℕ => 3*((N : ℝ)+1)*(1/2 : ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left _
  exact ne_top_of_le_ne_top h.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum (bad_probability_bound N))

/-- The good event uses only COUNTABLY many compact horizons and grid edges. -/
private def Good (ω : ℝ≥0 → ℝ) : Prop := ∀ N : ℕ, ∀ᶠ n in atTop, ω ∉ bad N n

private theorem good_ae : ∀ᵐ ω ∂sourceLaw, Good ω := by
  rw [show (fun ω => Good ω) = (fun ω => ∀ N : ℕ, ∀ᶠ n in atTop, ω ∉ bad N n) from rfl,ae_all_iff]
  intro N
  exact ae_eventually_notMem (bad_summable N)

private theorem measurableSet_good : MeasurableSet {ω | Good ω} := by
  simp only [Good,eventually_atTop,ofPred_forall,ofPred_exists]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun M =>
    MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun _hn : M ≤ n =>
      (measurableSet_bad N n).compl))))

private theorem good_adjacent {ω : ℝ≥0 → ℝ} (hω : Good ω) (N : ℕ) :
    ∃ M, ∀ n ≥ M, ∀ k ≤ N*32^n,
      |ω (grid n (k+1)) - ω (grid n k)| ≤ (1/2 : ℝ)^n := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hω N)
  refine ⟨M,fun n hn k hk => ?_⟩
  apply le_of_not_gt
  intro h
  apply hM n hn
  exact mem_iUnion.mpr ⟨⟨k,by omega⟩,h⟩

private theorem chain_bound (f : ℕ → ℝ) (a : ℕ) (δ : ℝ) : ∀ r : ℕ,
    (∀ j, a ≤ j → j < a+r → |f (j+1)-f j| ≤ δ) →
      |f (a+r)-f a| ≤ (r : ℝ)*δ := by
  intro r
  induction r with
  | zero => intros; simp
  | succ r ih =>
      intro h
      have hh := ih (fun j hja hjr => h j hja (by omega))
      have hl := h (a+r) (by omega) (by omega)
      have ht := abs_sub_le (f (a+(r+1))) (f (a+r)) (f a)
      push_cast
      simpa only [Nat.add_assoc] using ht.trans (add_le_add hl hh) |>.trans_eq (by ring)

private theorem step_refinement_bound (N n : ℕ) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) (ht : t ≤ N)
    (h : ∀ k ≤ N*32^(n+1), |ω (grid (n+1) (k+1))-ω (grid (n+1) k)| ≤ (1/2 : ℝ)^(n+1)) :
    dist (step n t ω) (step (n+1) t ω) ≤ 16*(1/2 : ℝ)^n := by
  let a := 32*index n t
  let j := index (n+1) t
  have href := index_refinement n t
  have ha : a ≤ j := href.1
  have hr : j-a ≤ 32 := by dsimp only [a,j]; omega
  have hj : j ≤ N*32^(n+1) := index_bound (n+1) N t ht
  have hc := chain_bound (fun k => ω (grid (n+1) k)) a ((1/2 : ℝ)^(n+1)) (j-a)
    (fun k hka hkj => h k (by omega))
  rw [Nat.add_sub_cancel' ha] at hc
  have hcr : |ω (grid (n+1) j)-ω (grid (n+1) a)| ≤ 32*(1/2 : ℝ)^(n+1) :=
    hc.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by positivity))
  change |ω (grid n (index n t))-ω (grid (n+1) j)| ≤ _
  rw [← grid_refinement n (index n t),abs_sub_comm]
  exact hcr.trans_eq (by rw [pow_succ]; ring)

private theorem index_near (n : ℕ) (s t : ℝ≥0) (h : dist s t < 1/(32 : ℝ)^n) :
    index n s ≤ index n t+1 ∧ index n t ≤ index n s+1 := by
  have hp : 0 < (32 : ℝ)^n := by positivity
  rw [NNReal.dist_eq] at h
  have hc : |(s : ℝ)*(32 : ℝ)^n-(t : ℝ)*(32 : ℝ)^n| < 1 := by
    rw [← sub_mul,abs_mul,abs_of_pos hp]
    have hh := mul_lt_mul_of_pos_right h hp
    simpa using hh
  have hl_s := Nat.floor_le (by positivity : 0 ≤ (s : ℝ)*(32 : ℝ)^n)
  have hl_t := Nat.floor_le (by positivity : 0 ≤ (t : ℝ)*(32 : ℝ)^n)
  have hu_s := Nat.lt_floor_add_one ((s : ℝ)*(32 : ℝ)^n)
  have hu_t := Nat.lt_floor_add_one ((t : ℝ)*(32 : ℝ)^n)
  have hs : (s : ℝ)*(32 : ℝ)^n-(t : ℝ)*(32 : ℝ)^n < 1 :=
    (le_abs_self _).trans_lt hc
  have ht : (t : ℝ)*(32 : ℝ)^n-(s : ℝ)*(32 : ℝ)^n < 1 := by
    rw [abs_sub_comm] at hc
    exact (le_abs_self _).trans_lt hc
  have hst : index n s < index n t+2 := by
    have hh : (index n s : ℝ) < (index n t : ℝ)+2 := by dsimp [index]; linarith
    exact_mod_cast hh
  have hts : index n t < index n s+2 := by
    have hh : (index n t : ℝ) < (index n s : ℝ)+2 := by dsimp [index]; linarith
    exact_mod_cast hh
  omega

private theorem step_oscillation_bound (N n : ℕ) (s t : ℝ≥0) (ω : ℝ≥0 → ℝ)
    (hs : s ≤ N) (ht : t ≤ N) (hd : dist s t < 1/(32 : ℝ)^n)
    (h : ∀ k ≤ N*32^n, |ω (grid n (k+1))-ω (grid n k)| ≤ (1/2 : ℝ)^n) :
    dist (step n s ω) (step n t ω) ≤ (1/2 : ℝ)^n := by
  have hi := index_near n s t hd
  have hc : index n s = index n t ∨ index n s+1 = index n t ∨ index n t+1 = index n s := by omega
  rcases hc with he | he | he
  · simp [step,approximateTime,he]
  · change |ω (grid n (index n s))-ω (grid n (index n t))| ≤ _
    rw [← he,abs_sub_comm]
    exact h (index n s) (index_bound n N s hs)
  · change |ω (grid n (index n s))-ω (grid n (index n t))| ≤ _
    rw [← he]
    exact h (index n t) (index_bound n N t ht)

private theorem step_cauchy {ω : ℝ≥0 → ℝ} (hω : Good ω) (t : ℝ≥0) :
    CauchySeq (fun n => step n t ω) := by
  obtain ⟨N,hN⟩ := exists_nat_ge t
  obtain ⟨M,hM⟩ := good_adjacent hω N
  have he : ∀ᶠ n in atTop, dist (step n t ω) (step (n+1) t ω) ≤ 16*(1/2 : ℝ)^n := by
    filter_upwards [eventually_ge_atTop M] with n hn
    exact step_refinement_bound N n t ω hN (hM (n+1) (by omega))
  have hg : Summable (fun n : ℕ => 16*(1/2 : ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun n => dist (step n t ω) (step (n+1) t ω)) := by
    apply hg.of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using he
  exact cauchySeq_of_summable_dist hs

/-- The actual continuous version is built from the countable grid sequence.
Outside the one measurable countable-good event it is the zero path. -/
def process (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := by
  classical
  exact if Good ω then atTop.limUnder (fun n => step n t ω) else 0

private theorem step_tendsto {ω : ℝ≥0 → ℝ} (hω : Good ω) (t : ℝ≥0) :
    Tendsto (fun n => step n t ω) atTop (𝓝 (process t ω)) := by
  classical
  simpa only [process,if_pos hω] using (step_cauchy hω t).tendsto_limUnder

/-- Every fixed-time coordinate is measurable, with one common good-event
fallback; separate unrelated a.e. versions are not selected at each time. -/
theorem measurable_process (t : ℝ≥0) : Measurable (process t) := by
  classical
  have hf (n : ℕ) : StronglyMeasurable (step n t) :=
    (measurable_pi_apply (approximateTime n t)).stronglyMeasurable
  have hm := (StronglyMeasurable.limUnder (l := atTop) hf).measurable
  exact Measurable.ite measurableSet_good hm measurable_const

private theorem step_tail_bound {ω : ℝ≥0 → ℝ} (hω : Good ω) (N M n : ℕ)
    (hM : ∀ r ≥ M, ∀ k ≤ N*32^r, |ω (grid r (k+1))-ω (grid r k)| ≤ (1/2 : ℝ)^r)
    (hn : M ≤ n) (t : ℝ≥0) (ht : t ≤ N) :
    dist (step n t ω) (process t ω) ≤ 32*(1/2 : ℝ)^n := by
  have hb (k : ℕ) : dist (step (k+n) t ω) (step ((k+1)+n) t ω) ≤
      (16*(1/2 : ℝ)^n)*(1/2 : ℝ)^k := by
    have he : (k+1)+n = (k+n)+1 := by omega
    rw [he]
    calc
      _ ≤ 16*(1/2 : ℝ)^(k+n) :=
        step_refinement_bound N (k+n) t ω ht (hM ((k+n)+1) (by omega))
      _ = _ := by rw [pow_add]; ring
  have hl := (step_tendsto hω t).comp (tendsto_add_atTop_nat n)
  have hh := dist_le_of_le_geometric_of_tendsto₀ (1/2 : ℝ) (16*(1/2 : ℝ)^n) (by norm_num) hb hl
  rw [Nat.zero_add] at hh
  exact hh.trans_eq (by ring)

private theorem continuous_good {ω : ℝ≥0 → ℝ} (hω : Good ω) :
    Continuous (fun t => process t ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt ((t : ℝ)+1)
  have ht : t ≤ (N : ℝ≥0) := by exact_mod_cast (by linarith : (t : ℝ) ≤ N)
  obtain ⟨M,hM⟩ := good_adjacent hω N
  have hp : Tendsto (fun n : ℕ => 65*(1/2 : ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ))
      (by norm_num : (1/2 : ℝ) < 1)).const_mul 65
  obtain ⟨n,hnM,hnε⟩ := ((eventually_ge_atTop M).and (hp.eventually (gt_mem_nhds hε))).exists
  refine ⟨min 1 (1/(32 : ℝ)^n),lt_min (by norm_num) (by positivity),?_⟩
  intro u hu
  have hu1 : dist u t < 1 := hu.trans_le (min_le_left _ _)
  have hun : dist u t < 1/(32 : ℝ)^n := hu.trans_le (min_le_right _ _)
  have huN : u ≤ (N : ℝ≥0) := by
    rw [NNReal.dist_eq] at hu1
    have hh : (u : ℝ)-(t : ℝ) < 1 := (le_abs_self _).trans_lt hu1
    exact_mod_cast (by linarith : (u : ℝ) ≤ (N : ℝ))
  have htu := step_tail_bound hω N M n hM hnM u huN
  have htt := step_tail_bound hω N M n hM hnM t ht
  have hcoarse := step_oscillation_bound N n u t ω huN ht hun (hM n hnM)
  have htri := dist_triangle (process u ω) (step n u ω) (process t ω)
  have htri2 := dist_triangle (step n u ω) (step n t ω) (process t ω)
  rw [dist_comm (process u ω) (step n u ω)] at htri
  linarith

/-- Every path of the constructed version is continuous: actual countable
chaining on Good, and the SAME zero path outside Good. The raw canonical
coordinate path is not asserted continuous. -/
theorem process_continuous (ω : ℝ≥0 → ℝ) : Continuous (fun t => process t ω) := by
  classical
  by_cases hω : Good ω
  · exact continuous_good hω
  · simp only [process,if_neg hω]
    exact continuous_const

private theorem approximateTime_dist_tendsto (t : ℝ≥0) :
    Tendsto (fun n => dist (approximateTime n t) t) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => 1/(32 : ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/32 : ℝ))
      (by norm_num : (1/32 : ℝ) < 1))
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hg
  have hle : (approximateTime n t : ℝ) ≤ (t : ℝ) := by exact_mod_cast approximateTime_le n t
  rw [NNReal.dist_eq,abs_of_nonpos (sub_nonpos.mpr hle)]
  have h := approximateTime_gap n t
  linarith

private theorem increment_second_moment (s t : ℝ≥0) :
    (∫ ω, (ω s - ω t)^2 ∂sourceLaw) = (nndist s t : ℝ) := by
  have h := source_isPreBrownian.hasLaw_sub s t
  calc
    _ = ∫ x : ℝ, x^2 ∂gaussianReal 0 (nndist s t) := h.integral_comp (by fun_prop)
    _ = _ := by
      have hv := variance_id_gaussianReal (μ := 0) (v := nndist s t)
      rw [variance_eq_integral measurable_id.aemeasurable] at hv
      simp only [id_eq, integral_id_gaussianReal, sub_zero] at hv
      simpa only [sub_zero] using hv

private theorem increment_second_tail (s t : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    sourceLaw.real {ω | r ≤ |ω s - ω t|} ≤ (nndist s t : ℝ)/r^2 := by
  have hsub : {ω : ℝ≥0 → ℝ | r ≤ |ω s - ω t|} ⊆ {ω | r^2 ≤ (ω s - ω t)^2} := by
    intro ω hω
    have h := pow_le_pow_left₀ hr.le hω 2
    simpa only [Set.mem_ofPred_eq,Even.pow_abs (by decide : Even (2 : ℕ))] using h
  have hi := (source_isPreBrownian.hasLaw_sub s t).hasGaussianLaw.memLp_two.integrable_sq
  have hn : 0 ≤ᵐ[sourceLaw] (fun ω : ℝ≥0 → ℝ => (ω s - ω t)^2) :=
    ae_of_all sourceLaw (fun ω => sq_nonneg _)
  have hM := mul_meas_ge_le_integral_of_nonneg hn hi (r^2)
  rw [increment_second_moment] at hM
  exact (measureReal_mono hsub).trans ((le_div_iff₀ (pow_pos hr 2)).mpr (by nlinarith [hM]))

private theorem step_tendstoInMeasure (t : ℝ≥0) :
    TendstoInMeasure sourceLaw (fun n => step n t) atTop (fun ω => ω t) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  apply squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
    (by simpa using (approximateTime_dist_tendsto t).div_const (ε^2))
  simpa only [step,Real.norm_eq_abs,coe_nndist] using increment_second_tail (approximateTime n t) t ε hε

/-- For EACH fixed time the constructed continuous process equals the actual
canonical coordinate a.e. No uncountable a.e. intersection is taken. -/
theorem process_eq_coordinate_ae (t : ℝ≥0) : process t =ᵐ[sourceLaw] (fun ω => ω t) := by
  have hlim : ∀ᵐ ω ∂sourceLaw, Tendsto (fun n => step n t ω) atTop (𝓝 (process t ω)) :=
    good_ae.mono (fun ω hω => step_tendsto hω t)
  have hi := tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_pi_apply (approximateTime n t)).aestronglyMeasurable) hlim
  exact tendstoInMeasure_ae_unique hi (step_tendstoInMeasure t)

/-- All finite Brownian laws transfer through the proved fixed-time
modification relation; they are not supplied as new process hypotheses. -/
theorem process_isPreBrownian : IsPreBrownianReal process sourceLaw :=
  source_isPreBrownian.congr (fun t => (process_eq_coordinate_ae t).symm)

/-- Actual Brownian realization: source-derived finite laws AND source-derived
continuous paths, without a Brownian/continuity/Kolmogorov certificate input. -/
theorem process_isBrownian : IsBrownianReal process sourceLaw where
  toIsPreBrownianReal := process_isPreBrownian
  cont := ae_of_all sourceLaw process_continuous

/-- Native Caratheodory measurability uses the proved continuous paths and
fixed-time measurability of this actual version. -/
theorem measurable_joint_process : Measurable (Function.uncurry process) :=
  measurable_uncurry_of_continuous_of_measurable process_continuous measurable_process

theorem process_zero : ∀ᵐ ω ∂sourceLaw, process 0 ω = 0 :=
  process_isPreBrownian.eval_zero_ae_eq_zero

theorem process_unit_variance : variance (process 1) sourceLaw = 1 := by
  rw [← covariance_self, process_isPreBrownian.covariance_eval, min_self]
  · rfl
  · exact process_isPreBrownian.aemeasurable 1

/-- The original OU continuity consumer now uses the SAME actually constructed
Brownian source, with no externally supplied continuous Brownian process. -/
theorem actual_ou_continuous (k s x0 : ℝ) :
    ∀ᵐ ω ∂sourceLaw, Continuous (fun t => OUQuadraticDynkinSource.ouSource process k s x0 t ω) :=
  OUQuadraticDynkinSource.ou_source_continuous process_isBrownian k s x0

/-- The realized continuous source has nonzero execution noise at every
positive time, even from a deterministic actual initial state. -/
theorem actual_ou_positive_variance (k s x0 : ℝ) (hk : 0 < k) (hs : s ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) :
    0 < variance (OUQuadraticDynkinSource.ouSource process k s x0 t) sourceLaw :=
  OUQuadraticDynkinSource.nonzero_noise_positive_variance process_isPreBrownian k s x0 hk hs t ht

/-- The continuous version preserves the original canonical OU finite-time
laws, rather than silently replacing the previously checked family. -/
theorem ou_law_eq_canonical (k s x0 t : ℝ) :
    OUQuadraticDynkinSource.ouLaw sourceLaw process k s x0 t =
      OUQuadraticDynkinSource.ouLaw sourceLaw (fun t ω => ω t) k s x0 t := by
  apply Measure.map_congr
  filter_upwards [process_eq_coordinate_ae
    (OUQuadraticDynkinSource.ouClock k (Real.toNNReal t))] with ω hω
  simp only [OUQuadraticDynkinSource.ouSource,hω]

/-- Existing actual recovery estimates are transported along the proved law
identity, while actual paths now come from the continuous modification. -/
theorem actual_ou_recovery (k s x0 T : ℝ) (hk : 0 < k) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T,
      (∫ x, x^2 ∂OUQuadraticDynkinSource.ouLaw sourceLaw process k s x0 t) ≤
        Real.exp (-(2*k)*t)*x0^2+s^2/(2*k)*(1-Real.exp (-(2*k)*t)) := by
  intro t ht
  rw [ou_law_eq_canonical]
  exact BrownianProjectiveSource.actual_ou_recovery k s x0 T hk hT t ht

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousSource
