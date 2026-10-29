import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariationSteps

/-!
Original commitment: the Brownian second-order term is a limit of actual squared source increments.
Existing result: same-source centered squares have derived exact variance and natural-past weighted orthogonality.
Premise reduced: derive literal deterministic-partition quadratic variation and its actual mesh-controlled L2 limit.
Model/witness: SAME scalar process/sourceLaw; every finite nondecreasing deterministic clock, repeated times allowed.
Consumer: weighted second-order Ito/compensator source; vector/other-filtered source generalization remains separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariation
open MeasureTheory ProbabilityTheory Set Filter
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource BrownianQuadraticVariationSteps
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual finite error, retaining the original clock and permitted weights. -/
def errorSum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin n, weightedError (H i) (τ i.castSucc) (τ i.succ) ω

theorem errorSum_memLp_two {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) : MemLp (errorSum τ H) 2 sourceLaw :=
  memLp_finsetSum Finset.univ (fun i _ => weightedError_memLp_two (hH i) _ _)

private theorem clock_order {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hτ (by exact_mod_cast Nat.le_succ (i : ℕ))

private theorem error_cross {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) (i j : Fin n) (hij : i ≠ j) :
    (∫ ω, weightedError (H i) (τ i.castSucc) (τ i.succ) ω *
      weightedError (H j) (τ j.castSucc) (τ j.succ) ω ∂sourceLaw) = 0 := by
  have ho (a b : Fin n) (hab : a < b) :
      (∫ ω, weightedError (H a) (τ a.castSucc) (τ a.succ) ω *
        weightedError (H b) (τ b.castSucc) (τ b.succ) ω ∂sourceLaw) = 0 := by
    exact weightedError_nonoverlap _ _ _ _ (clock_order τ hτ a)
      (hτ (by exact_mod_cast Nat.succ_le_of_lt hab)) (clock_order τ hτ b)
      (hHpast a) (hHpast b) (hH a) (hH b)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ho i j h
  · simpa only [mul_comm] using ho j i h

/-- Exact weighted quadratic-variation error energy from actual Gaussian
fourth moments and causal orthogonality; covariance is not an input field. -/
theorem errorSum_variance {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    (∫ ω, errorSum τ H ω ^ 2 ∂sourceLaw) =
      ∑ i : Fin n, (2*((τ i.succ : ℝ)-(τ i.castSucc : ℝ))^2) * (∫ ω, H i ω ^ 2 ∂sourceLaw) := by
  let Y (i : Fin n) := weightedError (H i) (τ i.castSucc) (τ i.succ)
  have hi (i j : Fin n) : Integrable (fun ω => Y i ω * Y j ω) sourceLaw :=
    (weightedError_memLp_two (hH i) _ _).integrable_mul (weightedError_memLp_two (hH j) _ _)
  have he : (fun ω => errorSum τ H ω ^ 2) =
      (fun ω => ∑ i : Fin n, ∑ j : Fin n, Y i ω * Y j ω) := by
    ext ω
    simp only [errorSum,pow_two,Fintype.sum_mul_sum,Y]
  rw [he,integral_finsetSum Finset.univ (f := fun i ω => ∑ j : Fin n, Y i ω * Y j ω)
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j),Finset.sum_eq_single i]
  · simpa only [← pow_two] using weightedError_variance _ _ (clock_order τ hτ i) (hHpast i) (hH i)
  · intro j _ hji
    exact error_cross τ H hτ hHpast hH i j hji.symm
  · simp

/-- The weight is actual past-measurable data; the target is its SAME clock
sum. The centered error is literally the difference of these two finite sums. -/
theorem errorSum_eq_weighted_difference {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) :
    errorSum τ H ω =
      (∑ i : Fin n, H i ω * increment (τ i.castSucc) (τ i.succ) ω ^ 2) -
      (∑ i : Fin n, H i ω * ((τ i.succ : ℝ)-(τ i.castSucc : ℝ))) := by
  simp only [errorSum,weightedError,Pi.mul_apply,centeredSquare,mul_sub,Finset.sum_sub_distrib]

/-- Mesh is COMPUTED from the caller's original finite clock. -/
def mesh {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : ℝ≥0 :=
  Finset.univ.sup (fun i : Fin n => τ i.succ-τ i.castSucc)

private theorem gap_le_mesh {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    (τ i.succ : ℝ)-(τ i.castSucc : ℝ) ≤ (mesh τ : ℝ) := by
  have h : τ i.succ-τ i.castSucc ≤ mesh τ := Finset.le_sup (f := fun j : Fin n => τ j.succ-τ j.castSucc) (Finset.mem_univ i)
  have hc := NNReal.coe_le_coe.mpr h
  rwa [NNReal.coe_sub (clock_order τ hτ i)] at hc

private theorem sum_gaps {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    (∑ i : Fin n, ((τ i.succ : ℝ)-(τ i.castSucc : ℝ))) = (τ (Fin.last n) : ℝ)-(τ 0 : ℝ) := by
  rw [Finset.sum_sub_distrib]
  have h0 := Fin.sum_univ_succ (fun i => (τ i : ℝ))
  have hN := Fin.sum_univ_castSucc (fun i => (τ i : ℝ))
  linarith

/-- Literal unweighted squared-increment sum. -/
def quadraticVariation {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin n, increment (τ i.castSucc) (τ i.succ) ω ^ 2

theorem quadraticVariation_error {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (ω : ℝ≥0 → ℝ) :
    quadraticVariation τ ω-((τ (Fin.last n) : ℝ)-(τ 0 : ℝ)) = errorSum τ (fun _ _ => 1) ω := by
  rw [errorSum_eq_weighted_difference]
  simp only [one_mul,quadraticVariation,sum_gaps]

/-- Exact actual Brownian partition MSE, valid for arbitrary deterministic
nondecreasing clocks, including repeated times and the empty partition. -/
theorem quadraticVariation_meanSquare {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ ω, (quadraticVariation τ ω-((τ (Fin.last n) : ℝ)-(τ 0 : ℝ)))^2 ∂sourceLaw) =
      2*∑ i : Fin n, ((τ i.succ : ℝ)-(τ i.castSucc : ℝ))^2 := by
  simp_rw [quadraticVariation_error]
  rw [errorSum_variance τ (fun _ _ => 1) hτ (fun _ => stronglyMeasurable_const) (fun _ => memLp_top_const 1)]
  simp only [one_pow,integral_const,probReal_univ,one_smul,mul_one,Finset.mul_sum]

theorem quadraticVariation_mesh_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ ω, (quadraticVariation τ ω-((τ (Fin.last n) : ℝ)-(τ 0 : ℝ)))^2 ∂sourceLaw) ≤
      2*(mesh τ : ℝ)*((τ (Fin.last n) : ℝ)-(τ 0 : ℝ)) := by
  rw [quadraticVariation_meanSquare τ hτ,← sum_gaps,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hg : (0 : ℝ) ≤ (τ i.succ : ℝ)-(τ i.castSucc : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast clock_order τ hτ i)
  have hm := mul_le_mul_of_nonneg_right (gap_le_mesh τ hτ i) hg
  nlinarith

/-- The actual source squared-increment sums converge in mean square for
EVERY family of caller-supplied partitions whose COMPUTED mesh tends to zero. -/
theorem quadraticVariation_meanSquare_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hτ : ∀ m, Monotone (τ m))
    (h0 : ∀ m, τ m 0 = 0) (hT : ∀ m, τ m (Fin.last (N m)) = T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, (quadraticVariation (τ m) ω-(T : ℝ))^2 ∂sourceLaw) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
  · intro m
    simpa only [h0,hT,NNReal.coe_zero,sub_zero] using quadraticVariation_mesh_bound (τ m) (hτ m)
  · simpa only [mul_zero,zero_mul] using (hmesh.const_mul 2).mul_const (T : ℝ)

/-- Actual uniformly bounded predictable weights give the SAME mesh rate;
the bound is on the supplied coefficient values, not on a desired covariance. -/
theorem errorSum_mesh_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ i, ∀ᵐ ω ∂sourceLaw, |H i ω| ≤ K) :
    (∫ ω, errorSum τ H ω ^ 2 ∂sourceLaw) ≤
      2*K^2*(mesh τ : ℝ)*((τ (Fin.last n) : ℝ)-(τ 0 : ℝ)) := by
  have hsq (i : Fin n) : (∫ ω, H i ω ^ 2 ∂sourceLaw) ≤ K^2 := by
    have hi : Integrable (fun ω => H i ω ^ 2) sourceLaw :=
      ((hH i).mono_exponent (show (2 : ℝ≥0∞) ≤ ∞ from le_top)).integrable_sq
    have hm : (∫ ω, H i ω ^ 2 ∂sourceLaw) ≤ ∫ _ω : ℝ≥0 → ℝ, K^2 ∂sourceLaw :=
      integral_mono_ae hi (integrable_const _) ((hbound i).mono (fun ω hω => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr hω))
    simpa only [integral_const,probReal_univ,one_smul] using hm
  rw [errorSum_variance τ H hτ hHpast hH,← sum_gaps,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hg : (0 : ℝ) ≤ (τ i.succ : ℝ)-(τ i.castSucc : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast clock_order τ hτ i)
  calc
    _ ≤ (2*((τ i.succ : ℝ)-(τ i.castSucc : ℝ))^2)*K^2 :=
      mul_le_mul_of_nonneg_left (hsq i) (by positivity)
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right (gap_le_mesh τ hτ i) hg
      nlinarith [sq_nonneg K]

/-- Weighted quadratic variation converges to its SAME weighted clock sum in
mean square, uniformly over actual bounded START-measurable weights, which
may vary with the deterministic partitions. -/
theorem weightedQuadraticVariation_meanSquare_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (H : (m : ℕ) → Fin (N m) → (ℝ≥0 → ℝ) → ℝ)
    (hτ : ∀ m, Monotone (τ m)) (h0 : ∀ m, τ m 0 = 0)
    (hT : ∀ m, τ m (Fin.last (N m)) = T)
    (hHpast : ∀ m i, StronglyMeasurable[naturalFiltration (τ m i.castSucc)] (H m i))
    (hH : ∀ m i, MemLp (H m i) ∞ sourceLaw) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ m i, ∀ᵐ ω ∂sourceLaw, |H m i ω| ≤ K)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω,
      ((∑ i : Fin (N m), H m i ω * increment (τ m i.castSucc) (τ m i.succ) ω ^ 2) -
        (∑ i : Fin (N m), H m i ω * ((τ m i.succ : ℝ)-(τ m i.castSucc : ℝ))))^2 ∂sourceLaw)
      atTop (𝓝 0) := by
  simp_rw [← errorSum_eq_weighted_difference]
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
  · intro m
    simpa only [h0,hT,NNReal.coe_zero,sub_zero] using
      errorSum_mesh_bound (τ m) (H m) (hτ m) (hHpast m) (hH m) K hK (hbound m)
  · simpa only [mul_zero,zero_mul] using (hmesh.const_mul (2*K^2)).mul_const (T : ℝ)

/-- L2 membership of the actual squared-increment sum, from the actual
centered sum and literal deterministic clock. -/
theorem quadraticVariation_memLp_two {n : ℕ} (τ : Fin (n+1) → ℝ≥0) :
    MemLp (quadraticVariation τ) 2 sourceLaw := by
  have he : quadraticVariation τ = errorSum τ (fun _ _ => 1)+
      (fun _ => ((τ (Fin.last n) : ℝ)-(τ 0 : ℝ))) := by
    ext ω
    have h := quadraticVariation_error τ ω
    simp only [Pi.add_apply]
    linarith
  rw [he]
  exact (errorSum_memLp_two τ (fun _ _ => 1) (fun _ => memLp_top_const 1)).add (memLp_const _)

def quadraticVariationClass {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : Lp ℝ 2 sourceLaw :=
  (quadraticVariation_memLp_two τ).toLp (quadraticVariation τ)

def clockClass (T : ℝ≥0) : Lp ℝ 2 sourceLaw :=
  (memLp_const (μ := sourceLaw) (p := 2) (T : ℝ)).toLp (fun _ => (T : ℝ))

private theorem class_error_norm {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (T : ℝ≥0) :
    ‖quadraticVariationClass τ-clockClass T‖^2 =
      ∫ ω, (quadraticVariation τ ω-(T : ℝ))^2 ∂sourceLaw := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (quadraticVariationClass τ) (clockClass T),
    (quadraticVariation_memLp_two τ).coeFn_toLp,
    (memLp_const (μ := sourceLaw) (p := 2) (T : ℝ)).coeFn_toLp] with ω hs hq hc
  simp only [Pi.sub_apply] at hs
  rw [hs]
  change (((quadraticVariation_memLp_two τ).toLp (quadraticVariation τ)) ω-
    ((memLp_const (μ := sourceLaw) (p := 2) (T : ℝ)).toLp (fun _ => (T : ℝ))) ω)^2 = _
  rw [hq,hc]

/-- Native source L2 convergence of the SAME computed squared-increment
classes to the SAME literal clock constant; no alternative limit is chosen. -/
theorem quadraticVariationClass_tendsto (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hτ : ∀ m, Monotone (τ m))
    (h0 : ∀ m, τ m 0 = 0) (hT : ∀ m, τ m (Fin.last (N m)) = T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun m => quadraticVariationClass (τ m)) atTop (𝓝 (clockClass T)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun m => ‖quadraticVariationClass (τ m)-clockClass T‖^2) atTop (𝓝 0) := by
    simp_rw [class_error_norm]
    exact quadraticVariation_meanSquare_tendsto T N τ hτ h0 hT hmesh
  have hr := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hr

/-- A concrete ACTUAL family, with n+1 equal original source-clock cells;
there is no assumed zero-mesh sequence or resampled source. -/
def uniformClock (T : ℝ≥0) (n : ℕ) : Fin (n+2) → ℝ≥0 :=
  fun i => (i : ℕ)*T/(n+1 : ℕ)

theorem uniformClock_mono (T : ℝ≥0) (n : ℕ) : Monotone (uniformClock T n) := by
  intro i j hij
  unfold uniformClock
  gcongr
  exact_mod_cast hij

theorem uniformClock_zero (T : ℝ≥0) (n : ℕ) : uniformClock T n 0 = 0 := by simp [uniformClock]

theorem uniformClock_end (T : ℝ≥0) (n : ℕ) : uniformClock T n (Fin.last (n+1)) = T := by
  simp only [uniformClock,Fin.val_last]
  have hn : ((n+1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
  exact mul_div_cancel_left₀ T hn

private theorem uniformClock_gap (T : ℝ≥0) (n : ℕ) (i : Fin (n+1)) :
    uniformClock T n i.succ-uniformClock T n i.castSucc = T/(n+1 : ℕ) := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub ((uniformClock_mono T n) (show i.castSucc ≤ i.succ by exact_mod_cast Nat.le_succ (i : ℕ)))]
  simp only [uniformClock,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,Fin.val_succ,Fin.val_castSucc]
  push_cast
  ring

theorem uniformClock_mesh (T : ℝ≥0) (n : ℕ) : mesh (uniformClock T n) = T/(n+1 : ℕ) := by
  simp only [mesh,uniformClock_gap]
  apply le_antisymm (Finset.sup_le (fun _ _ => le_rfl))
  exact Finset.le_sup (f := fun _ : Fin (n+1) => T/(n+1 : ℕ)) (Finset.mem_univ 0)

theorem uniformClock_mesh_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (mesh (uniformClock T n) : ℝ)) atTop (𝓝 0) := by
  simp only [uniformClock_mesh,NNReal.coe_div,NNReal.coe_natCast]
  have h : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero.comp h).const_mul (T : ℝ)

/-- Concrete nonzero-noise quadratic variation, with T=0 handled by the same
source family and T>0 giving the actual nonzero clock limit. -/
theorem uniformQuadraticVariationClass_tendsto (T : ℝ≥0) :
    Tendsto (fun n => quadraticVariationClass (uniformClock T n)) atTop (𝓝 (clockClass T)) :=
  quadraticVariationClass_tendsto T (fun n => n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariation
