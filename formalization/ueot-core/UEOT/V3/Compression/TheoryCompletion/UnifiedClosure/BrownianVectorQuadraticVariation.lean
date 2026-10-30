import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorQuadraticVariationSteps
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariation

/-!
Original commitment: SAME vector literal table requires an actual mesh-controlled quadratic-energy error, not desired QV.
Existing result: derived joint-past coordinate-product moments/weighted temporal orthogonality and actual full-input L1 stability.
Premise reduced: combine actual bounded finite table errors into a vanishing-mesh mean-square bound under SAME product source.
Model: finite d including0, original jointNaturalFiltration and deterministic monotone clocks with repeats; uniform bounds remain source-a.e.
Consumer: actual literal input/path binding then full-input vector-noise QV by native density; no state Ito/SDE or random partitions claimed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorQuadraticVariation
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorQuadraticVariationSteps BrownianVectorOneStepIntegral
open BrownianQuadraticVariation (mesh)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ) (k l : Fin d)

/-- Actual finite error, retaining the original clock and permitted weights. -/
def errorSum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (Sample d) → ℝ) (ω : Sample d) : ℝ :=
  ∑ i : Fin n, weightedError d k l (H i) (τ i.castSucc) (τ i.succ) ω

theorem errorSum_memLp_two {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (Sample d) → ℝ)
    (hH : ∀ i, MemLp (H i) ∞ (productLaw d)) : MemLp (errorSum d k l τ H) 2 (productLaw d) :=
  memLp_finsetSum Finset.univ (fun i _ => weightedError_memLp_two d k l (hH i) _ _)

private theorem clock_order {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hτ (by exact_mod_cast Nat.le_succ (i : ℕ))

private theorem error_cross {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (Sample d) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[(jointNaturalFiltration d) (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ (productLaw d)) (i j : Fin n) (hij : i ≠ j) :
    (∫ ω, weightedError d k l (H i) (τ i.castSucc) (τ i.succ) ω *
      weightedError d k l (H j) (τ j.castSucc) (τ j.succ) ω ∂(productLaw d)) = 0 := by
  have ho (a b : Fin n) (hab : a < b) :
      (∫ ω, weightedError d k l (H a) (τ a.castSucc) (τ a.succ) ω *
        weightedError d k l (H b) (τ b.castSucc) (τ b.succ) ω ∂(productLaw d)) = 0 := by
    exact weightedError_nonoverlap d k l k l _ _ _ _ (clock_order τ hτ a)
      (hτ (by exact_mod_cast Nat.succ_le_of_lt hab)) (clock_order τ hτ b)
      (hHpast a) (hHpast b) (hH a) (hH b)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ho i j h
  · simpa only [mul_comm] using ho j i h

/-- Exact weighted quadratic-variation error energy from actual Gaussian
fourth moments and causal orthogonality; covariance is not an input field. -/
theorem errorSum_variance {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (Sample d) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[(jointNaturalFiltration d) (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ (productLaw d)) :
    (∫ ω, errorSum d k l τ H ω ^ 2 ∂(productLaw d)) =
      ∑ i : Fin n, ((if k=l then 2 else 1)*((τ i.succ : ℝ)-(τ i.castSucc : ℝ))^2) * (∫ ω, H i ω ^ 2 ∂(productLaw d)) := by
  let Y (i : Fin n) := weightedError d k l (H i) (τ i.castSucc) (τ i.succ)
  have hi (i j : Fin n) : Integrable (fun ω => Y i ω * Y j ω) (productLaw d) :=
    (weightedError_memLp_two d k l (hH i) _ _).integrable_mul (weightedError_memLp_two d k l (hH j) _ _)
  have he : (fun ω => errorSum d k l τ H ω ^ 2) =
      (fun ω => ∑ i : Fin n, ∑ j : Fin n, Y i ω * Y j ω) := by
    ext ω
    simp only [errorSum,pow_two,Fintype.sum_mul_sum,Y]
  rw [he,integral_finsetSum Finset.univ (f := fun i ω => ∑ j : Fin n, Y i ω * Y j ω)
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j),Finset.sum_eq_single i]
  · simpa only [← pow_two] using weightedError_variance d k l _ _ (clock_order τ hτ i) (hHpast i) (hH i)
  · intro j _ hji
    exact error_cross d k l τ H hτ hHpast hH i j hji.symm
  · simp


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


theorem errorSum_mesh_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (Sample d) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[(jointNaturalFiltration d) (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ (productLaw d)) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ i, ∀ᵐ ω ∂(productLaw d), |H i ω| ≤ K) :
    (∫ ω, errorSum d k l τ H ω ^ 2 ∂(productLaw d)) ≤
      2*K^2*(mesh τ : ℝ)*((τ (Fin.last n) : ℝ)-(τ 0 : ℝ)) := by
  have hsq (i : Fin n) : (∫ ω, H i ω ^ 2 ∂(productLaw d)) ≤ K^2 := by
    have hi : Integrable (fun ω => H i ω ^ 2) (productLaw d) :=
      ((hH i).mono_exponent (show (2 : ℝ≥0∞) ≤ ∞ from le_top)).integrable_sq
    have hm : (∫ ω, H i ω ^ 2 ∂(productLaw d)) ≤ ∫ _ω : Sample d, K^2 ∂(productLaw d) :=
      integral_mono_ae hi (integrable_const _) ((hbound i).mono (fun ω hω => by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr hω))
    simpa only [integral_const,probReal_univ,one_smul] using hm
  rw [errorSum_variance d k l τ H hτ hHpast hH,← sum_gaps,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hg : (0 : ℝ) ≤ (τ i.succ : ℝ)-(τ i.castSucc : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast clock_order τ hτ i)
  calc
    _ ≤ ((if k=l then 2 else 1)*((τ i.succ : ℝ)-(τ i.castSucc : ℝ))^2)*K^2 :=
      mul_le_mul_of_nonneg_left (hsq i) (by split_ifs <;> positivity)
    _ ≤ (2*((τ i.succ : ℝ)-(τ i.castSucc : ℝ))^2)*K^2 := by
      split_ifs <;> nlinarith [sq_nonneg ((τ i.succ : ℝ)-(τ i.castSucc : ℝ)),sq_nonneg K]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right (gap_le_mesh τ hτ i) hg
      nlinarith [sq_nonneg K]


/-- Actual entire vector table error, retaining every coordinate pair and
original row coefficient. No independent error/covariance source is supplied. -/
def matrixErrorSum {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (H : Fin n→Fin d→Sample d→ℝ) (ω : Sample d) : ℝ :=
  ∑ p : Fin d×Fin d, errorSum d p.1 p.2 τ (fun r ω=>H r p.1 ω*H r p.2 ω) ω

theorem matrixErrorSum_memLp_two {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (H : Fin n→Fin d→Sample d→ℝ)
    (hH : ∀ r i, MemLp (H r i) ∞ (productLaw d)) :
    MemLp (matrixErrorSum d τ H) 2 (productLaw d) :=
  memLp_finsetSum Finset.univ (fun p _=>errorSum_memLp_two d p.1 p.2 τ _
    (fun r=>(hH r p.2).mul (hH r p.1)))

/-- Honest dimension-dependent (not necessarily sharp) source error bound.
Coefficient bounds remain SAME-source AE; they are never changed to forall ω. -/
theorem matrixErrorSum_mesh_bound {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (H : Fin n→Fin d→Sample d→ℝ)
    (hτ : Monotone τ) (hHpast : ∀ r i, StronglyMeasurable[jointNaturalFiltration d (τ r.castSucc)] (H r i))
    (hH : ∀ r i, MemLp (H r i) ∞ (productLaw d)) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ r i, ∀ᵐ ω ∂productLaw d, |H r i ω|≤K) :
    (∫ ω,matrixErrorSum d τ H ω^2 ∂productLaw d) ≤
      2*(d : ℝ)^4*K^4*(mesh τ : ℝ)*((τ (Fin.last n) : ℝ)-(τ 0 : ℝ)) := by
  let P := Fin d×Fin d
  have hcard : Fintype.card P=d*d := by simp [P]
  let Y (p : P) := errorSum d p.1 p.2 τ (fun r ω=>H r p.1 ω*H r p.2 ω)
  let B := 2*(K^2)^2*(mesh τ : ℝ)*((τ (Fin.last n) : ℝ)-(τ 0 : ℝ))
  have hY (p : P) : MemLp (Y p) 2 (productLaw d) :=
    errorSum_memLp_two d p.1 p.2 τ _ (fun r=>(hH r p.2).mul (hH r p.1))
  have hb (p : P) : (∫ ω,Y p ω^2 ∂productLaw d)≤B := by
    apply errorSum_mesh_bound d p.1 p.2 τ _ hτ
      (fun r=>(hHpast r p.1).mul (hHpast r p.2))
      (fun r=>(hH r p.2).mul (hH r p.1)) (K^2) (sq_nonneg _)
    intro r
    filter_upwards [hbound r p.1,hbound r p.2] with ω hi hj
    rw [Pi.mul_apply,abs_mul,pow_two]
    exact mul_le_mul hi hj (abs_nonneg _) hK
  have hp (ω : Sample d) : matrixErrorSum d τ H ω^2≤
      (∑ p : P,Y p ω^2)*((d : ℝ)*(d : ℝ)) := by
    have he : matrixErrorSum d τ H ω=∑ p : P,Y p ω := rfl
    rw [he]
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p : P=>Y p ω) (fun _=> (1 : ℝ))
    simpa only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,hcard,
      Nat.cast_mul,nsmul_eq_mul,mul_one] using h
  have hsum : Integrable (fun ω=>∑ p : P,Y p ω^2) (productLaw d) :=
    integrable_finsetSum Finset.univ (fun p _=>(hY p).integrable_sq)
  calc
    _ ≤ ∫ ω,(∑ p : P,Y p ω^2)*((d : ℝ)*(d : ℝ)) ∂productLaw d :=
      integral_mono (matrixErrorSum_memLp_two d τ H hH).integrable_sq (hsum.mul_const _) hp
    _ = (∑ p : P,∫ ω,Y p ω^2 ∂productLaw d)*((d : ℝ)*(d : ℝ)) := by
      rw [integral_mul_const,integral_finsetSum Finset.univ (fun p _=>(hY p).integrable_sq)]
    _ ≤ (∑ _p : P,B)*((d : ℝ)*(d : ℝ)) :=
      mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun p _=>hb p)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,hcard,Nat.cast_mul,nsmul_eq_mul,B]
      ring

/-- Mean-square mesh convergence for the actual bounded row table, whose
coefficients may depend on the partition and ALL joint START information. -/
theorem matrixErrorSum_meanSquare_tendsto (T : ℝ≥0) (N : ℕ→ℕ)
    (τ : (m : ℕ)→Fin (N m+1)→ℝ≥0) (H : (m : ℕ)→Fin (N m)→Fin d→Sample d→ℝ)
    (hτ : ∀ m,Monotone (τ m)) (h0 : ∀ m,τ m 0=0) (hT : ∀ m,τ m (Fin.last (N m))=T)
    (hHpast : ∀ m r i,StronglyMeasurable[jointNaturalFiltration d (τ m r.castSucc)] (H m r i))
    (hH : ∀ m r i,MemLp (H m r i) ∞ (productLaw d)) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ m r i,∀ᵐ ω ∂productLaw d,|H m r i ω|≤K)
    (hmesh : Tendsto (fun m=>(mesh (τ m) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun m=>∫ ω,matrixErrorSum d (τ m) (H m) ω^2 ∂productLaw d) atTop (𝓝 0) := by
  apply squeeze_zero (fun _=>integral_nonneg (fun _=>sq_nonneg _))
  · intro m
    simpa only [h0,hT,NNReal.coe_zero,sub_zero] using
      matrixErrorSum_mesh_bound d (τ m) (H m) (hτ m) (hHpast m) (hH m) K hK (hbound m)
  · simpa only [mul_zero,zero_mul] using (hmesh.const_mul (2*(d : ℝ)^4*K^4)).mul_const (T : ℝ)

/-- One actual vector projection's squared-increment error is LITERALLY the
sum of its actual coordinate-product errors with SAME coefficients. -/
theorem row_product_error_identity (H : Fin d→Sample d→ℝ) (s t : ℝ≥0) (ω : Sample d) :
    (∑ p : Fin d×Fin d,weightedError d p.1 p.2 (fun ω=>H p.1 ω*H p.2 ω) s t ω)=
      oneStep d H s t ω^2-((t : ℝ)-(s : ℝ))*‖coefficient d H ω‖^2 := by
  have hquad : (∑ i : Fin d,∑ j : Fin d,
      H i ω*H j ω*(coordinateIncrement d i s t ω*coordinateIncrement d j s t ω))=oneStep d H s t ω^2 := by
    change _=(∑ i : Fin d,H i ω*coordinateIncrement d i s t ω)^2
    rw [pow_two,Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiag : (∑ i : Fin d,∑ j : Fin d,
      H i ω*H j ω*(if i=j then (t : ℝ)-(s : ℝ) else 0))=
        ((t : ℝ)-(s : ℝ))*‖coefficient d H ω‖^2 := by
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [coefficient_apply]
    ring
  rw [Fintype.sum_prod_type]
  simp only [weightedError,Pi.mul_apply,productError,mul_sub,Finset.sum_sub_distrib]
  rw [hquad,hdiag]

/-- The error sum is the SAME row-by-row actual vector output square sum
minus its SAME actual row-clock Euclidean energy. -/
theorem matrixErrorSum_eq_table {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (H : Fin n→Fin d→Sample d→ℝ) (ω : Sample d) :
    matrixErrorSum d τ H ω=
      ∑ r : Fin n,(oneStep d (H r) (τ r.castSucc) (τ r.succ) ω^2-
        ((τ r.succ : ℝ)-(τ r.castSucc : ℝ))*‖coefficient d (H r) ω‖^2) := by
  simp only [matrixErrorSum,errorSum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _=>row_product_error_identity d (H r) _ _ ω)

/-- Actual literal table squared outputs converge to their SAME literal
clock energy; every parameter/row remains the original executed one. -/
theorem literalTable_quadratic_difference_tendsto (T : ℝ≥0) (N : ℕ→ℕ)
    (τ : (m : ℕ)→Fin (N m+1)→ℝ≥0) (H : (m : ℕ)→Fin (N m)→Fin d→Sample d→ℝ)
    (hτ : ∀ m,Monotone (τ m)) (h0 : ∀ m,τ m 0=0) (hT : ∀ m,τ m (Fin.last (N m))=T)
    (hHpast : ∀ m r i,StronglyMeasurable[jointNaturalFiltration d (τ m r.castSucc)] (H m r i))
    (hH : ∀ m r i,MemLp (H m r i) ∞ (productLaw d)) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ m r i,∀ᵐ ω ∂productLaw d,|H m r i ω|≤K)
    (hmesh : Tendsto (fun m=>(mesh (τ m) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun m=>∫ ω, (∑ r : Fin (N m),
      (oneStep d (H m r) (τ m r.castSucc) (τ m r.succ) ω^2-
        ((τ m r.succ : ℝ)-(τ m r.castSucc : ℝ))*‖coefficient d (H m r) ω‖^2))^2 ∂productLaw d)
      atTop (𝓝 0) := by
  have h := matrixErrorSum_meanSquare_tendsto d T N τ H hτ h0 hT hHpast hH K hK hbound hmesh
  simpa only [matrixErrorSum_eq_table] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorQuadraticVariation
