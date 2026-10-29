import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorOneStepIntegral

/-!
Original commitment: finite-dimensional causal control must combine actual vector-noise increments with past-only coefficients.
Existing result: actual product-source vector projection, whole-joint-past conditional moments and Euclidean one-step energy.
Premise reduced: derive cross-time orthogonality and finite predictable vector-noise projection energy, not assumed fields.
Model/witness: every finite d/clock, including zero dimensions, empty clocks and repeats; bounded weights read whole joint START past.
Consumer: later native predictable L2 vector-noise extension; full construction, Ito and Girsanov are not asserted.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorSimplePredictableIntegral
open MeasureTheory ProbabilityTheory
open BrownianFiniteProductSource BrownianVectorOneStepIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Orthogonality uses the first output's genuine END-time measurability and
the second output's START-time conditional mean zero. -/
theorem nonoverlap_orthogonal {d : ℕ} {H K : Fin d → Sample d → ℝ} (s t u v : ℝ≥0)
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (hHpast : ∀ k, StronglyMeasurable[(jointNaturalFiltration d) s] (H k)) (hKpast : ∀ k, StronglyMeasurable[(jointNaturalFiltration d) u] (K k))
    (hH : ∀ k, MemLp (H k) ∞ (productLaw d)) (hK : ∀ k, MemLp (K k) ∞ (productLaw d)) :
    (∫ ω, oneStep d H s t ω * oneStep d K u v ω ∂(productLaw d)) = 0 := by
  have hi : Integrable (oneStep d H s t * oneStep d K u v) (productLaw d) :=
    (oneStep_memLp_two hH s t).integrable_mul (oneStep_memLp_two hK u v)
  have hm : StronglyMeasurable[(jointNaturalFiltration d) u] (oneStep d H s t) :=
    (oneStep_stronglyMeasurable_end s t hst hHpast).mono ((jointNaturalFiltration d).mono htu)
  have hc := condExp_mul_of_stronglyMeasurable_left hm hi ((oneStep_memLp_two hK u v).integrable (by norm_num))
  have hz : (productLaw d)[oneStep d H s t * oneStep d K u v | (jointNaturalFiltration d) u] =ᵐ[(productLaw d)] fun _ => 0 := by
    apply hc.trans
    filter_upwards [oneStep_condExp_zero u v huv hKpast hK] with ω hω
    simp only [Pi.mul_apply,hω,mul_zero]
  simp only [Pi.mul_def] at hz
  rw [← integral_condExp ((jointNaturalFiltration d).le u)]
  rw [integral_congr_ae hz,integral_zero]

/-- The actual output on a finite deterministic clock partition. Repeated
partition times are allowed; their source increment and energy are zero. -/
def simpleIntegral (d : ℕ) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → Fin d → Sample d → ℝ)
    (ω : Sample d) : ℝ :=
  ∑ i : Fin n, oneStep d (H i) (τ i.castSucc) (τ i.succ) ω

theorem simpleIntegral_memLp_two {d n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → Fin d → Sample d → ℝ)
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    MemLp (simpleIntegral d τ H) 2 (productLaw d) := by
  exact memLp_finsetSum Finset.univ (fun i _ => oneStep_memLp_two (hH i) _ _)

private theorem partition_order {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hτ (by exact_mod_cast Nat.le_succ (i : ℕ))

/-- The literal finite output is measurable at its actual final clock time. -/
theorem simpleIntegral_stronglyMeasurable_end {d n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (hτ : Monotone τ)
    (hHpast : ∀ i k, StronglyMeasurable[(jointNaturalFiltration d) (τ i.castSucc)] (H i k)) :
    StronglyMeasurable[(jointNaturalFiltration d) (τ (Fin.last n))] (simpleIntegral d τ H) := by
  have h := Finset.stronglyMeasurable_sum Finset.univ (fun i _ =>
    (oneStep_stronglyMeasurable_end _ _ (partition_order τ hτ i) (hHpast i)).mono
      ((jointNaturalFiltration d).mono (hτ (Fin.le_last i.succ))))
  convert! h using 1
  ext ω
  simp only [simpleIntegral,Finset.sum_apply]

/-- Every off-diagonal term is derived zero for this actual partition and
these actual permitted coefficients; orthogonality is not an input field. -/
theorem partition_cross_orthogonal {d n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → Fin d → Sample d → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i k, StronglyMeasurable[(jointNaturalFiltration d) (τ i.castSucc)] (H i k))
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) (i j : Fin n) (hij : i ≠ j) :
    (∫ ω, oneStep d (H i) (τ i.castSucc) (τ i.succ) ω *
      oneStep d (H j) (τ j.castSucc) (τ j.succ) ω ∂(productLaw d)) = 0 := by
  have ho (a b : Fin n) (hab : a < b) :
      (∫ ω, oneStep d (H a) (τ a.castSucc) (τ a.succ) ω *
        oneStep d (H b) (τ b.castSucc) (τ b.succ) ω ∂(productLaw d)) = 0 := by
    apply nonoverlap_orthogonal _ _ _ _ (partition_order τ hτ a) ?_ (partition_order τ hτ b)
      (hHpast a) (hHpast b) (hH a) (hH b)
    exact hτ (by exact_mod_cast Nat.succ_le_of_lt hab)
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ho i j hij
  · simpa only [mul_comm] using ho j i hji

/-- Actual finite simple-predictable integral has zero expectation. -/
theorem simpleIntegral_mean_zero {d n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → Fin d → Sample d → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i k, StronglyMeasurable[(jointNaturalFiltration d) (τ i.castSucc)] (H i k))
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    (∫ ω, simpleIntegral d τ H ω ∂(productLaw d)) = 0 := by
  change (∫ ω, ∑ i : Fin n, oneStep d (H i) (τ i.castSucc) (τ i.succ) ω ∂(productLaw d)) = 0
  rw [integral_finsetSum Finset.univ (fun i _ => (oneStep_memLp_two (hH i) _ _).integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun i _ => oneStep_mean_zero _ _ (partition_order τ hτ i) (hHpast i) (hH i))

/-- Exact finite-partition predictable Ito isometry, with each ACTUAL source
elapsed time and coefficient. It does not assert completion to general integrands. -/
theorem simpleIntegral_isometry {d n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → Fin d → Sample d → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i k, StronglyMeasurable[(jointNaturalFiltration d) (τ i.castSucc)] (H i k))
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) :
    (∫ ω, simpleIntegral d τ H ω ^ 2 ∂(productLaw d)) =
      ∑ i : Fin n, ((τ i.succ : ℝ)-(τ i.castSucc : ℝ)) * (∫ ω, ‖coefficient d (H i) ω‖ ^ 2 ∂(productLaw d)) := by
  let Y (i : Fin n) := oneStep d (H i) (τ i.castSucc) (τ i.succ)
  have hi (i j : Fin n) : Integrable (fun ω => Y i ω * Y j ω) (productLaw d) :=
    (oneStep_memLp_two (hH i) _ _).integrable_mul (oneStep_memLp_two (hH j) _ _)
  have he : (fun ω => simpleIntegral d τ H ω ^ 2) =
      (fun ω => ∑ i : Fin n, ∑ j : Fin n, Y i ω * Y j ω) := by
    funext ω
    simp only [simpleIntegral,pow_two,Fintype.sum_mul_sum,Y]
  rw [he,integral_finsetSum Finset.univ (f := fun i ω => ∑ j : Fin n, Y i ω * Y j ω)
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j),Finset.sum_eq_single i]
  · simpa only [← pow_two] using oneStep_isometry (τ i.castSucc) (τ i.succ)
      (partition_order τ hτ i) (hHpast i) (hH i)
  · intro j _ hji
    exact partition_cross_orthogonal τ H hτ hHpast hH i j hji.symm
  · simp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorSimplePredictableIntegral
