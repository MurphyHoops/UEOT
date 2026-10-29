import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOneStepIntegral

/-!
Original commitment: causal finite control must combine actual source increments with past-only coefficients.
Existing result: same-source one-step conditional moments, L2 output and exact elapsed-time isometry.
Premise reduced: derive cross-term orthogonality and finite simple-predictable integration isometry.
Model/witness: every finite deterministic nondecreasing clock partition; bounded coefficient i sees only time i's past.
Consumer: minimal L2 predictable extension interface; general stochastic integration/Ito/Girsanov remain open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSimplePredictableIntegral
open MeasureTheory ProbabilityTheory
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource BrownianOneStepIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Orthogonality uses the first output's genuine END-time measurability and
the second output's START-time conditional mean zero. -/
theorem nonoverlap_orthogonal {H K : (ℝ≥0 → ℝ) → ℝ} (s t u v : ℝ≥0)
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (hHpast : StronglyMeasurable[naturalFiltration s] H) (hKpast : StronglyMeasurable[naturalFiltration u] K)
    (hH : MemLp H ∞ sourceLaw) (hK : MemLp K ∞ sourceLaw) :
    (∫ ω, oneStep H s t ω * oneStep K u v ω ∂sourceLaw) = 0 := by
  have hi : Integrable (oneStep H s t * oneStep K u v) sourceLaw :=
    (oneStep_memLp_two hH s t).integrable_mul (oneStep_memLp_two hK u v)
  have hm : StronglyMeasurable[naturalFiltration u] (oneStep H s t) :=
    (oneStep_stronglyMeasurable_end s t hst hHpast).mono (naturalFiltration.mono htu)
  have hc := condExp_mul_of_stronglyMeasurable_left hm hi (oneStep_integrable hK u v)
  have hz : sourceLaw[oneStep H s t * oneStep K u v | naturalFiltration u] =ᵐ[sourceLaw] fun _ => 0 := by
    apply hc.trans
    filter_upwards [oneStep_condExp_zero u v huv hKpast hK] with ω hω
    simp only [Pi.mul_apply,hω,mul_zero]
  simp only [Pi.mul_def] at hz
  rw [← integral_condExp (naturalFiltration.le u)]
  rw [integral_congr_ae hz,integral_zero]

/-- The actual output on a finite deterministic clock partition. Repeated
partition times are allowed; their source increment and energy are zero. -/
def simpleIntegral {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin n, oneStep (H i) (τ i.castSucc) (τ i.succ) ω

theorem simpleIntegral_memLp_two {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    MemLp (simpleIntegral τ H) 2 sourceLaw := by
  exact memLp_finsetSum Finset.univ (fun i _ => oneStep_memLp_two (hH i) _ _)

private theorem partition_order {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hτ (by exact_mod_cast Nat.le_succ (i : ℕ))

/-- The literal finite output is measurable at its actual final clock time. -/
theorem simpleIntegral_stronglyMeasurable_end {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (hτ : Monotone τ)
    (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i)) :
    StronglyMeasurable[naturalFiltration (τ (Fin.last n))] (simpleIntegral τ H) := by
  have h := Finset.stronglyMeasurable_sum Finset.univ (fun i _ =>
    (oneStep_stronglyMeasurable_end _ _ (partition_order τ hτ i) (hHpast i)).mono
      (naturalFiltration.mono (hτ (Fin.le_last i.succ))))
  convert! h using 1
  ext ω
  simp only [simpleIntegral,Finset.sum_apply]

/-- Every off-diagonal term is derived zero for this actual partition and
these actual permitted coefficients; orthogonality is not an input field. -/
theorem partition_cross_orthogonal {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) (i j : Fin n) (hij : i ≠ j) :
    (∫ ω, oneStep (H i) (τ i.castSucc) (τ i.succ) ω *
      oneStep (H j) (τ j.castSucc) (τ j.succ) ω ∂sourceLaw) = 0 := by
  have ho (a b : Fin n) (hab : a < b) :
      (∫ ω, oneStep (H a) (τ a.castSucc) (τ a.succ) ω *
        oneStep (H b) (τ b.castSucc) (τ b.succ) ω ∂sourceLaw) = 0 := by
    apply nonoverlap_orthogonal _ _ _ _ (partition_order τ hτ a) ?_ (partition_order τ hτ b)
      (hHpast a) (hHpast b) (hH a) (hH b)
    exact hτ (by exact_mod_cast Nat.succ_le_of_lt hab)
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ho i j hij
  · simpa only [mul_comm] using ho j i hji

/-- Actual finite simple-predictable integral has zero expectation. -/
theorem simpleIntegral_mean_zero {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    (∫ ω, simpleIntegral τ H ω ∂sourceLaw) = 0 := by
  change (∫ ω, ∑ i : Fin n, oneStep (H i) (τ i.castSucc) (τ i.succ) ω ∂sourceLaw) = 0
  rw [integral_finsetSum Finset.univ (fun i _ => oneStep_integrable (hH i) _ _)]
  exact Finset.sum_eq_zero (fun i _ => oneStep_mean_zero _ _ (partition_order τ hτ i) (hHpast i) (hH i))

/-- Exact finite-partition predictable Ito isometry, with each ACTUAL source
elapsed time and coefficient. It does not assert completion to general integrands. -/
theorem simpleIntegral_isometry {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (H : Fin n → (ℝ≥0 → ℝ) → ℝ)
    (hτ : Monotone τ) (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) :
    (∫ ω, simpleIntegral τ H ω ^ 2 ∂sourceLaw) =
      ∑ i : Fin n, ((τ i.succ : ℝ)-(τ i.castSucc : ℝ)) * (∫ ω, H i ω ^ 2 ∂sourceLaw) := by
  let Y (i : Fin n) := oneStep (H i) (τ i.castSucc) (τ i.succ)
  have hi (i j : Fin n) : Integrable (fun ω => Y i ω * Y j ω) sourceLaw :=
    (oneStep_memLp_two (hH i) _ _).integrable_mul (oneStep_memLp_two (hH j) _ _)
  have he : (fun ω => simpleIntegral τ H ω ^ 2) =
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
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSimplePredictableIntegral
