import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianCommonRefinement

/-!
Original commitment: the actual returned stochastic integral must be independent of its input representation.
Existing result: explicit time-source L2 classes and constructed common refinement preserve both literal inputs and outputs.
Premise reduced: prove common-cell energy and derive actual output equality from equality of native input classes.
Model/witness: SAME source; any two finite deterministic [0,T] partitions and bounded left-past coefficients.
Consumer: native continuous isometric extension on the elementary L2 closure; general predictable density stays open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralRepresentation
open MeasureTheory ProbabilityTheory Set
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource
open BrownianOneStepIntegral BrownianSimplePredictableIntegral BrownianTimeIntegrand BrownianCommonRefinement
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem cell_order {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hτ (by exact_mod_cast Nat.le_succ (i : ℕ))

/-- The actual common intervals are pairwise nonoverlapping, even when
repeated original times generate collapsed cells. -/
theorem commonCell_nonoverlap {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (q r : Fin n × Fin m) (hqr : q ≠ r) :
    commonEnd τ σ q.1 q.2 ≤ commonStart τ σ r.1 r.2 ∨
      commonEnd τ σ r.1 r.2 ≤ commonStart τ σ q.1 q.2 := by
  have ho (i k : Fin n) (j l : Fin m) (hik : i < k) :
      commonEnd τ σ i j ≤ commonStart τ σ k l :=
    (clamp_bounds _ _ _ (cell_order τ hτ i)).2.trans
      ((hτ (by exact_mod_cast Nat.succ_le_of_lt hik)).trans (le_max_left _ _))
  rcases lt_trichotomy q.1 r.1 with h | h | h
  · exact Or.inl (ho _ _ _ _ h)
  · have hj : q.2 ≠ r.2 := by intro he; apply hqr; exact Prod.ext h he
    rcases lt_or_gt_of_ne hj with hj | hj
    · left
      rw [h]
      exact clamp_mono _ _ (hσ (by exact_mod_cast Nat.succ_le_of_lt hj))
    · right
      rw [h]
      exact clamp_mono _ _ (hσ (by exact_mod_cast Nat.succ_le_of_lt hj))
  · exact Or.inr (ho _ _ _ _ h)

private theorem finite_square_energy {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : Measure α) (Y : ι → α → ℝ)
    (hY : ∀ i, MemLp (Y i) 2 μ)
    (hcross : ∀ i j, i ≠ j → (∫ a, Y i a * Y j a ∂μ) = 0) :
    (∫ a, (∑ i, Y i a)^2 ∂μ) = ∑ i, ∫ a, Y i a ^ 2 ∂μ := by
  simp_rw [pow_two,Fintype.sum_mul_sum]
  rw [integral_finsetSum Finset.univ (f := fun i a => ∑ j, Y i a * Y j a)
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => (hY i).integrable_mul (hY j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (f := fun j a => Y i a * Y j a)
    (fun j _ => (hY i).integrable_mul (hY j)),Finset.sum_eq_single i]
  · intro j _ hji
    exact hcross i j hji.symm
  · simp

private theorem interval_products_zero {H K : (ℝ≥0 → ℝ) → ℝ} (s t u v : ℝ≥0)
    (h : t ≤ u ∨ v ≤ s) (p : ℝ × (ℝ≥0 → ℝ)) :
    intervalIntegrand H s t p * intervalIntegrand K u v p = 0 := by
  have hd : ¬ (p.1 ∈ Ioc (s : ℝ) (t : ℝ) ∧ p.1 ∈ Ioc (u : ℝ) (v : ℝ)) := by
    intro hp
    rcases h with h | h
    · have hc : (t : ℝ) ≤ (u : ℝ) := by exact_mod_cast h
      exact (not_lt_of_ge (hp.1.2.trans hc)) hp.2.1
    · have hc : (v : ℝ) ≤ (s : ℝ) := by exact_mod_cast h
      exact (not_lt_of_ge (hp.2.2.trans hc)) hp.1.1
  by_cases hs : p.1 ∈ Ioc (s : ℝ) (t : ℝ)
  · have hu : p.1 ∉ Ioc (u : ℝ) (v : ℝ) := fun hu => hd ⟨hs,hu⟩
    simp [intervalIntegrand,hu]
  · simp [intervalIntegrand,hs]

/-- Common-cell exact isometry consumes the same coefficients whose start
permissions were proved by the construction. Orthogonality is derived here. -/
theorem refined_isometry {n m : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (hτT : τ (Fin.last n) ≤ T)
    (G : Fin n → Fin m → (ℝ≥0 → ℝ) → ℝ)
    (hGpast : ∀ i j, StronglyMeasurable[naturalFiltration (commonStart τ σ i j)] (G i j))
    (hG : ∀ i j, MemLp (G i j) ∞ sourceLaw) :
    (∫ ω, refinedOutput τ σ G ω ^ 2 ∂sourceLaw) =
      ∫ p, refinedInput τ σ G p ^ 2 ∂inputLaw T := by
  let A (q : Fin n × Fin m) := commonStart τ σ q.1 q.2
  let B (q : Fin n × Fin m) := commonEnd τ σ q.1 q.2
  let C (q : Fin n × Fin m) := G q.1 q.2
  let Y q := oneStep (C q) (A q) (B q)
  let Z q := intervalIntegrand (C q) (A q) (B q)
  have hAB q : A q ≤ B q := commonCell_order τ σ hσ q.1 q.2
  have hBT q : B q ≤ T :=
    (clamp_bounds _ _ _ (cell_order τ hτ q.1)).2.trans ((hτ (Fin.le_last q.1.succ)).trans hτT)
  have hY q : MemLp (Y q) 2 sourceLaw := oneStep_memLp_two (hG q.1 q.2) _ _
  have hZ q : MemLp (Z q) 2 (inputLaw T) := intervalIntegrand_memLp_two (hG q.1 q.2) T _ _
  have hYo q r (hqr : q ≠ r) : (∫ ω, Y q ω * Y r ω ∂sourceLaw) = 0 := by
    rcases commonCell_nonoverlap τ σ hτ hσ q r hqr with h | h
    · exact nonoverlap_orthogonal _ _ _ _ (hAB q) h (hAB r)
        (hGpast q.1 q.2) (hGpast r.1 r.2) (hG q.1 q.2) (hG r.1 r.2)
    · simpa only [mul_comm] using nonoverlap_orthogonal _ _ _ _ (hAB r) h (hAB q)
        (hGpast r.1 r.2) (hGpast q.1 q.2) (hG r.1 r.2) (hG q.1 q.2)
  have hZo q r (hqr : q ≠ r) : (∫ p, Z q p * Z r p ∂inputLaw T) = 0 := by
    have hz p : Z q p * Z r p = 0 :=
      interval_products_zero _ _ _ _ (commonCell_nonoverlap τ σ hτ hσ q r hqr) p
    simp_rw [hz]
    exact integral_zero _ _
  have heY : refinedOutput τ σ G = fun ω => ∑ q : Fin n × Fin m, Y q ω := by
    funext ω
    simp only [refinedOutput,Fintype.sum_prod_type,Y,C,A,B]
  have heZ : refinedInput τ σ G = fun p => ∑ q : Fin n × Fin m, Z q p := by
    funext p
    simp only [refinedInput,Fintype.sum_prod_type,Z,C,A,B]
  rw [heY,heZ,finite_square_energy sourceLaw Y hY hYo,finite_square_energy (inputLaw T) Z hZ hZo]
  apply Finset.sum_congr rfl
  intro q _
  rw [oneStep_isometry _ _ (hAB q) (hGpast q.1 q.2) (hG q.1 q.2),
    intervalIntegrand_energy (C q) T _ _ (hAB q) (hBT q)]

/-- Different partitions representing the SAME native L2 input return the
SAME actual output a.e.; no independently chosen strategy/output is introduced. -/
theorem output_ae_eq_of_inputClass_eq {n m : ℕ} (T : ℝ≥0)
    (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hKpast : ∀ j, StronglyMeasurable[naturalFiltration (σ j.castSucc)] (K j))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) (hK : ∀ j, MemLp (K j) ∞ sourceLaw)
    (heq : inputClass T τ H hH = inputClass T σ K hK) :
    simpleIntegral τ H =ᵐ[sourceLaw] simpleIntegral σ K := by
  have hleft : (inputClass T τ H hH : (ℝ × (ℝ≥0 → ℝ)) → ℝ) =ᵐ[inputLaw T] integrand τ H :=
    (integrand_memLp_two T τ H hH).coeFn_toLp
  have hright : (inputClass T σ K hK : (ℝ × (ℝ≥0 → ℝ)) → ℝ) =ᵐ[inputLaw T] integrand σ K :=
    (integrand_memLp_two T σ K hK).coeFn_toLp
  rw [heq] at hleft
  have hinput := hleft.symm.trans hright
  let G := commonDifference τ σ H K
  have hz : refinedInput τ σ G =ᵐ[inputLaw T] fun _ => 0 := by
    filter_upwards [hinput] with p hp
    rw [refinedInput_difference τ σ T hτ hσ hτ0 hσ0 hτT hσT H K p,hp,sub_self]
  have henergy : (∫ ω, refinedOutput τ σ G ω ^ 2 ∂sourceLaw) = 0 := by
    rw [refined_isometry T τ σ hτ hσ hτT.le G
      (commonDifference_permission τ σ hτ hσ H K hHpast hKpast)
      (commonDifference_bounded τ σ H K hH hK)]
    have hsq : (fun p => refinedInput τ σ G p ^ 2) =ᵐ[inputLaw T] fun _ => 0 := by
      filter_upwards [hz] with p hp
      rw [hp]
      norm_num
    rw [integral_congr_ae hsq,integral_zero]
  have hdiff : (∫ ω, (simpleIntegral τ H ω-simpleIntegral σ K ω)^2 ∂sourceLaw) = 0 := by
    dsimp only [G] at henergy
    simpa only [refinedOutput_difference τ σ T hτ hσ hτ0 hσ0 hτT hσT H K] using henergy
  have hi := ((simpleIntegral_memLp_two τ H hH).sub (simpleIntegral_memLp_two σ K hK)).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (fun ω =>
    sq_nonneg (simpleIntegral τ H ω-simpleIntegral σ K ω))) hi).mp hdiff
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

/-- Representation independence in the original native source L2 space. -/
theorem outputClass_eq_of_inputClass_eq {n m : ℕ} (T : ℝ≥0)
    (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hKpast : ∀ j, StronglyMeasurable[naturalFiltration (σ j.castSucc)] (K j))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) (hK : ∀ j, MemLp (K j) ∞ sourceLaw)
    (heq : inputClass T τ H hH = inputClass T σ K hK) : outputClass τ H hH = outputClass σ K hK := by
  apply Lp.ext
  exact (simpleIntegral_memLp_two τ H hH).coeFn_toLp.trans
    ((output_ae_eq_of_inputClass_eq T τ σ hτ hσ hτ0 hσ0 hτT hσT H K hHpast hKpast hH hK heq).trans
      (simpleIntegral_memLp_two σ K hK).coeFn_toLp.symm)

private theorem toLp_difference_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f-hg.toLp g‖ ^ 2 = ∫ a, (f a-g a)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp] with a ha hf hg
  simp only [Pi.sub_apply] at ha
  rw [ha,hf,hg]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- Stronger than zero-class uniqueness: the actual input-to-output mapping
preserves ALL native L2 distances across different deterministic partitions. -/
theorem input_output_distance {n m : ℕ} (T : ℝ≥0)
    (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (hHpast : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hKpast : ∀ j, StronglyMeasurable[naturalFiltration (σ j.castSucc)] (K j))
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) (hK : ∀ j, MemLp (K j) ∞ sourceLaw) :
    dist (outputClass τ H hH) (outputClass σ K hK) =
      dist (inputClass T τ H hH) (inputClass T σ K hK) := by
  rw [dist_eq_norm,dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [outputClass,outputClass,inputClass,inputClass,toLp_difference_norm_sq,toLp_difference_norm_sq]
  have h := refined_isometry T τ σ hτ hσ hτT.le (commonDifference τ σ H K)
    (commonDifference_permission τ σ hτ hσ H K hHpast hKpast)
    (commonDifference_bounded τ σ H K hH hK)
  simpa only [refinedOutput_difference τ σ T hτ hσ hτ0 hσ0 hτT hσT H K,
    refinedInput_difference τ σ T hτ hσ hτ0 hσ0 hτT hσT H K] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralRepresentation
