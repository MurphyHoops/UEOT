import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorTimeInput
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralRepresentation

/-!
Original commitment: actual vector-noise integral output must depend on its native time input, not a chosen partition.
Existing result: actual Euclidean time inputs and source outputs have finite-disjoint-family isometry under SAME joint past.
Premise reduced: derive actual cross-partition common refinement, permissions and native representation independence.
Model/witness: arbitrary finite d and finite deterministic monotone0/T clocks, repeated/empty cells and horizon0 included.
Consumer: native Gram/Finsupp span extension returning SAME original outputs; full predictable density is separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorRepresentation
open MeasureTheory ProbabilityTheory Set
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorSimplePredictableIntegral
open BrownianVectorTimeInput
open BrownianCommonRefinement (clamp clamp_mono clamp_bounds clamp_telescope clamp_difference_symm
  commonStart commonEnd commonCell_order)
open BrownianIntegralRepresentation (commonCell_nonoverlap)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Only the PURE time-indicator identity of the old clock API is used: its
coefficient/readout is constant1, so no old scalar noise/filter is substituted. -/
private theorem indicator_refine {m : ℕ} (σ : Fin (m+1) → ℝ≥0) (hσ : Monotone σ)
    (T s t : ℝ≥0) (h0 : σ 0 = 0) (hT : σ (Fin.last m) = T) (hst : s ≤ t) (htT : t ≤ T) (x : ℝ) :
    (∑ j : Fin m, (Ioc (clamp s t (σ j.castSucc) : ℝ) (clamp s t (σ j.succ) : ℝ)).indicator (fun _ => (1 : ℝ)) x) =
      (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => (1 : ℝ)) x := by
  simpa only [BrownianTimeIntegrand.intervalIntegrand,mul_one] using
    BrownianCommonRefinement.intervalIntegrand_refine σ hσ T s t h0 hT hst htT (fun _ => 1) (x,fun _ => 0)

private theorem indicator_common_symm (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v) (x : ℝ) :
    (Ioc (clamp s t u : ℝ) (clamp s t v : ℝ)).indicator (fun _ => (1 : ℝ)) x =
      (Ioc (clamp u v s : ℝ) (clamp u v t : ℝ)).indicator (fun _ => (1 : ℝ)) x := by
  simpa only [BrownianTimeIntegrand.intervalIntegrand,mul_one] using
    BrownianCommonRefinement.intervalIntegrand_common_symm s t u v hst huv (fun _ => 1) (x,fun _ => 0)

theorem intervalInput_refine {d m : ℕ} (σ : Fin (m+1) → ℝ≥0) (hσ : Monotone σ)
    (T s t : ℝ≥0) (h0 : σ 0 = 0) (hT : σ (Fin.last m) = T) (hst : s ≤ t) (htT : t ≤ T)
    (H : Fin d → Sample d → ℝ) (p : ℝ × Sample d) :
    (∑ j : Fin m, intervalInput d H (clamp s t (σ j.castSucc)) (clamp s t (σ j.succ)) p) =
      intervalInput d H s t p := by
  simp only [intervalInput]
  rw [← Finset.sum_smul,indicator_refine σ hσ T s t h0 hT hst htT]

theorem intervalInput_common_symm {d : ℕ} (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (H : Fin d → Sample d → ℝ) (p : ℝ × Sample d) :
    intervalInput d H (clamp s t u) (clamp s t v) p =
      intervalInput d H (clamp u v s) (clamp u v t) p := by
  simp only [intervalInput,indicator_common_symm s t u v hst huv]

/-- The old PURE clamp telescope is applied to each actual product-source
coordinate readout. It never transports H to an own-coordinate filtration. -/
theorem oneStep_refine {d m : ℕ} (σ : Fin (m+1) → ℝ≥0) (T s t : ℝ≥0)
    (h0 : σ 0 = 0) (hT : σ (Fin.last m) = T) (hst : s ≤ t) (htT : t ≤ T)
    (H : Fin d → Sample d → ℝ) (ω : Sample d) :
    (∑ j : Fin m, oneStep d H (clamp s t (σ j.castSucc)) (clamp s t (σ j.succ)) ω) =
      oneStep d H s t ω := by
  simp only [oneStep,component,Pi.mul_apply,coordinateIncrement]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum,clamp_telescope σ T s t h0 hT hst htT (fun a => coordinate d k a ω)]

theorem oneStep_common_symm {d : ℕ} (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (H : Fin d → Sample d → ℝ) (ω : Sample d) :
    oneStep d H (clamp s t u) (clamp s t v) ω = oneStep d H (clamp u v s) (clamp u v t) ω := by
  simp only [oneStep,component,Pi.mul_apply,coordinateIncrement]
  apply Finset.sum_congr rfl
  intro k _
  rw [clamp_difference_symm s t u v hst huv (fun a => coordinate d k a ω)]

def refinedInput (d : ℕ) {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (G : Fin n → Fin m → Fin d → Sample d → ℝ) (p : ℝ × Sample d) : EuclideanSpace ℝ (Fin d) :=
  ∑ i : Fin n, ∑ j : Fin m, intervalInput d (G i j) (commonStart τ σ i j) (commonEnd τ σ i j) p

def refinedOutput (d : ℕ) {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (G : Fin n → Fin m → Fin d → Sample d → ℝ) (ω : Sample d) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, oneStep d (G i j) (commonStart τ σ i j) (commonEnd τ σ i j) ω

private theorem cell_order {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hτ (by exact_mod_cast Nat.le_succ (i : ℕ))

theorem refinedInput_left {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ) (hσ0 : σ 0 = 0)
    (hσT : σ (Fin.last m) = T) (hτT : τ (Fin.last n) ≤ T)
    (H : Fin n → Fin d → Sample d → ℝ) (p : ℝ × Sample d) :
    refinedInput d τ σ (fun i _ => H i) p = integrand d τ H p := by
  apply Finset.sum_congr rfl
  intro i _
  exact intervalInput_refine σ hσ T _ _ hσ0 hσT (cell_order τ hτ i)
    ((hτ (Fin.le_last i.succ)).trans hτT) (H i) p

theorem refinedOutput_left {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ0 : σ 0 = 0)
    (hσT : σ (Fin.last m) = T) (hτT : τ (Fin.last n) ≤ T)
    (H : Fin n → Fin d → Sample d → ℝ) (ω : Sample d) :
    refinedOutput d τ σ (fun i _ => H i) ω = simpleIntegral d τ H ω := by
  apply Finset.sum_congr rfl
  intro i _
  exact oneStep_refine σ T _ _ hσ0 hσT (cell_order τ hτ i)
    ((hτ (Fin.le_last i.succ)).trans hτT) (H i) ω

theorem refinedInput_right {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ) (hτ0 : τ 0 = 0)
    (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) ≤ T)
    (K : Fin m → Fin d → Sample d → ℝ) (p : ℝ × Sample d) :
    refinedInput d τ σ (fun _ j => K j) p = integrand d σ K p := by
  have he : refinedInput d τ σ (fun _ j => K j) p = refinedInput d σ τ (fun j _ => K j) p := by
    unfold refinedInput
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact intervalInput_common_symm _ _ _ _ (cell_order τ hτ i) (cell_order σ hσ j) (K j) p
  rw [he]
  exact refinedInput_left σ τ T hσ hτ hτ0 hτT hσT K p

theorem refinedOutput_right {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ) (hτ0 : τ 0 = 0)
    (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) ≤ T)
    (K : Fin m → Fin d → Sample d → ℝ) (ω : Sample d) :
    refinedOutput d τ σ (fun _ j => K j) ω = simpleIntegral d σ K ω := by
  have he : refinedOutput d τ σ (fun _ j => K j) ω = refinedOutput d σ τ (fun j _ => K j) ω := by
    unfold refinedOutput
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact oneStep_common_symm _ _ _ _ (cell_order τ hτ i) (cell_order σ hσ j) (K j) ω
  rw [he]
  exact refinedOutput_left σ τ T hσ hτ0 hτT hσT K ω

private theorem positive_other_start (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (hpos : clamp s t u < clamp s t v) : u ≤ clamp s t u := by
  by_cases hut : u ≤ t
  · simpa only [clamp,min_eq_right hut] using (le_max_right s u)
  · have htu : t ≤ u := (lt_of_not_ge hut).le
    have htv := htu.trans huv
    simp only [clamp,min_eq_left htu,min_eq_left htv,max_eq_right hst] at hpos
    exact False.elim ((lt_irrefl t) hpos)

/-- Empty common cells get zero in EVERY coordinate. A future K is never
assigned measurability at a collapsed earlier common start. -/
def commonDifference {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (i : Fin n) (j : Fin m) (k : Fin d) (ω : Sample d) : ℝ :=
  if commonStart τ σ i j < commonEnd τ σ i j then H i k ω-K j k ω else 0

theorem commonDifference_permission {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (hH : ∀ i k, StronglyMeasurable[jointNaturalFiltration d (τ i.castSucc)] (H i k))
    (hK : ∀ j k, StronglyMeasurable[jointNaturalFiltration d (σ j.castSucc)] (K j k)) (i : Fin n) (j : Fin m) (k : Fin d) :
    StronglyMeasurable[jointNaturalFiltration d (commonStart τ σ i j)] (commonDifference τ σ H K i j k) := by
  unfold commonDifference
  split_ifs with hp
  · exact ((hH i k).mono ((jointNaturalFiltration d).mono (le_max_left _ _))).sub
      ((hK j k).mono ((jointNaturalFiltration d).mono
        (positive_other_start _ _ _ _ (cell_order τ hτ i) (cell_order σ hσ j) hp)))
  · exact stronglyMeasurable_const

theorem commonDifference_bounded {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) (hK : ∀ j k, MemLp (K j k) ∞ (productLaw d))
    (i : Fin n) (j : Fin m) (k : Fin d) : MemLp (commonDifference τ σ H K i j k) ∞ (productLaw d) := by
  unfold commonDifference
  split_ifs with hp
  · simpa only [Pi.sub_def] using (hH i k).sub (hK j k)
  · exact MemLp.zero

private theorem cell_input_difference {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hσ : Monotone σ) (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (i : Fin n) (j : Fin m) (p : ℝ × Sample d) :
    intervalInput d (commonDifference τ σ H K i j) (commonStart τ σ i j) (commonEnd τ σ i j) p =
      intervalInput d (H i) (commonStart τ σ i j) (commonEnd τ σ i j) p-
        intervalInput d (K j) (commonStart τ σ i j) (commonEnd τ σ i j) p := by
  by_cases hp : commonStart τ σ i j < commonEnd τ σ i j
  · apply (EuclideanSpace.equiv (Fin d) ℝ).injective
    funext k
    change intervalInput d (commonDifference τ σ H K i j) _ _ p k =
      intervalInput d (H i) _ _ p k-intervalInput d (K j) _ _ p k
    simp only [intervalInput_apply,commonDifference,if_pos hp,mul_sub]
  · have he : commonStart τ σ i j = commonEnd τ σ i j :=
      le_antisymm (commonCell_order τ σ hσ i j) (le_of_not_gt hp)
    simp [intervalInput,he]

private theorem cell_output_difference {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hσ : Monotone σ) (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (i : Fin n) (j : Fin m) (ω : Sample d) :
    oneStep d (commonDifference τ σ H K i j) (commonStart τ σ i j) (commonEnd τ σ i j) ω =
      oneStep d (H i) (commonStart τ σ i j) (commonEnd τ σ i j) ω-
        oneStep d (K j) (commonStart τ σ i j) (commonEnd τ σ i j) ω := by
  by_cases hp : commonStart τ σ i j < commonEnd τ σ i j
  · simp only [oneStep,component,Pi.mul_apply,commonDifference,if_pos hp,sub_mul,Finset.sum_sub_distrib]
  · have he : commonStart τ σ i j = commonEnd τ σ i j :=
      le_antisymm (commonCell_order τ σ hσ i j) (le_of_not_gt hp)
    simp [oneStep,component,coordinateIncrement,he]

theorem refinedInput_difference {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ) (p : ℝ × Sample d) :
    refinedInput d τ σ (commonDifference τ σ H K) p = integrand d τ H p-integrand d σ K p := by
  unfold refinedInput
  simp_rw [cell_input_difference τ σ hσ H K,Finset.sum_sub_distrib]
  exact congrArg₂ (fun a b : EuclideanSpace ℝ (Fin d) => a-b)
    (refinedInput_left τ σ T hτ hσ hσ0 hσT hτT.le H p)
    (refinedInput_right τ σ T hτ hσ hτ0 hτT hσT.le K p)

theorem refinedOutput_difference {d n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ) (ω : Sample d) :
    refinedOutput d τ σ (commonDifference τ σ H K) ω = simpleIntegral d τ H ω-simpleIntegral d σ K ω := by
  unfold refinedOutput
  simp_rw [cell_output_difference τ σ hσ H K,Finset.sum_sub_distrib]
  exact congrArg₂ (fun a b : ℝ => a-b)
    (refinedOutput_left τ σ T hτ hσ0 hσT hτT.le H ω)
    (refinedOutput_right τ σ T hτ hσ hτ0 hτT hσT.le K ω)


/-- The ACTUAL common-cell family consumes the already derived finite
joint-source isometry and the OLD pure-clock nonoverlap theorem. -/
theorem refined_isometry {d n m : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (hτT : τ (Fin.last n) ≤ T)
    (G : Fin n → Fin m → Fin d → Sample d → ℝ)
    (hGpast : ∀ i j k, StronglyMeasurable[jointNaturalFiltration d (commonStart τ σ i j)] (G i j k))
    (hG : ∀ i j k, MemLp (G i j k) ∞ (productLaw d)) :
    (∫ ω, refinedOutput d τ σ G ω^2 ∂productLaw d) =
      ∫ p, ‖refinedInput d τ σ G p‖^2 ∂inputLaw d T := by
  let A (q : Fin n × Fin m) := commonStart τ σ q.1 q.2
  let B (q : Fin n × Fin m) := commonEnd τ σ q.1 q.2
  let C (q : Fin n × Fin m) := G q.1 q.2
  have hAB q : A q ≤ B q := commonCell_order τ σ hσ q.1 q.2
  have hBT q : B q ≤ T :=
    (clamp_bounds _ _ _ (cell_order τ hτ q.1)).2.trans ((hτ (Fin.le_last q.1.succ)).trans hτT)
  have hd q r (hqr : q ≠ r) : B q ≤ A r ∨ B r ≤ A q :=
    commonCell_nonoverlap τ σ hτ hσ q r hqr
  have h := finiteInterval_isometry T A B C hAB hBT hd
    (fun q => hGpast q.1 q.2) (fun q => hG q.1 q.2)
  simpa only [refinedOutput,refinedInput,Fintype.sum_prod_type,A,B,C] using h

private theorem toLp_difference_norm_square {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (μ : Measure α)
    (f g : α → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f-hg.toLp g‖^2 = ∫ a, ‖f a-g a‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp] with a ha hfa hga
  simp only [Pi.sub_apply] at ha
  rw [ha,hfa,hga,real_inner_self_eq_norm_sq]

/-- ALL native L2 distances are preserved across different actual partitions
of the SAME vector time input. This derives the later Gram/kernel identity. -/
theorem input_output_distance {d n m : ℕ} (T : ℝ≥0)
    (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (hHpast : ∀ i k, StronglyMeasurable[jointNaturalFiltration d (τ i.castSucc)] (H i k))
    (hKpast : ∀ j k, StronglyMeasurable[jointNaturalFiltration d (σ j.castSucc)] (K j k))
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) (hK : ∀ j k, MemLp (K j k) ∞ (productLaw d)) :
    dist (outputClass τ H hH) (outputClass σ K hK) =
      dist (inputClass T τ H hH) (inputClass T σ K hK) := by
  rw [dist_eq_norm,dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [outputClass,outputClass,inputClass,inputClass,toLp_difference_norm_square,toLp_difference_norm_square]
  simp only [Real.norm_eq_abs,sq_abs]
  have h := refined_isometry T τ σ hτ hσ hτT.le (commonDifference τ σ H K)
    (commonDifference_permission τ σ hτ hσ H K hHpast hKpast)
    (commonDifference_bounded τ σ H K hH hK)
  simpa only [refinedOutput_difference τ σ T hτ hσ hτ0 hσ0 hτT hσT H K,
    refinedInput_difference τ σ T hτ hσ hτ0 hσ0 hτT hσT H K] using h

/-- Native equality returns the SAME literal source output class, with no
new a.e.-chosen strategy or output substituted. -/
theorem outputClass_eq_of_inputClass_eq {d n m : ℕ} (T : ℝ≥0)
    (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (hHpast : ∀ i k, StronglyMeasurable[jointNaturalFiltration d (τ i.castSucc)] (H i k))
    (hKpast : ∀ j k, StronglyMeasurable[jointNaturalFiltration d (σ j.castSucc)] (K j k))
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) (hK : ∀ j k, MemLp (K j k) ∞ (productLaw d))
    (heq : inputClass T τ H hH = inputClass T σ K hK) : outputClass τ H hH = outputClass σ K hK := by
  apply dist_eq_zero.mp
  rw [input_output_distance T τ σ hτ hσ hτ0 hσ0 hτT hσT H K hHpast hKpast hH hK,heq,dist_self]

/-- The actually supplied finite programs also return the SAME literal
output a.e. when their original native Euclidean input classes agree. -/
theorem output_ae_eq_of_inputClass_eq {d n m : ℕ} (T : ℝ≥0)
    (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → Fin d → Sample d → ℝ) (K : Fin m → Fin d → Sample d → ℝ)
    (hHpast : ∀ i k, StronglyMeasurable[jointNaturalFiltration d (τ i.castSucc)] (H i k))
    (hKpast : ∀ j k, StronglyMeasurable[jointNaturalFiltration d (σ j.castSucc)] (K j k))
    (hH : ∀ i k, MemLp (H i k) ∞ (productLaw d)) (hK : ∀ j k, MemLp (K j k) ∞ (productLaw d))
    (heq : inputClass T τ H hH = inputClass T σ K hK) :
    simpleIntegral d τ H =ᵐ[productLaw d] simpleIntegral d σ K := by
  have he := outputClass_eq_of_inputClass_eq T τ σ hτ hσ hτ0 hσ0 hτT hσT H K hHpast hKpast hH hK heq
  have hl : (outputClass τ H hH : Sample d → ℝ) =ᵐ[productLaw d] simpleIntegral d τ H :=
    (simpleIntegral_memLp_two τ H hH).coeFn_toLp
  have hr : (outputClass σ K hK : Sample d → ℝ) =ᵐ[productLaw d] simpleIntegral d σ K :=
    (simpleIntegral_memLp_two σ K hK).coeFn_toLp
  rw [he] at hl
  exact hl.symm.trans hr

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorRepresentation
