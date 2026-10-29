import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianTimeIntegrand

/-!
Original commitment: the actual stochastic integral must depend on its time input, not the chosen partition.
Existing result: literal predictable outputs and native time-times-source input classes have exact equal norms.
Premise reduced: construct a common interval refinement with pointwise input and actual-output invariance.
Model/witness: two finite deterministic [0,T] partitions; coefficients retain their original left-past permission.
Consumer: representation independence and native L2 continuous extension; general predictable density remains open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianCommonRefinement
open MeasureTheory ProbabilityTheory Set
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource
open BrownianOneStepIntegral BrownianSimplePredictableIntegral BrownianTimeIntegrand
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Clamp the refining clock to one original interval. Degenerate and empty
intersection cells become zero-length actual intervals. -/
def clamp (s t x : ℝ≥0) : ℝ≥0 := max s (min t x)

theorem clamp_mono (s t : ℝ≥0) : Monotone (clamp s t) :=
  fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)

theorem clamp_bounds (s t x : ℝ≥0) (hst : s ≤ t) : s ≤ clamp s t x ∧ clamp s t x ≤ t :=
  ⟨le_max_left _ _,max_le hst (min_le_left _ _)⟩

private theorem fin_telescope {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ i : Fin n, (f i.succ-f i.castSucc)) = f (Fin.last n)-f 0 := by
  rw [Finset.sum_sub_distrib]
  have h0 := Fin.sum_univ_succ f
  have hN := Fin.sum_univ_castSucc f
  linarith

/-- A literal source-coordinate identity valid for ANY readout, rather than
an identity postulated only for a desired Brownian law. -/
theorem clamp_telescope {m : ℕ} (σ : Fin (m+1) → ℝ≥0) (T s t : ℝ≥0)
    (h0 : σ 0 = 0) (hT : σ (Fin.last m) = T) (hst : s ≤ t) (htT : t ≤ T)
    (f : ℝ≥0 → ℝ) :
    (∑ j : Fin m, (f (clamp s t (σ j.succ))-f (clamp s t (σ j.castSucc)))) = f t-f s := by
  have h := fin_telescope (fun j => f (clamp s t (σ j)))
  simpa only [h0,hT,clamp,min_eq_left htT,max_eq_right hst,min_zero,max_zero] using h

/-- Symmetry of each common-refinement increment, including empty cells.
It applies to both actual source readouts and interval-indicator readouts. -/
theorem clamp_difference_symm (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (f : ℝ≥0 → ℝ) :
    f (clamp s t v)-f (clamp s t u) = f (clamp u v t)-f (clamp u v s) := by
  by_cases htu : t ≤ u
  · have hsu := hst.trans htu
    have htv := htu.trans huv
    simp only [clamp,min_eq_left htu,min_eq_left htv,max_eq_right hst,
      min_eq_right (hsu.trans huv),min_eq_right htv,max_eq_left hsu,max_eq_left htu,sub_self]
  · by_cases hvs : v ≤ s
    · have hus := huv.trans hvs
      have hut := hus.trans hst
      have hvt := hvs.trans hst
      simp only [clamp,min_eq_right hut,min_eq_right hvt,max_eq_left hus,max_eq_left hvs,
        min_eq_left hvt,min_eq_left hvs,max_eq_right huv,sub_self]
    · have hut : u ≤ t := (lt_of_not_ge htu).le
      have hsv : s ≤ v := (lt_of_not_ge hvs).le
      have hsmin : s ≤ min t v := le_min hst hsv
      have humin : u ≤ min v t := le_min huv hut
      simp only [clamp,min_eq_right hut,min_eq_right hsv,max_eq_right hsmin,max_eq_right humin]
      rw [min_comm t v,max_comm s u]

private theorem interval_indicator_difference (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ) :
    (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => (1 : ℝ)) x =
      (Iic (t : ℝ)).indicator (fun _ => (1 : ℝ)) x-
        (Iic (s : ℝ)).indicator (fun _ => (1 : ℝ)) x := by
  have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  by_cases hs : x ≤ (s : ℝ)
  · have ht := hs.trans hst'
    simp [hs,ht,not_lt_of_ge hs]
  · by_cases ht : x ≤ (t : ℝ)
    · simp [hs,ht,lt_of_not_ge hs]
    · simp [hs,ht]

/-- The refining clock reconstructs the exact literal input block at EVERY
time-source point, including all partition boundaries. -/
theorem intervalIntegrand_refine {m : ℕ} (σ : Fin (m+1) → ℝ≥0) (hσ : Monotone σ)
    (T s t : ℝ≥0) (h0 : σ 0 = 0) (hT : σ (Fin.last m) = T) (hst : s ≤ t) (htT : t ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) :
    (∑ j : Fin m, intervalIntegrand H (clamp s t (σ j.castSucc)) (clamp s t (σ j.succ)) p) =
      intervalIntegrand H s t p := by
  have horder (j : Fin m) : clamp s t (σ j.castSucc) ≤ clamp s t (σ j.succ) :=
    clamp_mono s t (hσ (by exact_mod_cast Nat.le_succ (j : ℕ)))
  simp only [intervalIntegrand]
  simp_rw [interval_indicator_difference _ _ (horder _)]
  rw [← Finset.sum_mul]
  rw [clamp_telescope σ T s t h0 hT hst htT
    (fun a => (Iic (a : ℝ)).indicator (fun _ => (1 : ℝ)) p.1)]
  rw [interval_indicator_difference s t hst]

/-- Exact common-cell symmetry of the literal integrand, derived using the
same clamp readout identity as the actual source output. -/
theorem intervalIntegrand_common_symm (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (H : (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) :
    intervalIntegrand H (clamp s t u) (clamp s t v) p =
      intervalIntegrand H (clamp u v s) (clamp u v t) p := by
  simp only [intervalIntegrand]
  rw [interval_indicator_difference _ _ (clamp_mono s t huv),
    interval_indicator_difference _ _ (clamp_mono u v hst),
    clamp_difference_symm s t u v hst huv
      (fun a => (Iic (a : ℝ)).indicator (fun _ => (1 : ℝ)) p.1)]

/-- The actual SAME Brownian one-step output splits pointwise over the
common cells, rather than producing a new a.e.-chosen output version. -/
theorem oneStep_refine {m : ℕ} (σ : Fin (m+1) → ℝ≥0) (T s t : ℝ≥0)
    (h0 : σ 0 = 0) (hT : σ (Fin.last m) = T) (hst : s ≤ t) (htT : t ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) :
    (∑ j : Fin m, oneStep H (clamp s t (σ j.castSucc)) (clamp s t (σ j.succ)) ω) =
      oneStep H s t ω := by
  simp only [oneStep,Pi.mul_apply,increment]
  rw [← Finset.mul_sum,clamp_telescope σ T s t h0 hT hst htT (fun a => process a ω)]

/-- Both descriptions of a common cell read the SAME actual increment. -/
theorem oneStep_common_symm (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (H : (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) :
    oneStep H (clamp s t u) (clamp s t v) ω =
      oneStep H (clamp u v s) (clamp u v t) ω := by
  simp only [oneStep,Pi.mul_apply,increment]
  rw [clamp_difference_symm s t u v hst huv (fun a => process a ω)]

/-- Refinement preserves permission: the old coefficient is measurable in
the refined cell's START-time past, using only forward filtration monotonicity. -/
theorem coefficient_refine_permission {H : (ℝ≥0 → ℝ) → ℝ} (s t x : ℝ≥0)
    (hH : StronglyMeasurable[naturalFiltration s] H) :
    StronglyMeasurable[naturalFiltration (clamp s t x)] H :=
  hH.mono (naturalFiltration.mono (le_max_left _ _))

private theorem cell_order {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hτ (by exact_mod_cast Nat.le_succ (i : ℕ))

/-- Deterministic common-cell start; no source coordinate is added. -/
def commonStart {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (i : Fin n) (j : Fin m) : ℝ≥0 := clamp (τ i.castSucc) (τ i.succ) (σ j.castSucc)

def commonEnd {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (i : Fin n) (j : Fin m) : ℝ≥0 := clamp (τ i.castSucc) (τ i.succ) (σ j.succ)

def refinedInput {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (G : Fin n → Fin m → (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, intervalIntegrand (G i j) (commonStart τ σ i j) (commonEnd τ σ i j) p

def refinedOutput {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (G : Fin n → Fin m → (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, oneStep (G i j) (commonStart τ σ i j) (commonEnd τ σ i j) ω

theorem commonCell_order {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hσ : Monotone σ) (i : Fin n) (j : Fin m) : commonStart τ σ i j ≤ commonEnd τ σ i j :=
  clamp_mono _ _ (cell_order σ hσ j)

/-- The common refinement preserves the original left description pointwise. -/
theorem refinedInput_left {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ) (hσ0 : σ 0 = 0)
    (hσT : σ (Fin.last m) = T) (hτT : τ (Fin.last n) ≤ T)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) :
    refinedInput τ σ (fun i _ => H i) p = integrand τ H p := by
  apply Finset.sum_congr rfl
  intro i _
  exact intervalIntegrand_refine σ hσ T _ _ hσ0 hσT (cell_order τ hτ i)
    ((hτ (Fin.le_last i.succ)).trans hτT) (H i) p

theorem refinedOutput_left {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ0 : σ 0 = 0)
    (hσT : σ (Fin.last m) = T) (hτT : τ (Fin.last n) ≤ T)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) :
    refinedOutput τ σ (fun i _ => H i) ω = simpleIntegral τ H ω := by
  apply Finset.sum_congr rfl
  intro i _
  exact oneStep_refine σ T _ _ hσ0 hσT (cell_order τ hτ i)
    ((hτ (Fin.le_last i.succ)).trans hτT) (H i) ω

/-- The SAME common cells preserve the other partition's description. -/
theorem refinedInput_right {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ) (hτ0 : τ 0 = 0)
    (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) ≤ T)
    (K : Fin m → (ℝ≥0 → ℝ) → ℝ) (p : ℝ × (ℝ≥0 → ℝ)) :
    refinedInput τ σ (fun _ j => K j) p = integrand σ K p := by
  have he : refinedInput τ σ (fun _ j => K j) p = refinedInput σ τ (fun j _ => K j) p := by
    unfold refinedInput
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegrand_common_symm _ _ _ _ (cell_order τ hτ i) (cell_order σ hσ j) (K j) p
  rw [he]
  exact refinedInput_left σ τ T hσ hτ hτ0 hτT hσT K p

theorem refinedOutput_right {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ) (hτ0 : τ 0 = 0)
    (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) ≤ T)
    (K : Fin m → (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) :
    refinedOutput τ σ (fun _ j => K j) ω = simpleIntegral σ K ω := by
  have he : refinedOutput τ σ (fun _ j => K j) ω = refinedOutput σ τ (fun j _ => K j) ω := by
    unfold refinedOutput
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact oneStep_common_symm _ _ _ _ (cell_order τ hτ i) (cell_order σ hσ j) (K j) ω
  rw [he]
  exact refinedOutput_left σ τ T hσ hτ0 hτT hσT K ω

private theorem clamp_positive_other_start (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v)
    (hpos : clamp s t u < clamp s t v) : u ≤ clamp s t u := by
  by_cases hut : u ≤ t
  · simpa only [clamp,min_eq_right hut] using (le_max_right s u)
  · have htu : t ≤ u := (lt_of_not_ge hut).le
    have htv := htu.trans huv
    simp only [clamp,min_eq_left htu,min_eq_left htv,max_eq_right hst] at hpos
    exact False.elim ((lt_irrefl t) hpos)

/-- Empty common cells receive the SAME zero coefficient. This avoids
claiming that a future coefficient is measurable at a collapsed earlier cell. -/
def commonDifference {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (i : Fin n) (j : Fin m) (ω : ℝ≥0 → ℝ) : ℝ :=
  if commonStart τ σ i j < commonEnd τ σ i j then H i ω-K j ω else 0

theorem commonDifference_permission {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (hH : ∀ i, StronglyMeasurable[naturalFiltration (τ i.castSucc)] (H i))
    (hK : ∀ j, StronglyMeasurable[naturalFiltration (σ j.castSucc)] (K j)) (i : Fin n) (j : Fin m) :
    StronglyMeasurable[naturalFiltration (commonStart τ σ i j)] (commonDifference τ σ H K i j) := by
  unfold commonDifference
  by_cases hp : commonStart τ σ i j < commonEnd τ σ i j
  · simp only [if_pos hp]
    exact ((hH i).mono (naturalFiltration.mono (le_max_left _ _))).sub
      ((hK j).mono (naturalFiltration.mono
        (clamp_positive_other_start _ _ _ _ (cell_order τ hτ i) (cell_order σ hσ j) hp)))
  · simp only [if_neg hp]
    exact stronglyMeasurable_const

theorem commonDifference_bounded {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (hH : ∀ i, MemLp (H i) ∞ sourceLaw) (hK : ∀ j, MemLp (K j) ∞ sourceLaw) (i : Fin n) (j : Fin m) :
    MemLp (commonDifference τ σ H K i j) ∞ sourceLaw := by
  unfold commonDifference
  by_cases hp : commonStart τ σ i j < commonEnd τ σ i j
  · simpa only [if_pos hp,Pi.sub_def] using (hH i).sub (hK j)
  · simp only [if_neg hp]
    exact MemLp.zero

private theorem cell_input_difference {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hσ : Monotone σ) (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (i : Fin n) (j : Fin m) (p : ℝ × (ℝ≥0 → ℝ)) :
    intervalIntegrand (commonDifference τ σ H K i j) (commonStart τ σ i j) (commonEnd τ σ i j) p =
      intervalIntegrand (H i) (commonStart τ σ i j) (commonEnd τ σ i j) p -
        intervalIntegrand (K j) (commonStart τ σ i j) (commonEnd τ σ i j) p := by
  by_cases hp : commonStart τ σ i j < commonEnd τ σ i j
  · simp only [intervalIntegrand,commonDifference,if_pos hp,mul_sub]
  · have he : commonStart τ σ i j = commonEnd τ σ i j :=
      le_antisymm (commonCell_order τ σ hσ i j) (le_of_not_gt hp)
    simp [intervalIntegrand,he]

private theorem cell_output_difference {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hσ : Monotone σ) (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (i : Fin n) (j : Fin m) (ω : ℝ≥0 → ℝ) :
    oneStep (commonDifference τ σ H K i j) (commonStart τ σ i j) (commonEnd τ σ i j) ω =
      oneStep (H i) (commonStart τ σ i j) (commonEnd τ σ i j) ω -
        oneStep (K j) (commonStart τ σ i j) (commonEnd τ σ i j) ω := by
  by_cases hp : commonStart τ σ i j < commonEnd τ σ i j
  · simp only [oneStep,Pi.mul_apply,commonDifference,if_pos hp,sub_mul]
  · have he : commonStart τ σ i j = commonEnd τ σ i j :=
      le_antisymm (commonCell_order τ σ hσ i j) (le_of_not_gt hp)
    simp [oneStep,increment,he]

/-- Two different partitions are compared on one ACTUALLY CONSTRUCTED common
input. Degenerate cells are strictly zero, not silently assigned future permission. -/
theorem refinedInput_difference {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (p : ℝ × (ℝ≥0 → ℝ)) :
    refinedInput τ σ (commonDifference τ σ H K) p = integrand τ H p-integrand σ K p := by
  unfold refinedInput
  simp_rw [cell_input_difference τ σ hσ H K,Finset.sum_sub_distrib]
  exact congrArg₂ (fun a b : ℝ => a-b)
    (refinedInput_left τ σ T hτ hσ hσ0 hσT hτT.le H p)
    (refinedInput_right τ σ T hτ hσ hτ0 hτT hσT.le K p)

/-- The SAME constructed common difference produces the difference of the
literal original outputs, pointwise on the original source sample space. -/
theorem refinedOutput_difference {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (T : ℝ≥0) (hτ : Monotone τ) (hσ : Monotone σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτT : τ (Fin.last n) = T) (hσT : σ (Fin.last m) = T)
    (H : Fin n → (ℝ≥0 → ℝ) → ℝ) (K : Fin m → (ℝ≥0 → ℝ) → ℝ)
    (ω : ℝ≥0 → ℝ) :
    refinedOutput τ σ (commonDifference τ σ H K) ω = simpleIntegral τ H ω-simpleIntegral σ K ω := by
  unfold refinedOutput
  simp_rw [cell_output_difference τ σ hσ H K,Finset.sum_sub_distrib]
  exact congrArg₂ (fun a b : ℝ => a-b)
    (refinedOutput_left τ σ T hτ hσ0 hσT hτT.le H ω)
    (refinedOutput_right τ σ T hτ hσ hτ0 hτT hσT.le K ω)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianCommonRefinement
