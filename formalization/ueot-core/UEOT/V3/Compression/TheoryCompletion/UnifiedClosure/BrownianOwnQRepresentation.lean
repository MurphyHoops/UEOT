import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTimeInput

/-!
Original commitment: actual Q integrals must return the same value for the same time-input L2 class.
Existing result: literal Q tables and actual dt×Q inputs have exact energy/norm, with original common-cell START permissions.
Premise reduced: derive common-refinement Q isometry and all input/output L2 distances for the actual W, rather than relabel old P outputs.
Model/witness: same ownQ/shiftedW, original Fs, arbitrary finite clocks and commonDifference with collapsed cells assigned zero.
Consumer/boundary: native continuous-isometry Q extension; full predictable density and actual ItoRun remain separate obligations.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQRepresentation
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianIntegralClosure
open BrownianBoundedControlSource BrownianBoundedExponentialLimitSource BrownianBoundedGirsanovSource
open BrownianOwnQOneStepIntegral BrownianOwnQSimpleIntegral BrownianOwnQTimeInput
open BrownianCommonRefinement BrownianIntegralRepresentation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory InnerProductSpace RealInnerProductSpace
noncomputable section
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


variable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)

def refinedOutputQ {n m : ℕ} (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (G : Fin n → Fin m → (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, oneStep T f K (G i j) (commonStart τ σ i j) (commonEnd τ σ i j) ω

/-- SAME permitted common difference returns the literal difference of
actual Q outputs, pointwise; the only noise readout is actual shifted W. -/
theorem refinedOutput_difference {U : ℝ≥0} (r s : ElementaryInput U) (ω : ℝ≥0 → ℝ) :
    refinedOutputQ T f K r.clock s.clock (commonDifference r.clock s.clock r.coefficient s.coefficient) ω=
      BrownianOwnQSimpleIntegral.simpleIntegral T f K r ω-BrownianOwnQSimpleIntegral.simpleIntegral T f K s ω := by
  have hcell (i : Fin r.n) (j : Fin s.n) :
      oneStep T f K (commonDifference r.clock s.clock r.coefficient s.coefficient i j)
        (commonStart r.clock s.clock i j) (commonEnd r.clock s.clock i j) ω=
      oneStep T f K (r.coefficient i) (commonStart r.clock s.clock i j) (commonEnd r.clock s.clock i j) ω-
        oneStep T f K (s.coefficient j) (commonStart r.clock s.clock i j) (commonEnd r.clock s.clock i j) ω := by
    by_cases hp : commonStart r.clock s.clock i j < commonEnd r.clock s.clock i j
    · simp only [oneStep,Pi.mul_apply,commonDifference,if_pos hp,sub_mul]
    · have he : commonStart r.clock s.clock i j=commonEnd r.clock s.clock i j :=
        le_antisymm (commonCell_order r.clock s.clock s.clock_mono i j) (le_of_not_gt hp)
      simp [oneStep,fullIncrement,he]
  have hL : (∑ i : Fin r.n, ∑ j : Fin s.n, oneStep T f K (r.coefficient i)
      (commonStart r.clock s.clock i j) (commonEnd r.clock s.clock i j) ω)=
      BrownianOwnQSimpleIntegral.simpleIntegral T f K r ω := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [oneStep,Pi.mul_apply,fullIncrement,commonStart,commonEnd]
    rw [← Finset.mul_sum]
    apply congrArg (fun x : ℝ => r.coefficient i ω*x)
    apply clamp_telescope s.clock U (r.clock i.castSucc) (r.clock i.succ) s.clock_zero s.clock_end
      ?_ ?_ (fun a => shiftedProcess T f K a ω)
    · exact r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
    · simpa only [r.clock_end] using r.clock_mono (Fin.le_last i.succ)
  have hR : (∑ i : Fin r.n, ∑ j : Fin s.n, oneStep T f K (s.coefficient j)
      (commonStart r.clock s.clock i j) (commonEnd r.clock s.clock i j) ω)=
      BrownianOwnQSimpleIntegral.simpleIntegral T f K s ω := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have he (i : Fin r.n) : oneStep T f K (s.coefficient j) (commonStart r.clock s.clock i j) (commonEnd r.clock s.clock i j) ω=
        oneStep T f K (s.coefficient j) (commonStart s.clock r.clock j i) (commonEnd s.clock r.clock j i) ω := by
      simp only [oneStep,Pi.mul_apply,fullIncrement,commonStart,commonEnd]
      rw [clamp_difference_symm _ _ _ _
        (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ)))
        (s.clock_mono (by exact_mod_cast Nat.le_succ (j : ℕ))) (fun a => shiftedProcess T f K a ω)]
    simp_rw [he]
    simp only [oneStep,Pi.mul_apply,fullIncrement,commonStart,commonEnd]
    rw [← Finset.mul_sum]
    apply congrArg (fun x : ℝ => s.coefficient j ω*x)
    apply clamp_telescope r.clock U (s.clock j.castSucc) (s.clock j.succ) r.clock_zero r.clock_end
      ?_ ?_ (fun a => shiftedProcess T f K a ω)
    · exact s.clock_mono (by exact_mod_cast Nat.le_succ (j : ℕ))
    · simpa only [s.clock_end] using s.clock_mono (Fin.le_last j.succ)
  unfold refinedOutputQ
  simp_rw [hcell,Finset.sum_sub_distrib]
  rw [hL,hR]

include hK hbound
/-- Common-cell isometry under actual final Q with actual dt×Q energy.
The common cell's full original Fs permission is used, including empty cells. -/
theorem refined_isometry {n m : ℕ} (U : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (σ : Fin (m+1) → ℝ≥0)
    (hτ : Monotone τ) (hσ : Monotone σ) (hτU : τ (Fin.last n)≤U)
    (G : Fin n → Fin m → (ℝ≥0 → ℝ) → ℝ)
    (hGpast : ∀ i j, StronglyMeasurable[naturalFiltration (commonStart τ σ i j)] (G i j))
    (hG : ∀ i j, MemLp (G i j) ∞ (fullLaw T f)) :
    (∫ ω, refinedOutputQ T f K τ σ G ω^2 ∂fullLaw T f)=
      ∫ p, refinedInput τ σ G p^2 ∂inputLawQ T f U := by
  let _ := fullLaw_probability T f K hK hbound
  let A (q : Fin n × Fin m) := commonStart τ σ q.1 q.2
  let B (q : Fin n × Fin m) := commonEnd τ σ q.1 q.2
  let C (q : Fin n × Fin m) := G q.1 q.2
  let Y q := oneStep T f K (C q) (A q) (B q)
  let Z q := intervalIntegrand (C q) (A q) (B q)
  have hAB q : A q≤B q := commonCell_order τ σ hσ q.1 q.2
  have hBT q : B q≤U :=
    (clamp_bounds _ _ _ (hτ (by exact_mod_cast Nat.le_succ (q.1 : ℕ)))).2.trans
      ((hτ (Fin.le_last q.1.succ)).trans hτU)
  have hY q : MemLp (Y q) 2 (fullLaw T f) := oneStep_memLp_two T f K hK hbound (hG q.1 q.2) _ _
  have hZ q : MemLp (Z q) 2 (inputLawQ T f U) := interval_memLp_two T f K hK hbound (hG q.1 q.2) U _ _
  have hYo q r (hqr : q≠r) : (∫ ω, Y q ω*Y r ω ∂fullLaw T f)=0 := by
    rcases commonCell_nonoverlap τ σ hτ hσ q r hqr with h | h
    · exact nonoverlap_orthogonal T f K hK hbound _ _ _ _ (hAB q) h (hAB r)
        (hGpast q.1 q.2) (hGpast r.1 r.2) (hG q.1 q.2) (hG r.1 r.2)
    · simpa only [mul_comm] using nonoverlap_orthogonal T f K hK hbound _ _ _ _ (hAB r) h (hAB q)
        (hGpast r.1 r.2) (hGpast q.1 q.2) (hG r.1 r.2) (hG q.1 q.2)
  have hZo q r (hqr : q≠r) : (∫ p, Z q p*Z r p ∂inputLawQ T f U)=0 := by
    have hz p : Z q p*Z r p=0 := interval_products_zero _ _ _ _ (commonCell_nonoverlap τ σ hτ hσ q r hqr) p
    simp_rw [hz]
    exact integral_zero _ _
  have heY : refinedOutputQ T f K τ σ G=fun ω => ∑ q : Fin n × Fin m, Y q ω := by
    funext ω
    simp only [refinedOutputQ,Fintype.sum_prod_type,Y,C,A,B]
  have heZ : refinedInput τ σ G=fun p => ∑ q : Fin n × Fin m, Z q p := by
    funext p
    simp only [refinedInput,Fintype.sum_prod_type,Z,C,A,B]
  rw [heY,heZ,finite_square_energy (fullLaw T f) Y hY hYo,finite_square_energy (inputLawQ T f U) Z hZ hZo]
  apply Finset.sum_congr rfl
  intro q _
  rw [oneStep_isometry T f K hK hbound _ _ (hAB q) (hGpast q.1 q.2) (hG q.1 q.2),
    interval_energy T f K hK hbound (C q) U _ _ (hAB q) (hBT q)]

omit hK hbound in
private theorem toLp_difference_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a b : α → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ‖ha.toLp a-hb.toLp b‖^2=∫ x, (a x-b x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (ha.toLp a) (hb.toLp b),ha.coeFn_toLp,hb.coeFn_toLp] with x hs ha hb
  simp only [Pi.sub_apply] at hs
  rw [hs,ha,hb]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- Actual Q input/output distances across arbitrary representations;
this yields class dependence before any Q integral extension is defined. -/
theorem family_distance {U : ℝ≥0} (r s : ElementaryInput U) :
    dist (outputValueQ T f K hK hbound r) (outputValueQ T f K hK hbound s)=
      dist (inputValueQ T f K hK hbound r) (inputValueQ T f K hK hbound s) := by
  rw [dist_eq_norm,dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [outputValueQ,outputValueQ,inputValueQ,inputValueQ,toLp_difference_norm_sq,toLp_difference_norm_sq]
  have h := refined_isometry T f K hK hbound U r.clock s.clock r.clock_mono s.clock_mono r.clock_end.le
    (commonDifference r.clock s.clock r.coefficient s.coefficient)
    (commonDifference_permission r.clock s.clock r.clock_mono s.clock_mono r.coefficient s.coefficient r.coefficient_past s.coefficient_past)
    (fun i j => coefficient_bounded_Q T f K hK hbound
      (commonDifference_bounded r.clock s.clock r.coefficient s.coefficient r.coefficient_bounded s.coefficient_bounded i j))
  simpa only [refinedOutput_difference T f K r s,
    refinedInput_difference r.clock s.clock U r.clock_mono s.clock_mono r.clock_zero s.clock_zero r.clock_end s.clock_end r.coefficient s.coefficient] using h

/-- Input representation equality returns equality of the actual Q output. -/
theorem output_eq_of_input_eq {U : ℝ≥0} (r s : ElementaryInput U)
    (h : inputValueQ T f K hK hbound r=inputValueQ T f K hK hbound s) :
    outputValueQ T f K hK hbound r=outputValueQ T f K hK hbound s := by
  apply dist_eq_zero.mp
  rw [family_distance T f K hK hbound r s,h,dist_self]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQRepresentation
