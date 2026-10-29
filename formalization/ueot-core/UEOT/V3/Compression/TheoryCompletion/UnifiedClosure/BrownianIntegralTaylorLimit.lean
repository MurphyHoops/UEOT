import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianScalarTaylorRemainder

/-!
Original commitment: actual scalar Ito requires the actual finite Taylor remainder sum to vanish in source measure.
Existing result: genuine C2 quadratic remainder control on the SAME actual continuous path and actual full-input QV.
Premise reduced: construct measurable finite-grid normalized errors from actual increments, derive their AE zero limit, consume actual QV.
Model/witness: SAME original fullPredictableL2 T/sourceLaw/naturalFiltration and deterministic computed-vanishing-mesh caller clocks, T=0/empty allowed.
Consumer: actual bounded-C2 Ito identity; no third derivative, L4, remainder-zero source field or uncountable AE intersection.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTaylorLimit
open MeasureTheory ProbabilityTheory Set Filter
open BrownianMartingaleSource
open BrownianProjectiveSource BrownianPredictableInputs BrownianIntegralContinuousVersion
open BrownianQuadraticVariation BrownianPartitionQV BrownianScalarTaylorRemainder
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual finite-cell normalized Taylor error; native zero division is
harmless because the numerator is literally zero on a zero increment. -/
def cellRatio (φ : ℝ → ℝ) (a b : ℝ) : ℝ≥0 :=
  ‖secondRemainder φ a b‖₊/‖b-a‖₊^2

theorem cellRatio_mul_sq (φ : ℝ → ℝ) (a b : ℝ) :
    (cellRatio φ a b : ℝ)*(b-a)^2 = ‖secondRemainder φ a b‖ := by
  by_cases h : b-a=0
  · have hab : b=a := sub_eq_zero.mp h
    subst b
    simp [cellRatio,secondRemainder]
  · simp only [cellRatio,NNReal.coe_div,NNReal.coe_pow,coe_nnnorm,Real.norm_eq_abs,sq_abs]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 h)

theorem cellRatio_le_of_bound (φ : ℝ → ℝ) (a b : ℝ) (ε : ℝ≥0)
    (hb : ‖secondRemainder φ a b‖ ≤ (ε : ℝ)*(b-a)^2) : cellRatio φ a b ≤ ε := by
  by_cases h : b-a=0
  · have hab : b=a := sub_eq_zero.mp h
    subst b
    simp [cellRatio,secondRemainder]
  · apply NNReal.coe_le_coe.mp
    simp only [cellRatio,NNReal.coe_div,NNReal.coe_pow,coe_nnnorm,Real.norm_eq_abs,sq_abs]
    exact (div_le_iff₀ (sq_pos_of_ne_zero h)).mpr hb

/-- Maximum is a literal finite supremum, including the empty-grid zero. -/
def gridRatio (φ : ℝ → ℝ) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (X : ℝ≥0 → ℝ) : ℝ≥0 :=
  Finset.univ.sup (fun i : Fin n => cellRatio φ (X (τ i.castSucc)) (X (τ i.succ)))

/-- Actual finite-path Taylor remainder table. -/
def remainderSum (φ : ℝ → ℝ) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (X : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin n, secondRemainder φ (X (τ i.castSucc)) (X (τ i.succ))

theorem remainderSum_norm_le (φ : ℝ → ℝ) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (X : ℝ≥0 → ℝ) :
    ‖remainderSum φ τ X‖ ≤ (gridRatio φ τ X : ℝ)*
      (∑ i : Fin n, (X (τ i.succ)-X (τ i.castSucc))^2) := by
  calc
    _ ≤ ∑ i : Fin n, ‖secondRemainder φ (X (τ i.castSucc)) (X (τ i.succ))‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, (cellRatio φ (X (τ i.castSucc)) (X (τ i.succ)) : ℝ)*
        (X (τ i.succ)-X (τ i.castSucc))^2 := by simp_rw [cellRatio_mul_sq]
    _ ≤ ∑ i : Fin n, (gridRatio φ τ X : ℝ)*(X (τ i.succ)-X (τ i.castSucc))^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j : Fin n =>
        cellRatio φ (X (τ j.castSucc)) (X (τ j.succ))) (Finset.mem_univ i))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Actual C2 path control derives the actual finite maximum-ratio limit. -/
theorem gridRatio_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (T : ℝ≥0) (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hmono : ∀ m, Monotone (τ m)) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) (X : ℝ≥0 → ℝ) (hX : Continuous X) :
    Tendsto (fun m => (gridRatio φ (τ m) X : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := secondRemainder_grid_small φ hφ T N τ hmono hend hmesh X hX (ε/2) (by positivity)
  obtain ⟨M,hM⟩ := eventually_atTop.mp he
  refine ⟨M,fun m hm => ?_⟩
  have hr : gridRatio φ (τ m) X ≤ Real.toNNReal (ε/2) := by
    apply Finset.sup_le
    intro i _
    apply cellRatio_le_of_bound
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ ε/2)]
    exact hM m hm i
  have hb := NNReal.coe_le_coe.mpr hr
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ ε/2)] at hb
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (gridRatio φ (τ m) X).coe_nonneg]
  linarith

private theorem measurable_secondRemainder {Ω : Type*} [MeasurableSpace Ω]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => secondRemainder φ (X ω) (Y ω)) := by
  have hf := hφ.continuous.measurable
  have hd := (hφ.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).measurable
  have hdd := (hφ.continuous_iteratedDeriv' 2).measurable
  unfold secondRemainder
  fun_prop

private theorem measurable_cellRatio {Ω : Type*} [MeasurableSpace Ω]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => cellRatio φ (X ω) (Y ω)) :=
  (measurable_secondRemainder φ hφ X Y hX hY).nnnorm.div ((hY.sub hX).nnnorm.pow_const 2)

private theorem measurable_finset_sup {Ω ι : Type*} [MeasurableSpace Ω] (S : Finset ι)
    (F : ι → Ω → ℝ≥0) (hF : ∀ i, Measurable (F i)) : Measurable (fun ω => S.sup (fun i => F i ω)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sup_empty]; exact measurable_const
  | @insert i S hi ih =>
    simp only [Finset.sup_insert]
    exact (hF i).sup ih

private theorem gridRatio_measurable {Ω : Type*} [MeasurableSpace Ω]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (hX : ∀ u, Measurable (X u)) :
    Measurable (fun ω => (gridRatio φ τ (fun u => X u ω) : ℝ)) :=
  measurable_coe_nnreal_real.comp (measurable_finset_sup Finset.univ _
    (fun i => measurable_cellRatio φ hφ (X (τ i.castSucc)) (X (τ i.succ)) (hX _) (hX _)))

private theorem remainderSum_measurable {Ω : Type*} [MeasurableSpace Ω]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (hX : ∀ u, Measurable (X u)) :
    Measurable (fun ω => remainderSum φ τ (fun u => X u ω)) := by
  exact Finset.measurable_fun_sum Finset.univ (fun i _ =>
    measurable_secondRemainder φ hφ (X (τ i.castSucc)) (X (τ i.succ)) (hX _) (hX _))

/-- Actual finite normalized remainder coefficient is measurable and tends
AE to zero on the already constructed SAME continuous source event. -/
theorem actual_gridRatio_tendsto_ae (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (T : ℝ≥0) (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hmono : ∀ m, Monotone (τ m)) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) (f : fullPredictableL2 T) :
    ∀ᵐ ω ∂sourceLaw, Tendsto (fun m => (gridRatio φ (τ m) (fun u => continuousIntegralProcess T f u ω) : ℝ)) atTop (𝓝 0) :=
  (continuousIntegralProcess_continuous T f).mono (fun ω hω =>
    gridRatio_tendsto φ hφ T N τ hmono hend hmesh (fun u => continuousIntegralProcess T f u ω) hω)

/-- Actual computed finite maximum is an ordinary measurable source
readout, including empty/repeated/zero-increment cells. -/
theorem actual_gridRatio_measurable (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (f : fullPredictableL2 T) :
    Measurable (fun ω => (gridRatio φ τ (fun u => continuousIntegralProcess T f u ω) : ℝ)) :=
  gridRatio_measurable φ hφ τ (continuousIntegralProcess T f)
    (fun u => ((continuousIntegralProcess_stronglyAdapted T f u).mono (naturalFiltration.le u)).measurable)

/-- Actual SAME finite Taylor remainder sums vanish in source measure for
EVERY original full predictable L2 input and original caller clock family.
Only C2 regularity enters, with no global derivative bound/L4/third derivative. -/
theorem actual_remainderSum_tendstoInMeasure (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (T : ℝ≥0) (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hmono : ∀ m, Monotone (τ m)) (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) (f : fullPredictableL2 T) :
    TendstoInMeasure sourceLaw (fun m ω => remainderSum φ (τ m) (fun u => continuousIntegralProcess T f u ω))
      atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_of_ae_zero_domination sourceLaw _
    (fun m ω => (gridRatio φ (τ m) (fun u => continuousIntegralProcess T f u ω) : ℝ))
    (fun m ω => ∑ i : Fin (N m), (continuousIntegralProcess T f (τ m i.succ) ω-
      continuousIntegralProcess T f (τ m i.castSucc) ω)^2) _
  · intro m
    exact (remainderSum_measurable φ hφ (τ m) (continuousIntegralProcess T f)
      (fun u => ((continuousIntegralProcess_stronglyAdapted T f u).mono (naturalFiltration.le u)).measurable)).aestronglyMeasurable
  · exact actual_gridRatio_tendsto_ae φ hφ T N τ hmono hend hmesh f
  · exact fullInput_partition_QV_inMeasure T N τ hmono hzero hend hmesh f
  · intro m ω
    have hpos : 0 ≤ ∑ i : Fin (N m), (continuousIntegralProcess T f (τ m i.succ) ω-
        continuousIntegralProcess T f (τ m i.castSucc) ω)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simpa only [Real.norm_eq_abs,abs_of_nonneg hpos] using
      remainderSum_norm_le φ (τ m) (fun u => continuousIntegralProcess T f u ω)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTaylorLimit
