import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralL2TimeContinuity
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Finset.Sort

/-!
Original commitment: actual integral approximation must control a whole time grid, not only each endpoint separately.
Existing result: actual same-source natural martingale, L2 energies and native conditional Jensen/maximal inequalities.
Premise reduced: derive squared submartingale and weak finite-grid maximum tail directly from those native sources.
Model/witness: SAME naturalFiltration/sourceLaw, genuine full predictable input, arbitrary monotone countable clock.
Consumer: countable dense-time approximation and actual continuous modification; full Doob Lp is not assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralMaximalControl
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralMartingale BrownianIntegralL2TimeContinuity
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Native conditional Jensen, with actual integrability, turns any source-natural
L2 martingale into its nonnegative squared submartingale. -/
theorem square_submartingale {g : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ}
    (hg : Martingale g naturalFiltration sourceLaw) (hL2 : ∀ u, MemLp (g u) 2 sourceLaw) :
    Submartingale (fun u ω => g u ω ^ 2) naturalFiltration sourceLaw := by
  refine ⟨fun u => (hg.stronglyMeasurable u).pow 2,?_,fun u => (hL2 u).integrable_sq⟩
  intro s t hst
  have hj := (show Even (2 : ℕ) from ⟨1,rfl⟩).convexOn_pow.map_condExp_le_univ
    (naturalFiltration.le s) (continuous_pow 2).lowerSemicontinuous
    (hg.integrable t) (hL2 t).integrable_sq
  filter_upwards [hj,hg.condExp_ae_eq hst] with ω hjω hmω
  simpa only [Function.comp_def,hmω] using hjω

theorem integralProcess_square_submartingale (T : ℝ≥0) (f : fullPredictableL2 T) :
    Submartingale (fun u ω => integralProcess T f u ω ^ 2) naturalFiltration sourceLaw :=
  square_submartingale (integralProcess_martingale T f) (fun u => integralProcess_memLp_two T u f)

/-- Restriction of the ORIGINAL natural filtration to a monotone clock only. -/
def clockFiltration (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    Filtration ℕ (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) where
  seq := fun n => naturalFiltration (τ n)
  mono' := fun _ _ h => naturalFiltration.mono (hτ h)
  le' := fun n => naturalFiltration.le (τ n)

/-- Weak maximum control supplied by the actual native maximal inequality.
The terminal second energy is literal; no maximal-norm certificate is input. -/
theorem finite_grid_maximum (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    {g : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ} (hg : Martingale g naturalFiltration sourceLaw)
    (hL2 : ∀ u, MemLp (g u) 2 sourceLaw) (ε : ℝ≥0) (n : ℕ) :
    (ε : ℝ≥0∞)^2 * sourceLaw {ω | ∃ k ≤ n, (ε : ℝ) ≤ |g (τ k) ω|} ≤
      ENNReal.ofReal (∫ ω, g (τ n) ω ^ 2 ∂sourceLaw) := by
  let G : ℕ → (ℝ≥0 → ℝ) → ℝ := fun k ω => g (τ k) ω ^ 2
  have hsq := square_submartingale hg hL2
  have hsub : Submartingale G (clockFiltration τ hτ) sourceLaw :=
    ⟨fun k => hsq.stronglyMeasurable (τ k),fun i j hij => hsq.2.1 _ _ (hτ hij),fun k => hsq.integrable (τ k)⟩
  have hm := maximal_ineq hsub (fun k ω => sq_nonneg (g (τ k) ω)) (ε := ε^2) n
  have he : {ω | ((ε^2 : ℝ≥0) : ℝ) ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun k => G k ω)} =
      {ω | ∃ k ≤ n, (ε : ℝ) ≤ |g (τ k) ω|} := by
    ext ω
    simp only [mem_ofPred_eq,Finset.le_sup'_iff,Finset.mem_range,Nat.lt_succ_iff,NNReal.coe_pow,G]
    constructor
    · rintro ⟨k,hkn,hk⟩
      exact ⟨k,hkn,(sq_le_sq₀ ε.coe_nonneg (abs_nonneg _)).mp (by simpa only [sq_abs] using hk)⟩
    · rintro ⟨k,hkn,hk⟩
      exact ⟨k,hkn,by simpa only [sq_abs] using (sq_le_sq₀ ε.coe_nonneg (abs_nonneg _)).mpr hk⟩
  rw [he] at hm
  have hm' : (ε : ℝ≥0∞)^2 * sourceLaw {ω | ∃ k ≤ n, (ε : ℝ) ≤ |g (τ k) ω|} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ k ≤ n, (ε : ℝ) ≤ |g (τ k) ω|}, g (τ n) ω ^ 2 ∂sourceLaw) := by
    simpa only [ENNReal.coe_pow] using hm
  exact hm'.trans
    (ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hL2 (τ n)).integrable_sq
      (Eventually.of_forall (fun ω => sq_nonneg (g (τ n) ω)))))

/-- The actual full-input process has finite-grid maximum tail controlled by
its ORIGINAL full input L2 energy, at every grid and horizon, including zero. -/
theorem integralProcess_finite_grid_maximum (T : ℝ≥0) (f : fullPredictableL2 T)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (ε : ℝ≥0) (n : ℕ) :
    (ε : ℝ≥0∞)^2 * sourceLaw {ω | ∃ k ≤ n, (ε : ℝ) ≤ |integralProcess T f (τ k) ω|} ≤
      ENNReal.ofReal (‖f‖ ^ 2) := by
  apply (finite_grid_maximum τ hτ (integralProcess_martingale T f)
    (fun u => integralProcess_memLp_two T u f) ε n).trans
  apply ENNReal.ofReal_le_ofReal
  have he : (∫ ω, integralProcess T f (τ n) ω ^ 2 ∂sourceLaw) = ‖integralClassProcess T f (τ n)‖ ^ 2 := by
    rw [← processClass_eq_actual]
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(integralProcess_memLp_two T (τ n) f).coeFn_toLp] with ω hω
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    exact congrArg (fun x : ℝ => x^2) hω.symm
  rw [he]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (integralClassProcess_norm_le T (τ n) f)

/-- Sorting is only a finite clock operation; it adds no observation or source
permission. Thus arbitrary finite lists need not arrive in chronological order. -/
theorem integralProcess_arbitrary_finite_maximum (T : ℝ≥0) (f : fullPredictableL2 T)
    (τ : ℕ → ℝ≥0) (ε : ℝ≥0) (n : ℕ) :
    (ε : ℝ≥0∞)^2 * sourceLaw {ω | ∃ k ≤ n, (ε : ℝ) ≤ |integralProcess T f (τ k) ω|} ≤
      ENNReal.ofReal (‖f‖ ^ 2) := by
  classical
  let S : Finset ℝ≥0 := (Finset.range (n+1)).image τ
  have hp : 0 < S.card := Finset.card_pos.mpr ⟨τ 0,Finset.mem_image.mpr ⟨0,by simp,rfl⟩⟩
  let idx (k : ℕ) : Fin S.card := ⟨min k (S.card-1),lt_of_le_of_lt (min_le_right _ _) (by omega)⟩
  let σ (k : ℕ) := S.orderEmbOfFin rfl (idx k)
  have hσ : Monotone σ := fun i j hij => (S.orderEmbOfFin rfl).monotone (min_le_min_right _ hij)
  have hs : {ω | ∃ k ≤ n, (ε : ℝ) ≤ |integralProcess T f (τ k) ω|} ⊆
      {ω | ∃ j ≤ S.card-1, (ε : ℝ) ≤ |integralProcess T f (σ j) ω|} := by
    rintro ω ⟨k,hkn,hk⟩
    have hkS : τ k ∈ S := Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by omega),rfl⟩
    have hx : τ k ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hkS
    obtain ⟨j,hj⟩ := hx
    have hjle : (j : ℕ) ≤ S.card-1 := by omega
    refine ⟨j,hjle,?_⟩
    have he : σ j = τ k := by
      change S.orderEmbOfFin rfl (idx j) = τ k
      have hi : idx j = j := Fin.ext (min_eq_left hjle)
      rw [hi,hj]
    rwa [he]
  apply le_trans ?_ (integralProcess_finite_grid_maximum T f σ hσ ε (S.card-1))
  gcongr

/-- Genuine countable maximum control, by native continuity from below;
there is one bound for the UNION, rather than a divergent sum of endpoint bounds. -/
theorem integralProcess_countable_maximum (T : ℝ≥0) (f : fullPredictableL2 T)
    (τ : ℕ → ℝ≥0) (ε : ℝ≥0) :
    (ε : ℝ≥0∞)^2 * sourceLaw {ω | ∃ k, (ε : ℝ) ≤ |integralProcess T f (τ k) ω|} ≤
      ENNReal.ofReal (‖f‖ ^ 2) := by
  let A (n : ℕ) := {ω | ∃ k ≤ n, (ε : ℝ) ≤ |integralProcess T f (τ k) ω|}
  have hm : Monotone A := by
    intro n m hnm ω hω
    obtain ⟨k,hkn,hk⟩ := hω
    exact ⟨k,hkn.trans hnm,hk⟩
  have he : {ω | ∃ k, (ε : ℝ) ≤ |integralProcess T f (τ k) ω|} = ⋃ n, A n := by
    ext ω
    simp only [mem_ofPred_eq,mem_iUnion,A]
    exact ⟨fun ⟨k,hk⟩ => ⟨k,k,le_rfl,hk⟩,fun ⟨_,k,_,hk⟩ => ⟨k,hk⟩⟩
  rw [he,hm.directed_le.measure_iUnion,ENNReal.mul_iSup]
  exact iSup_le (fun n => integralProcess_arbitrary_finite_maximum T f τ ε n)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralMaximalControl
