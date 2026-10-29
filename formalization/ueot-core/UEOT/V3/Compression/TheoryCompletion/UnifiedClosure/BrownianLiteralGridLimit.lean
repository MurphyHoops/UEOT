import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLiteralGridBinding

/-!
Original commitment: same-source finite weighted Brownian QV must yield an actual integral-grid/dt-energy limit.
Existing result: literal_grid_error_coe binds original input/output grid error to original errorSum(H_i squared).
Premise reduced: derive actual source L1 error convergence from Gaussian weighted mean-square bounds and native probability norm comparison.
Model/witness: SAME ElementaryInput T family, actual computed mesh→0 and uniform SOURCE-AE coefficient bound K, not a global raw bound.
Consumer: bounded left-sampled integral QV and full-input L1 density extension; no general-input QV or Ito field is supplied.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLiteralGridLimit
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianIntegralClosure BrownianPredictableDensity BrownianQuadraticVariation
open BrownianIntegralGridL1 BrownianIntegralEnergyL1 BrownianLiteralGridBinding
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- General original literal arrays: their SAME actual grid square sum minus
SAME actual dt energy tends to zero in native source L1. Clocks and inputs may
both vary; this theorem does NOT rename that as fixed-input general QV. -/
theorem literal_grid_error_tendsto (T : ℝ≥0) (r : ℕ → ElementaryInput T)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ m i, ∀ᵐ ω ∂sourceLaw, |(r m).coefficient i ω| ≤ K)
    (hmesh : Tendsto (fun m => (mesh (r m).clock : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun m => gridSquares T (r m).clock (literalPredictableInput (r m))-
      energyClass T T (literalPredictableInput (r m))) atTop (𝓝 0) := by
  let W (m : ℕ) (i : Fin (r m).n) (ω : ℝ≥0 → ℝ) := (r m).coefficient i ω^2
  have hW (m : ℕ) (i : Fin (r m).n) : MemLp (W m i) ∞ sourceLaw := by
    simpa only [W,Pi.mul_def,pow_two] using
      ((r m).coefficient_bounded i).mul ((r m).coefficient_bounded i)
  have hWp (m : ℕ) (i : Fin (r m).n) :
      StronglyMeasurable[BrownianMartingaleSource.naturalFiltration ((r m).clock i.castSucc)] (W m i) :=
    ((r m).coefficient_past i).pow 2
  have hWb (m : ℕ) (i : Fin (r m).n) : ∀ᵐ ω ∂sourceLaw, |W m i ω| ≤ K^2 := by
    filter_upwards [hbound m i] with ω hω
    simpa only [W,abs_sq,sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr hω
  let U (m : ℕ) := errorSum (r m).clock (W m)
  have hU (m : ℕ) : MemLp (U m) 2 sourceLaw := errorSum_memLp_two _ _ (hW m)
  have hMSE : Tendsto (fun m => ∫ ω, U m ω^2 ∂sourceLaw) atTop (𝓝 0) := by
    have h := weightedQuadraticVariation_meanSquare_tendsto T (fun m => (r m).n)
      (fun m => (r m).clock) W (fun m => (r m).clock_mono) (fun m => (r m).clock_zero)
      (fun m => (r m).clock_end) hWp hW (K^2) (sq_nonneg K) hWb hmesh
    simpa only [← errorSum_eq_weighted_difference] using h
  let V (m : ℕ) : Lp ℝ 2 sourceLaw := (hU m).toLp (U m)
  have he (m : ℕ) : ‖V m‖^2 = ∫ ω, U m ω^2 ∂sourceLaw := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    apply integral_congr_ae
    exact (hU m).coeFn_toLp.mono (fun _ h => congrArg (fun x : ℝ => x^2) h)
  have hV : Tendsto (fun m => ‖V m‖) atTop (𝓝 0) := by
    have hs := (tendsto_congr' (Eventually.of_forall he)).mpr hMSE
    have hr := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hr
  have hnorm (m : ℕ) : ‖gridSquares T (r m).clock (literalPredictableInput (r m))-
      energyClass T T (literalPredictableInput (r m))‖ ≤ ‖V m‖ := by
    have heq : gridSquares T (r m).clock (literalPredictableInput (r m))-
        energyClass T T (literalPredictableInput (r m)) = ((hU m).integrable one_le_two).toL1 (U m) := by
      apply Lp.ext
      exact (literal_grid_error_coe (r m)).trans ((hU m).integrable one_le_two).coeFn_toL1.symm
    rw [heq]
    simp only [Integrable.toL1,V,Lp.norm_toLp]
    exact ENNReal.toReal_mono (hU m).eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le (show (1 : ℝ≥0∞) ≤ 2 by norm_num) (hU m).aestronglyMeasurable)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hnorm hV

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLiteralGridLimit
