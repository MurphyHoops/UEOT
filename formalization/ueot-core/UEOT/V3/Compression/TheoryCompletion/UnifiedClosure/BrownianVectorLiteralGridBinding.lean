import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorQuadraticVariation

/-!
Original commitment: vector-table error limits must bind the SAME actual integral's grid and actual dt energy, not an unrelated row sum.
Existing result: source-derived vector matrix error/mesh bound and native full-input grid/energy classes and continuous literal returns.
Premise reduced: derive literal-path row increments and actual Euclidean energy decomposition, then identify actual native grid error with SAME matrixErrorSum.
Model: unchanged ElementaryInput d T/inputLaw/productLaw/jointNaturalFiltration, finite d0/T0/repeated clocks and whole-joint START coefficients.
Consumer: original literal-grid L1 limit and full-input QV extension; no changed strategy/measure/permission or desired QV field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorLiteralGridBinding
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianVectorIntegralConditionalSource BrownianVectorIntegralFinitePaths BrownianVectorIntegralContinuousVersion
open BrownianVectorIntegralGridL1 BrownianVectorIntegralTimeEnergy BrownianVectorIntegralEnergyL1
open BrownianVectorQuadraticVariation BrownianIntegralSquareL1
open BrownianCommonRefinement (clamp)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

private def part {T : ℝ≥0} (r : ElementaryInput d T) (i : Fin r.n) : fullPredictableL2 d T :=
  BrownianVectorIntegralConditionalSource.intervalInput d T (r.clock i.castSucc) (r.clock i.succ)
    (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ)))
    ((r.clock_mono (Fin.le_last i.succ)).trans r.clock_end.le)
    (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)

private theorem raw_norm_square {T : ℝ≥0} (r : ElementaryInput d T) (p : ℝ×Sample d) :
    ‖integrand d r.clock r.coefficient p‖^2=
      ∑ i : Fin r.n,‖BrownianVectorTimeInput.intervalInput d (r.coefficient i)
        (r.clock i.castSucc) (r.clock i.succ) p‖^2 := by
  simp only [integrand,← real_inner_self_eq_norm_sq,sum_inner,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    apply intervalInput_nonoverlap
    rcases lt_or_gt_of_ne hji with h | h
    · exact Or.inl (r.clock_mono (show j.succ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt h))
    · exact Or.inr (r.clock_mono (show i.succ≤j.castSucc by exact_mod_cast Nat.succ_le_of_lt h))
  · simp

private theorem normSquare_input_parts {T : ℝ≥0} (r : ElementaryInput d T) :
    normSquareClass (inputLaw d T) (literalPredictableInput d r : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))=
      ∑ i : Fin r.n,normSquareClass (inputLaw d T)
        (part d r i : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) := by
  apply Lp.ext
  have hi : ∀ᵐ p ∂inputLaw d T,∀ i : Fin r.n,
      normSquareClass (inputLaw d T) (part d r i : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p=
        ‖BrownianVectorTimeInput.intervalInput d (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p‖^2 :=
    ae_all_iff.mpr (fun i=>(normSquareClass_coe (inputLaw d T)
      (part d r i : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))).trans
      ((intervalInput_coe d T _ _ _ _ (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)).mono
        (fun _ h=>congrArg (fun x : EuclideanSpace ℝ (Fin d)=>‖x‖^2) h)))
  filter_upwards [normSquareClass_coe (inputLaw d T)
    (literalPredictableInput d r : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)),
    (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin r.n=>normSquareClass (inputLaw d T)
      (part d r i : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))),hi] with p hs hr hsum hi
  change (literalPredictableInput d r : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p=
    integrand d r.clock r.coefficient p at hr
  rw [hs,hr,raw_norm_square,hsum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _=>(hi i).symm)

/-- Actual original dt-energy class is the sum of the actual disjoint blocks'
energy classes. Euclidean cross terms vanish from real clock separation. -/
theorem energyClass_literal_parts {T : ℝ≥0} (r : ElementaryInput d T) :
    energyClass d T T (literalPredictableInput d r)=∑ i : Fin r.n,energyClass d T T (part d r i) := by
  rw [energyClass_eq_marginal_normSquare,truncate_horizon,normSquare_input_parts,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [energyClass_eq_marginal_normSquare,truncate_horizon]

/-- Actual original input dt energy returns the SAME original coefficient
Euclidean norm-square and clock. This is stronger than equality in expectation. -/
theorem timeEnergy_literal_horizon {T : ℝ≥0} (r : ElementaryInput d T) :
    timeEnergy d T (literalPredictableInput d r) T =ᵐ[productLaw d]
      fun ω=>∑ i : Fin r.n,((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*‖coefficient d (r.coefficient i) ω‖^2 := by
  have he := (energyClass_coe d T T (literalPredictableInput d r)).symm
  rw [energyClass_literal_parts] at he
  apply he.trans
  have hi : ∀ᵐ ω ∂productLaw d,∀ i : Fin r.n,energyClass d T T (part d r i) ω=
      ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*‖coefficient d (r.coefficient i) ω‖^2 :=
    ae_all_iff.mpr (fun i=>(energyClass_coe d T T (part d r i)).trans
      (timeEnergy_interval_horizon d T _ _ _ _ (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin r.n=>energyClass d T T (part d r i)),hi]
    with ω hs hi
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _=>hi i)

/-- SAME original literal vector path increment, pointwise including repeated
clock cells. No source-a.e. row identity or new path is supplied as a field. -/
theorem literalPath_increment {T : ℝ≥0} (r : ElementaryInput d T) (i : Fin r.n) (ω : Sample d) :
    literalPath d r (r.clock i.succ) ω-literalPath d r (r.clock i.castSucc) ω=
      oneStep d (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) ω := by
  rw [literalPath,literalPath,← Finset.sum_sub_distrib,Finset.sum_eq_single i]
  · have hab : r.clock i.castSucc≤r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
    simp only [clamp,min_self,max_eq_right hab,min_eq_right hab,max_self]
    simp only [oneStep,component,Pi.mul_apply,coordinateIncrement,sub_self,mul_zero,Finset.sum_const_zero,sub_zero]
  · intro j _ hji
    have hj : r.clock j.castSucc≤r.clock j.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (j : ℕ))
    have hi : r.clock i.castSucc≤r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
    rcases lt_or_gt_of_ne hji with h | h
    · have hc : r.clock j.succ≤r.clock i.castSucc :=
        r.clock_mono (show j.succ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
      simp only [clamp,min_eq_left hc,min_eq_left (hc.trans hi),max_eq_right hj,sub_self]
    · have hc : r.clock i.succ≤r.clock j.castSucc :=
        r.clock_mono (show i.succ≤j.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
      simp only [clamp,min_eq_right (hc.trans hj),min_eq_right ((hi.trans hc).trans hj),
        max_eq_left hc,max_eq_left (hi.trans hc),sub_self]
  · simp

theorem integral_literal_increment_coe {T : ℝ≥0} (r : ElementaryInput d T) (i : Fin r.n) :
    (incrementAt d T (r.clock i.castSucc) (r.clock i.succ) (literalPredictableInput d r) : Sample d→ℝ)
      =ᵐ[productLaw d] oneStep d (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) := by
  apply (incrementAt_coe d T _ _ (literalPredictableInput d r)).trans
  filter_upwards [continuousIntegralProcess_returns_literal d r] with ω hω
  rw [hω,hω,literalPath_increment]

/-- Actual SAME full-integral native grid minus actual SAME input dt energy
is literally the original table's source-derived matrixErrorSum. -/
theorem literal_grid_error_coe {T : ℝ≥0} (r : ElementaryInput d T) :
    (gridSquares d T r.clock (literalPredictableInput d r)-energyClass d T T (literalPredictableInput d r) :
      Lp ℝ 1 (productLaw d)) =ᵐ[productLaw d] matrixErrorSum d r.clock r.coefficient := by
  filter_upwards [Lp.coeFn_sub (gridSquares d T r.clock (literalPredictableInput d r))
      (energyClass d T T (literalPredictableInput d r)),
    gridSquares_coe d T r.clock (literalPredictableInput d r),energyClass_coe d T T (literalPredictableInput d r),
    timeEnergy_literal_horizon d r,continuousIntegralProcess_returns_literal d r] with ω hd hq ha hA hpath
  simp only [Pi.sub_apply] at hd
  rw [hd,hq,ha,hA,matrixErrorSum_eq_table,Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hpath,hpath,literalPath_increment]

/-- Actual original literal arrays, not fixed-input general QV: SAME native
grid minus SAME actual dt energy tends to zero in original source L1. -/
theorem literal_grid_error_tendsto (T : ℝ≥0) (r : ℕ→ElementaryInput d T)
    (K : ℝ) (hK : 0≤K) (hbound : ∀ m i k,∀ᵐ ω ∂productLaw d,|(r m).coefficient i k ω|≤K)
    (hmesh : Tendsto (fun m=>(BrownianQuadraticVariation.mesh (r m).clock : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun m=>gridSquares d T (r m).clock (literalPredictableInput d (r m))-
      energyClass d T T (literalPredictableInput d (r m))) atTop (𝓝 0) := by
  let U (m : ℕ) := matrixErrorSum d (r m).clock (r m).coefficient
  have hU (m : ℕ) : MemLp (U m) 2 (productLaw d) :=
    matrixErrorSum_memLp_two d _ _ (r m).coefficient_bounded
  have hMSE : Tendsto (fun m=>∫ ω,U m ω^2 ∂productLaw d) atTop (𝓝 0) :=
    matrixErrorSum_meanSquare_tendsto d T (fun m=>(r m).n) (fun m=>(r m).clock)
      (fun m=>(r m).coefficient) (fun m=>(r m).clock_mono) (fun m=>(r m).clock_zero)
      (fun m=>(r m).clock_end) (fun m=>(r m).coefficient_past) (fun m=>(r m).coefficient_bounded)
      K hK hbound hmesh
  let V (m : ℕ) : Lp ℝ 2 (productLaw d) := (hU m).toLp (U m)
  have he (m : ℕ) : ‖V m‖^2=∫ ω,U m ω^2 ∂productLaw d := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    exact integral_congr_ae ((hU m).coeFn_toLp.mono (fun _ h=>congrArg (fun x : ℝ=>x^2) h))
  have hV : Tendsto (fun m=>‖V m‖) atTop (𝓝 0) := by
    have hs := (tendsto_congr' (Eventually.of_forall he)).mpr hMSE
    have hr := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hr
  have hnorm (m : ℕ) : ‖gridSquares d T (r m).clock (literalPredictableInput d (r m))-
      energyClass d T T (literalPredictableInput d (r m))‖≤‖V m‖ := by
    have heq : gridSquares d T (r m).clock (literalPredictableInput d (r m))-
        energyClass d T T (literalPredictableInput d (r m))=((hU m).integrable one_le_two).toL1 (U m) := by
      apply Lp.ext
      exact (literal_grid_error_coe d (r m)).trans ((hU m).integrable one_le_two).coeFn_toL1.symm
    rw [heq]
    simp only [Integrable.toL1,V,Lp.norm_toLp]
    exact ENNReal.toReal_mono (hU m).eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le (show (1 : ℝ≥0∞)≤2 by norm_num) (hU m).aestronglyMeasurable)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  exact squeeze_zero (fun _=>norm_nonneg _) hnorm hV

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorLiteralGridBinding
