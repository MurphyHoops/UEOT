import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralGridL1
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralEnergyL1
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianQuadraticVariation

/-!
Original commitment: the weighted Brownian QV theorem must consume the SAME actual literal integral and its actual time-energy.
Existing result: actual finite prefix paths, actual time-energy/marginal L1 classes and source weighted square-error law.
Premise reduced: derive literal-row time-energy and grid-increment identities, then bind the actual QV error to the original weighted source.
Model/witness: SAME original ElementaryInput T with original START permissions and nondecreasing 0/T clock, repeats allowed.
Consumer: actual uniform bounded-continuous input QV and full-input L1 extension; no QV limit or Ito certificate is supplied.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLiteralGridBinding
open MeasureTheory ProbabilityTheory Set Filter
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource BrownianOneStepIntegral
open BrownianCommonRefinement BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs
open BrownianPredictableDensity BrownianIntegralLiteralIntervals BrownianIntegralFinitePaths
open BrownianIntegralContinuousVersion BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralGridL1
open BrownianIntegralSquareL1 BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private def part {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : fullPredictableL2 T :=
  intervalInput T (r.clock i.castSucc) (r.clock i.succ)
    (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ)))
    ((r.clock_mono (Fin.le_last i.succ)).trans r.clock_end.le)
    (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)

private theorem cell_product_zero {T : ℝ≥0} (r : ElementaryInput T) (i j : Fin r.n) (hij : i ≠ j)
    (p : ℝ × (ℝ≥0 → ℝ)) :
    intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p *
      intervalIntegrand (r.coefficient j) (r.clock j.castSucc) (r.clock j.succ) p = 0 := by
  have hdis : ¬ (p.1 ∈ Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ) ∧
      p.1 ∈ Ioc (r.clock j.castSucc : ℝ) (r.clock j.succ : ℝ)) := by
    rintro ⟨hi,hj⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have hc : (r.clock i.succ : ℝ) ≤ (r.clock j.castSucc : ℝ) := by
        exact_mod_cast r.clock_mono (show i.succ ≤ j.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hi.2.trans hc)) hj.1
    · have hc : (r.clock j.succ : ℝ) ≤ (r.clock i.castSucc : ℝ) := by
        exact_mod_cast r.clock_mono (show j.succ ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hj.2.trans hc)) hi.1
  by_cases hi : p.1 ∈ Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)
  · have hj : p.1 ∉ Ioc (r.clock j.castSucc : ℝ) (r.clock j.succ : ℝ) := fun hj => hdis ⟨hi,hj⟩
    simp only [intervalIntegrand,Set.indicator_of_notMem hj,zero_mul,mul_zero]
  · simp only [intervalIntegrand,Set.indicator_of_notMem hi,zero_mul]

private theorem raw_square {T : ℝ≥0} (r : ElementaryInput T) (p : ℝ × (ℝ≥0 → ℝ)) :
    integrand r.clock r.coefficient p ^ 2 =
      ∑ i : Fin r.n, intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p ^ 2 := by
  simp only [integrand,pow_two,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    exact cell_product_zero r i j hji.symm p
  · simp

private theorem lp1_sum_coe {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (S : Finset ι) (F : ι → Lp ℝ 1 μ) :
    (∑ i ∈ S, F i : Lp ℝ 1 μ) =ᵐ[μ] fun a => ∑ i ∈ S, F i a := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 1 μ] with a ha
    simp only [Finset.sum_empty]
    exact ha
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ S, F j),ih] with a ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

private theorem square_input_parts {T : ℝ≥0} (r : ElementaryInput T) :
    squareClass (inputLaw T) (inputValue r) =
      ∑ i : Fin r.n, squareClass (inputLaw T) (part r i : Lp ℝ 2 (inputLaw T)) := by
  apply Lp.ext
  have hi : ∀ᵐ p ∂inputLaw T, ∀ i : Fin r.n,
      squareClass (inputLaw T) (part r i : Lp ℝ 2 (inputLaw T)) p =
        intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p ^ 2 :=
    ae_all_iff.mpr (fun i => (squareClass_coe _ _).trans
      ((intervalInput_coe T _ _ _ _ (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)).mono
        (fun _ h => congrArg (fun x : ℝ => x^2) h)))
  filter_upwards [squareClass_coe (inputLaw T) (inputValue r),
    (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
    lp1_sum_coe (inputLaw T) Finset.univ (fun i : Fin r.n => squareClass (inputLaw T) (part r i : Lp ℝ 2 (inputLaw T))),hi]
    with p hs hr hsum hi
  rw [hs,hsum]
  change (inputValue r p) = _ at hr
  rw [hr,raw_square]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)

/-- The SAME literal record's actual time-energy class is the sum of its
actual row interval energies, by original time-disjointness and native marginal linearity. -/
theorem energyClass_literal_parts {T : ℝ≥0} (r : ElementaryInput T) :
    energyClass T T (literalPredictableInput r) = ∑ i : Fin r.n, energyClass T T (part r i) := by
  simp_rw [energyClass_eq_marginal_square,BrownianIntegralTimeTruncation.truncate_horizon]
  change timeMarginal T (squareClass (inputLaw T) (inputValue r)) =
    ∑ i : Fin r.n, timeMarginal T (squareClass (inputLaw T) (part r i : Lp ℝ 2 (inputLaw T)))
  rw [square_input_parts,map_sum]

/-- Actual literal dt energy, retaining EVERY original coefficient and clock
row. It is not a separately supplied weighted-clock identity. -/
theorem timeEnergy_literal_horizon {T : ℝ≥0} (r : ElementaryInput T) :
    timeEnergy T (literalPredictableInput r) T =ᵐ[sourceLaw]
      fun ω => ∑ i : Fin r.n, ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*r.coefficient i ω^2 := by
  have he := (energyClass_coe T T (literalPredictableInput r)).symm
  rw [energyClass_literal_parts] at he
  apply he.trans
  have hi : ∀ᵐ ω ∂sourceLaw, ∀ i : Fin r.n, energyClass T T (part r i) ω =
      ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*r.coefficient i ω^2 :=
    ae_all_iff.mpr (fun i => (energyClass_coe T T (part r i)).trans
      (timeEnergy_interval_horizon T _ _ _ _ (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)))
  filter_upwards [lp1_sum_coe sourceLaw Finset.univ (fun i : Fin r.n => energyClass T T (part r i)),hi] with ω hs hi
  rw [hs]
  exact Finset.sum_congr rfl (fun i _ => hi i)

/-- The original record's ACTUAL finite-prefix path increment on its own
clock is literally its original allowed oneStep output, including repeated clocks. -/
theorem literalPath_increment {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) (ω : ℝ≥0 → ℝ) :
    literalPath r (r.clock i.succ) ω-literalPath r (r.clock i.castSucc) ω =
      oneStep (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) ω := by
  rw [literalPath,literalPath,← Finset.sum_sub_distrib,Finset.sum_eq_single i]
  · have hab : r.clock i.castSucc ≤ r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
    simp only [clamp,min_self,max_eq_right hab,min_eq_right hab,max_self]
    simp only [oneStep,Pi.mul_apply,increment,sub_self,mul_zero,sub_zero]
  · intro j _ hji
    have hj : r.clock j.castSucc ≤ r.clock j.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (j : ℕ))
    have hi : r.clock i.castSucc ≤ r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
    rcases lt_or_gt_of_ne hji with h | h
    · have hc : r.clock j.succ ≤ r.clock i.castSucc :=
        r.clock_mono (show j.succ ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
      simp only [clamp,min_eq_left hc,min_eq_left (hc.trans hi),max_eq_right hj,sub_self]
    · have hc : r.clock i.succ ≤ r.clock j.castSucc :=
        r.clock_mono (show i.succ ≤ j.castSucc by exact_mod_cast Nat.succ_le_of_lt h)
      simp only [clamp,min_eq_right (hc.trans hj),min_eq_right ((hi.trans hc).trans hj),
        max_eq_left hc,max_eq_left (hi.trans hc),sub_self]
  · simp

/-- Same native integral increment class returns the SAME original row;
there is no newly chosen finite strategy or unrelated source increment. -/
theorem integral_literal_increment_coe {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    (incrementAt T (r.clock i.castSucc) (r.clock i.succ) (literalPredictableInput r) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      oneStep (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) := by
  apply (incrementAt_coe T _ _ (literalPredictableInput r)).trans
  filter_upwards [continuousIntegralProcess_returns_literal r] with ω hω
  rw [hω,hω,literalPath_increment]

/-- The ACTUAL original integral-grid QV error minus its ACTUAL dt energy is
EXACTLY the original Brownian weighted error with weights original H_i squared.
This binding makes the source fourth-moment theorem a real consumer. -/
theorem literal_grid_error_coe {T : ℝ≥0} (r : ElementaryInput T) :
    (gridSquares T r.clock (literalPredictableInput r)-energyClass T T (literalPredictableInput r) : Lp ℝ 1 sourceLaw) =ᵐ[sourceLaw]
      errorSum r.clock (fun i ω => r.coefficient i ω^2) := by
  have hi : ∀ᵐ ω ∂sourceLaw, ∀ i : Fin r.n,
      (continuousIntegralProcess T (literalPredictableInput r) (r.clock i.succ) ω-
        continuousIntegralProcess T (literalPredictableInput r) (r.clock i.castSucc) ω)^2 =
        r.coefficient i ω^2*increment (r.clock i.castSucc) (r.clock i.succ) ω^2 := by
    filter_upwards [continuousIntegralProcess_returns_literal r] with ω hω
    intro i
    rw [hω,hω,literalPath_increment]
    simp only [oneStep,Pi.mul_apply,mul_pow]
  filter_upwards [Lp.coeFn_sub (gridSquares T r.clock (literalPredictableInput r)) (energyClass T T (literalPredictableInput r)),
    gridSquares_coe T r.clock (literalPredictableInput r),
    (energyClass_coe T T (literalPredictableInput r)).trans (timeEnergy_literal_horizon r),hi]
    with ω hd hg hA hi
  simp only [Pi.sub_apply] at hd
  rw [hd,hg,hA,errorSum_eq_weighted_difference]
  apply congrArg₂ (fun x y : ℝ => x-y)
  · exact Finset.sum_congr rfl (fun i _ => hi i)
  · exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLiteralGridBinding
