import UEOT
namespace BoundedDensityIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralLiteralIntervals BrownianIntegralTimeEnergy
open BrownianFiniteDensityL2Source BrownianFiniteStepExponentialSource BrownianFiniteStepShiftedSource
open BrownianBoundedPredictableApproximation BrownianBoundedExponentialLimitSource BrownianBoundedControlSource
open UEOT.V3.GirsanovPathKL
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

-- Fresh nonsmooth START1 feedback. This is a genuine discontinuous predictable
-- block, not an assumed continuous-time raw Lp representative.
def H (w : ℝ≥0 → ℝ) : ℝ := if 0≤process 1 w then 3/2 else 1/2
theorem H_past : StronglyMeasurable[naturalFiltration 1] H := by
  let : MeasurableSpace (ℝ≥0 → ℝ) := naturalFiltration 1
  have hs : MeasurableSet {w : ℝ≥0 → ℝ | 0≤process 1 w} :=
    measurableSet_le measurable_const (process_stronglyAdapted 1).measurable
  exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
theorem H_bound (w : ℝ≥0 → ℝ) : ‖H w‖≤(3/2 : ℝ) := by unfold H; split_ifs <;> norm_num
theorem H_top : MemLp H ∞ sourceLaw :=
  MemLp.of_bound (H_past.mono (naturalFiltration.le 1)).aestronglyMeasurable (3/2) (ae_of_all _ H_bound)

def f : fullPredictableL2 2 := intervalInput 2 1 2 (by norm_num) le_rfl H H_past H_top
theorem f_bound : ∀ᵐ p ∂inputLaw 2, |(f : Lp ℝ 2 (inputLaw 2)) p|≤(3/2 : ℝ) := by
  filter_upwards [intervalInput_coe 2 1 2 (by norm_num) le_rfl H H_past H_top] with p hp
  change (f : Lp ℝ 2 (inputLaw 2)) p=intervalIntegrand H 1 2 p at hp
  rw [hp]
  unfold intervalIntegrand
  change |(Ioc (1 : ℝ) 2).indicator (fun _=>1) p.1*H p.2|≤3/2
  by_cases ht : p.1∈Ioc (1 : ℝ) 2
  · rw [Set.indicator_of_mem ht,one_mul]
    exact H_bound p.2
  · simp only [Set.indicator_of_notMem ht,zero_mul,abs_zero]
    norm_num

def actualTable (n : ℕ) : ElementaryInput 2 :=
  BrownianBoundedPredictableApproximation.approximation 2 f (3/2) (by norm_num) f_bound n

-- No external approximant-exists or UI premise. These are SAME derived tables.
example (n : ℕ) := approximation_bound 2 f (3/2) (by norm_num) f_bound n
example := approximation_full_tendsto 2 f (3/2) (by norm_num) f_bound
example := approximation_outputs_tendsto 2 f (3/2) (by norm_num) f_bound
example := approximation_energy_tendsto 2 f (3/2) (by norm_num) f_bound 2
example := approximation_densities_uniformIntegrable 2 f (3/2) (by norm_num) f_bound
example (n : ℕ) (w : ℝ≥0 → ℝ) : terminalDensity (actualTable n) w^2=
    terminalDensity (scaleTable (actualTable n) 2) w*Real.exp (tableEnergy (actualTable n) w) :=
  density_square_factor _ _
example (n : ℕ) : Integrable (fun w=>terminalDensity (actualTable n) w^2) sourceLaw ∧
    (∫ w, terminalDensity (actualTable n) w^2 ∂sourceLaw)≤Real.exp ((3/2 : ℝ)^2*2) := by
  apply bounded_density_square _ (3/2) (by norm_num)
  intro i
  exact ae_of_all _ (fun w=>approximation_bound 2 f (3/2) (by norm_num) f_bound n i w)
-- These EXACT derived finite controls consume the previously reviewed actual-Q path source.
example (n : ℕ) := tableProcess_isBrownian (actualTable n)
example (n : ℕ) := BrownianFiniteStepTerminalKLSource.actualTerminalData (actualTable n)

example (w : ℝ≥0 → ℝ) : fullDensity 2 f w=
    Real.exp ((predictableIntegral 2 f : (ℝ≥0 → ℝ) → ℝ) w-(1/2 : ℝ)*timeEnergy 2 f 2 w) := rfl
example := actual_densities_tendstoInMeasure 2 f (3/2) (by norm_num) f_bound
example := actual_densities_tendsto_L1 2 f (3/2) (by norm_num) f_bound
example : (∫ w, fullDensity 2 f w ∂sourceLaw)=1 := fullDensity_mean_one 2 f (3/2) (by norm_num) f_bound
example : IsProbabilityMeasure (fullLaw 2 f) := fullLaw_probability 2 f (3/2) (by norm_num) f_bound
example := fullLaw_rnDeriv 2 f

-- Actual real-time control is chosen from native predictable sigma then mask,
-- bound globally while matching SAME f in dt times originalP class.
example := control_progressive 2 f (3/2)
example := control_input_ae 2 f (3/2) f_bound
example (w : ℝ≥0 → ℝ) : control 2 f (3/2) (-1) w=0 ∧ control 2 f (3/2) 3 w=0 := by
  constructor <;> unfold BrownianBoundedControlSource.control <;> apply Set.indicator_of_notMem <;> norm_num
example := drift_stronglyAdapted 2 f (3/2)
example (w : ℝ≥0 → ℝ) := drift_continuous 2 f (3/2) (by norm_num) w
example := control_energy_eq_actual 2 f (3/2) f_bound
example : controlEnergy 2 (control 2 f (3/2))=ᵐ[fullLaw 2 f] timeEnergy 2 f 2 :=
  (fullLaw_absolutelyContinuous 2 f).ae_le (control_energy_eq_actual 2 f (3/2) f_bound)
example := shiftedProcess_stronglyAdapted 2 f (3/2)
example (w : ℝ≥0 → ℝ) := shiftedProcess_continuous 2 f (3/2) (by norm_num) w
example (w : ℝ≥0 → ℝ) : drift 2 f (3/2) 3 w=drift 2 f (3/2) 2 w := drift_after 2 f (3/2) 3 (by norm_num) w

-- K0/zero horizon boundary does not secretly require a nonempty sample/time cell.
theorem zero_bound : ∀ᵐ p ∂inputLaw 0, |(0 : Lp ℝ 2 (inputLaw 0)) p|≤(0 : ℝ) := by
  filter_upwards [Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=inputLaw 0)] with p hp
  rw [hp];norm_num
example : (∫ w, fullDensity 0 0 w ∂sourceLaw)=1 := fullDensity_mean_one 0 0 0 le_rfl zero_bound
example : IsProbabilityMeasure (fullLaw 0 0) := fullLaw_probability 0 0 0 le_rfl zero_bound
example (g : fullPredictableL2 0) (K : ℝ) (s : ℝ≥0) (w : ℝ≥0 → ℝ) : drift 0 g K s w=0 := drift_horizon_zero g K s w

#print axioms density_square_factor
#print axioms densities_uniformIntegrable
#print axioms exists_bounded_table_dist_lt
#print axioms approximation_full_tendsto
#print axioms actual_densities_tendsto_L1
#print axioms fullDensity_mean_one
#print axioms fullLaw_probability
#print axioms control_progressive
#print axioms control_input_ae
#print axioms control_energy_eq_actual
#print axioms drift_continuous
#print axioms shiftedProcess_continuous
end
end BoundedDensityIndependent

namespace BoundedDensityIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianBoundedDriftLimitSource BrownianBoundedMovingLawSource
open scoped NNReal ENNReal Topology BoundedContinuousFunction
noncomputable section
-- SAME nonsmooth source input from the independent density audit, not a new
-- approximant or caller-supplied density/control law.
example : TendstoInMeasure sourceLaw
    (fun n => BrownianFiniteStepShiftedSource.tableProcess (actualTable n) 3) atTop
      (BrownianBoundedControlSource.shiftedProcess 2 f (3/2) 3) :=
  actual_paths_tendstoInMeasure 2 3 f (3/2) (by norm_num) f_bound
example (s : ℝ≥0) := actual_drifts_tendstoInMeasure 2 s f (3/2) (by norm_num) f_bound
example {T : ℝ≥0} (r : ElementaryInput T) (s : ℝ≥0) (w : ℝ≥0 → ℝ) :=
  literal_time_integral r s w
-- A discontinuous ORIGINAL START-past factor survives the moving-law limit.
-- This is not merely the unweighted finite Brownian marginal identity.
example (I : Finset ℝ≥0) (phi : (I → ℝ) →ᵇ ℝ) :=
  actual_finite_tests_tendsto 2 f (3/2) (by norm_num) f_bound I H
    (H_past.mono (naturalFiltration.le 1)).measurable (3/2) (by norm_num) H_bound phi
example (phi : (({0,1/2,1,3/2,2,3} : Finset ℝ≥0) → ℝ) →ᵇ ℝ) :=
  actual_finite_tests_tendsto 2 f (3/2) (by norm_num) f_bound {0,1/2,1,3/2,2,3} H
    (H_past.mono (naturalFiltration.le 1)).measurable (3/2) (by norm_num) H_bound phi
example := actual_finite_paths_tendstoInMeasure 0 0 0 le_rfl zero_bound ∅
#print axioms driftClass_coe
#print axioms actual_paths_tendstoInMeasure
#print axioms actual_weighted_tests_tendsto
#print axioms actual_finite_tests_tendsto
end
end BoundedDensityIndependent

namespace BoundedDensityIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianBoundedControlSource BrownianBoundedExponentialLimitSource BrownianBoundedGirsanovSource
open scoped NNReal ENNReal Topology
noncomputable section
-- Fresh nonsmooth source: full Brownian/path/martingale on SAME actualQ.
example : IsBrownianReal (shiftedProcess 2 f (3/2)) (fullLaw 2 f) :=
  full_isBrownian 2 f (3/2) (by norm_num) f_bound
example := full_finite_hasLaw 2 f (3/2) (by norm_num) f_bound {0,1/2,1,3/2,2,3}
example (s : ℝ≥0) := full_future_indep_original_past 2 f (3/2) (by norm_num) f_bound s
example (s : ℝ≥0) (I : Finset ℝ≥0) (A : Set (ℝ≥0 → ℝ))
    (hA : MeasurableSet[naturalFiltration s] A) :=
  full_future_restricted_law 2 f (3/2) (by norm_num) f_bound s I A hA
example : Martingale (shiftedProcess 2 f (3/2)) naturalFiltration (fullLaw 2 f) :=
  full_process_martingale 2 f (3/2) (by norm_num) f_bound
example (s t : ℝ≥0) (hst : s≤t) :=
  full_increment_condExp_zero 2 f (3/2) (by norm_num) f_bound s t hst
example := full_isBrownian 0 0 0 le_rfl zero_bound
example (s : ℝ≥0) := full_future_indep_original_past 0 0 0 le_rfl zero_bound s
#print axioms full_isBrownian
#print axioms full_future_restricted_law
#print axioms full_future_indep_original_past
#print axioms full_process_martingale
end
end BoundedDensityIndependent
