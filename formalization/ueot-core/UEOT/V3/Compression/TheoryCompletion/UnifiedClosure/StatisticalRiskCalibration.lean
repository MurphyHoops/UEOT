import UEOT.V3.BoundedLossTwoSided
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteHorizonRisk
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk

/-!
# Finite-sample calibration of the actual controlled source

Independent observations within each registered transition row estimate a
fixed finite family of bounded tests. Rows may share arbitrarily dependent
data: a finite union bound needs no independence between different rows.
The sampling law is the actual source row, whose expectation is proved to
equal the existing SISC transition-test expectation.

The simultaneous event can subsequently be used for a data-selected
partition, representative, reconstruction and policy. The test family, row
experiment, horizon, sample size and confidence radii are fixed before the
data; no online adaptive sampling, post-selected radius or unregistered
selected-test guarantee is asserted.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

noncomputable section

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling UEOT.V3.BoundedLossTwoSided
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

universe u uΩ uJ

/-- The population mean under the normalized source row is the very same
transition expectation used by the deterministic risk certificate. -/
theorem finiteKernelRowPMF_trueRisk
    {X A R O : Type u} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : UEOT.V3.FiniteStablePartition.Model X A R O)
    (test : X → ℝ) (a : A) (x : X) :
    trueRisk (finiteKernelRowPMF (modelAsFiniteKernel M) x a).toMeasure test =
      transitionTestExpectation M test a x := by
  unfold trueRisk
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, finiteKernelRowPMF_apply_toReal,
    modelAsFiniteKernel, transitionTestExpectation]

/-- Simultaneous bounded-test calibration for finitely many row experiments.
Only the observations within each row are required to be independent. -/
theorem measure_finite_row_calibration_bad_le
    {Ω : Type uΩ} {X I : Type u} {J : Type uJ}
    [MeasurableSpace Ω] [MeasurableSpace X] [Fintype I] [Fintype J]
    {N : ℕ} (hN : 0 < N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (law : J → Measure X) (test : J → I → X → ℝ)
    (sample : J → Fin N → Ω → X) (rho : J → ℝ)
    (htest : ∀ j i, Measurable (test j i))
    (hbounded : ∀ j i x, test j i x ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ j k, Measurable (sample j k))
    (hindep : ∀ j, iIndepFun (sample j) μ)
    (hlaw : ∀ j k, μ.map (sample j k) = law j)
    (hrho : ∀ j, 0 ≤ rho j) :
    μ.real {ω | ∃ j i,
      rho j < |empiricalRisk (test j i) (sample j) ω - trueRisk (law j) (test j i)|}
      ≤ ∑ j, (Fintype.card I : ℝ) *
        (2 * exp (-2 * (N : ℝ) * (rho j) ^ 2)) := by
  have hset :
      {ω | ∃ j i, rho j <
        |empiricalRisk (test j i) (sample j) ω - trueRisk (law j) (test j i)|} =
      ⋃ j, {ω | ∃ i, rho j <
        |empiricalRisk (test j i) (sample j) ω - trueRisk (law j) (test j i)|} := by
    ext ω
    simp
  rw [hset]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  exact Finset.sum_le_sum fun j _ =>
    measure_exists_candidate_bad_le hN μ (law j) (test j) (htest j)
      (hbounded j) (sample j) (hmeas j) (hindep j) (hlaw j) (hrho j)

/-- Actual empirical test means from the source-row observations. -/
def empiricalTransitionTests
    {Ω : Type uΩ} {X A I : Type u} {N : ℕ}
    (test : ℕ → I → X → ℝ)
    (sample : ℕ → A → X → Fin N → Ω → X) (ω : Ω) :
    ℕ → A → X → I → ℝ :=
  fun n a x i => empiricalRisk (test n i) (sample n a x) ω

/-- One event covers every registered time, source state, action and test. -/
def EmpiricalTransitionCalibrated
    {Ω : Type uΩ} {X A R O I : Type u} [Fintype X] {N : ℕ}
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
    (test : ℕ → I → X → ℝ)
    (sample : ℕ → A → X → Fin N → Ω → X)
    (rho : ℕ → ℝ) (T : ℕ) (ω : Ω) : Prop :=
  ∀ n, n < T → ∀ a x i,
    |transitionTestExpectation (M n) (test n i) a x -
      empiricalTransitionTests test sample ω n a x i| ≤ rho n

/-- Explicit confidence budget, with the number of tested rows and tests
visible. It may exceed one; no confidence claim below zero is implied. -/
def transitionCalibrationFailureBudget
    (X A I : Type u) [Fintype X] [Fintype A] [Fintype I]
    (N T : ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ row : Fin T × A × X, (Fintype.card I : ℝ) *
    (2 * exp (-2 * (N : ℝ) * (rho row.1) ^ 2))

/-- Actual per-row IID samples discharge the deterministic simultaneous
calibration premise with an explicit finite-sample failure probability. -/
theorem measure_empirical_transition_uncalibrated_le
    {Ω : Type uΩ} {X A R O I : Type u}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] [Fintype A] [Fintype I]
    {N : ℕ} (hN : 0 < N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
    (test : ℕ → I → X → ℝ)
    (sample : ℕ → A → X → Fin N → Ω → X) (rho : ℕ → ℝ) (T : ℕ)
    (htest : ∀ n, n < T → ∀ i, Measurable (test n i))
    (hbounded : ∀ n, n < T → ∀ i x, test n i x ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ n, n < T → ∀ a x k, Measurable (sample n a x k))
    (hindep : ∀ n, n < T → ∀ a x, iIndepFun (sample n a x) μ)
    (hlaw : ∀ n, n < T → ∀ a x k,
      μ.map (sample n a x k) =
        (finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n) :
    μ.real {ω | ¬ EmpiricalTransitionCalibrated M test sample rho T ω} ≤
      transitionCalibrationFailureBudget X A I N T rho := by
  let law : (Fin T × A × X) → Measure X := fun row =>
    (finiteKernelRowPMF (modelAsFiniteKernel (M row.1)) row.2.2 row.2.1).toMeasure
  have htail := measure_finite_row_calibration_bad_le hN μ law
    (fun row => test row.1) (fun row => sample row.1 row.2.1 row.2.2)
    (fun row => rho row.1)
    (fun row => htest row.1 row.1.isLt)
    (fun row => hbounded row.1 row.1.isLt)
    (fun row => hmeas row.1 row.1.isLt row.2.1 row.2.2)
    (fun row => hindep row.1 row.1.isLt row.2.1 row.2.2)
    (fun row => hlaw row.1 row.1.isLt row.2.1 row.2.2)
    (fun row => hrho row.1 row.1.isLt)
  apply le_trans (measureReal_mono ?_) htail
  intro ω hω
  change ¬ (∀ n, n < T → ∀ a x i,
    |transitionTestExpectation (M n) (test n i) a x -
      empiricalTransitionTests test sample ω n a x i| ≤ rho n) at hω
  push Not at hω
  obtain ⟨n, hn, a, x, i, hbad⟩ := hω
  refine ⟨(⟨n, hn⟩, a, x), i, ?_⟩
  simpa only [law, finiteKernelRowPMF_trueRisk, empiricalTransitionTests,
    abs_sub_comm] using hbad

section GoodEvent

variable {Ω : Type uΩ} {X A R O I : Type u}
variable [MeasurableSpace Ω] [MeasurableSpace X]
variable [Fintype X] [Fintype A] [Fintype I] {N : ℕ}
variable (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
variable (test : ℕ → I → X → ℝ)
variable (sample : ℕ → A → X → Fin N → Ω → X) (rho : ℕ → ℝ) (T : ℕ)

/-- The common good event is measurable before any partition or policy is
selected. No measurability of a later selection map is needed for its use. -/
theorem measurableSet_empirical_transition_calibrated
    (htest : ∀ n, n < T → ∀ i, Measurable (test n i))
    (hmeas : ∀ n, n < T → ∀ a x k, Measurable (sample n a x k)) :
    MeasurableSet {ω | EmpiricalTransitionCalibrated M test sample rho T ω} := by
  have hset : {ω | EmpiricalTransitionCalibrated M test sample rho T ω} =
      ⋂ n : Fin T, ⋂ a : A, ⋂ x : X, ⋂ i : I,
        {ω | |transitionTestExpectation (M n) (test n i) a x -
          empiricalTransitionTests test sample ω n a x i| ≤ rho n} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h n a x i
      exact h n n.isLt a x i
    · intro h n hn a x i
      exact h ⟨n, hn⟩ a x i
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun a =>
    MeasurableSet.iInter fun x => MeasurableSet.iInter fun i => ?_
  have hcomp : ∀ k : Fin N,
      Measurable (fun ω => test n i (sample n a x k ω)) :=
    fun k => (htest n n.isLt i).comp (hmeas n n.isLt a x k)
  have hemp : Measurable (fun ω => empiricalTransitionTests test sample ω n a x i) := by
    unfold empiricalTransitionTests empiricalRisk
    exact (Finset.measurable_sum Finset.univ (fun k _ => hcomp k)).div_const _
  exact measurableSet_le (measurable_const.sub hemp).abs measurable_const

end GoodEvent

section RepresentativeConclusion

variable {X A R O : Type u} [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O) (S : Setoid X)
variable (r : ReachableState (setoidRepresentation S) → X) (p₀ : PMF X)
variable (policy : ∀ n, CausalHistory (ReachableState (setoidRepresentation S))
  (A × ReachableState (setoidRepresentation S)) n → PMF A)
variable (delta eta rho kappa : ℕ → ℝ) (T : ℕ)

local notation "qS" => (toReachable (setoidRepresentation S))
local notation "microP" => (fun n x a => finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a)
local notation "macroQ" => (riskRepresentativeKernel qS r microP)

/-- This predicate contains only conclusions about the actual source and
representative deployment laws. The microscopic clause requires a proved
conservative envelope, so hidden failure is not silently treated as observed. -/
def RepresentativeRiskConclusion : Prop :=
  letI : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
  letI : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
  let source := causalLaw p₀ (riskMicroControlKernel qS microP policy) T
  let project := riskHistoryMap qS (fun ax : A × X => (ax.1, qS ax.2)) T
  let reference := causalLaw (p₀.map qS) (riskMacroControlKernel macroQ policy) T
  let epsilon := fun n => min 1 ((1 / 2 : ℝ) *
    ((Fintype.card (ReachableState (setoidRepresentation S)) : ℝ) *
      (2 * delta n + (eta n + 2 * rho n) * kappa n)))
  let budget := 1 - (∏ n ∈ Finset.range T, (1 - epsilon n))
  tvDist (source.map project).toMeasure reference.toMeasure ≤ budget ∧
  budget ≤ ∑ n ∈ Finset.range T, epsilon n ∧
  (∀ F, (source.map project).toMeasure.real F ≤
    min 1 (reference.toMeasure.real F + budget)) ∧
  (∀ E F, E ⊆ project ⁻¹' F → source.toMeasure.real E ≤
    min 1 (reference.toMeasure.real F + budget))

end RepresentativeConclusion

section UniformSelection

variable {Ω : Type uΩ} {X A R O I : Type u}
variable [Fintype X] [Fintype A] [Fintype I]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {N : ℕ}
variable (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
variable (test : ℕ → I → X → ℝ)
variable (sample : ℕ → A → X → Fin N → Ω → X) (rho : ℕ → ℝ) (T : ℕ)

/-- All subsequently selected representations and common policies are
covered by the same empirical calibration event. Reconstruction and measured
fibre checks remain explicit deterministic obligations of the selection.
The fixed test library, source and row experiment do not depend on `ω`. -/
def UniformEmpiricalRepresentativeRisk (ω : Ω) : Prop :=
  ∀ (S : Setoid X) (r : ReachableState (setoidRepresentation S) → X),
    (∀ y, toReachable (setoidRepresentation S) (r y) = y) →
  ∀ (p₀ : PMF X)
    (policy : ∀ n, CausalHistory (ReachableState (setoidRepresentation S))
      (A × ReachableState (setoidRepresentation S)) n → PMF A)
    (coeff : ℕ → X → I → ℝ) (delta eta kappa : ℕ → ℝ),
    (∀ n, n < T → ApproxSpansPartitionIndicators S (test n) (coeff n) (delta n)) →
    (∀ n, n < T → ∀ ⦃x y⦄, S.r x y → ∀ a i,
      |empiricalTransitionTests test sample ω n a x i -
        empiricalTransitionTests test sample ω n a y i| ≤ eta n) →
    (∀ n, n < T → 0 ≤ delta n) → (∀ n, n < T → 0 ≤ eta n) →
    (∀ n, n < T → 0 ≤ kappa n) →
    (∀ n, n < T → ∀ z, ∑ i, |coeff n z i| ≤ kappa n) →
    RepresentativeRiskConclusion M S r p₀ policy delta eta rho kappa T

/-- The generated simultaneous calibration premise feeds the already proved
representative path theorem and the actual microscopic envelope adapter. -/
theorem empirical_representative_risk_of_calibrated
    (hrho : ∀ n, n < T → 0 ≤ rho n) (ω : Ω)
    (hcal : EmpiricalTransitionCalibrated M test sample rho T ω) :
    UniformEmpiricalRepresentativeRisk M test sample rho T ω := by
  intro S r hr p₀ policy coeff delta eta kappa hspan hfit hd he hk hcondition
  letI : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
  letI : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
  have hpath := calibrated_representative_path_error M S r hr p₀ policy test coeff
    (empiricalTransitionTests test sample ω) delta eta rho kappa T
    hspan hcal hfit hd he hrho hk hcondition
  have hfailure := calibrated_representative_failure_risk M S r hr p₀ policy test coeff
    (empiricalTransitionTests test sample ω) delta eta rho kappa T
    hspan hcal hfit hd he hrho hk hcondition
  refine ⟨hpath.1, hpath.2, ?_, ?_⟩
  · intro F
    exact hfailure F (Set.to_countable F |>.measurableSet)
  · intro E F hEF
    exact (risk_microscopic_event_le_envelope _ _ (measurable_of_countable _)
      E F (Set.to_countable F |>.measurableSet) hEF).trans
        (hfailure F (Set.to_countable F |>.measurableSet))

variable [MeasurableSpace Ω]

/-- A measurable common event carries every successful data-selected
representative risk certificate. Confidence is spent once on the complete
registered experiment, without an extra union over chosen partitions or
policies. This is a training-data confidence statement; an unconditional
training-plus-deployment risk requires its own conditional deployment law.
The horizon, sample size and radii are fixed before the training data. -/
theorem statistical_representative_risk_certificate
    (hN : 0 < N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (htest : ∀ n, n < T → ∀ i, Measurable (test n i))
    (hbounded : ∀ n, n < T → ∀ i x, test n i x ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ n, n < T → ∀ a x k, Measurable (sample n a x k))
    (hindep : ∀ n, n < T → ∀ a x, iIndepFun (sample n a x) μ)
    (hlaw : ∀ n, n < T → ∀ a x k,
      μ.map (sample n a x k) =
        (finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n) :
    ∃ good : Set Ω, MeasurableSet good ∧
      μ.real goodᶜ ≤ transitionCalibrationFailureBudget X A I N T rho ∧
      ∀ ω ∈ good, UniformEmpiricalRepresentativeRisk M test sample rho T ω := by
  refine ⟨{ω | EmpiricalTransitionCalibrated M test sample rho T ω},
    measurableSet_empirical_transition_calibrated M test sample rho T htest hmeas,
    ?_, ?_⟩
  · exact measure_empirical_transition_uncalibrated_le hN μ M test sample rho T
      htest hbounded hmeas hindep hlaw hrho
  · intro ω hω
    exact empirical_representative_risk_of_calibrated M test sample rho T hrho ω hω

end UniformSelection

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
