import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRisk
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRisk

/-!
# Unequal registered samples and Good-only selected deployment risk

The same registered source experiment calibrates every row before data-dependent
selection. Empirical fit, actual occupancy caps, the microscopic event envelope
and the numerical risk check all concern that one calibration event. The source
process, registration, sample allocation and microscopic event are fixed inputs.

The theorem derives true row errors and the actual selected source risk, then
uses the established training/deployment mixture bound. The observation alphabet need not be finite; the selected reference event is
explicitly measurable on Good. The bad event is charged once. No complete calibration or source-risk bound is assumed as a premise.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace VariableRegisteredJointCheck

open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe uΩ uC u

/-- The same source rows are calibrated before selection, with fixed per-row
sample allocations. The event is the canonical simultaneous source-to-empirical
TV condition, not a new asserted probability estimate. -/
def RegisteredCalibrationGood
    {Ω : Type uΩ} {X A : Type u} [MeasurableSpace X]
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop) (T : ℕ)
    (N : CoverageRegisteredRow certified T → ℕ) (hN : ∀ j, 0 < N j)
    (sample : ∀ j : CoverageRegisteredRow certified T, Fin (N j) → Ω → X)
    (rho : ℕ → ℝ) (ω : Ω) : Prop :=
  ∀ j : CoverageRegisteredRow certified T,
    tvDist (P j.1.1 j.1.2.2 j.1.2.1).toMeasure
      (empiricalResponsePMF (hN j) (sample j) ω).toMeasure ≤ rho j.1.1

/-- Specialize the established variable-row confidence budget to the exact
registered source rows; no maximum/minimum sample-count replacement. -/
def registeredConfidenceBudget
    {X A : Type u} [Fintype X] [Fintype A]
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (N : CoverageRegisteredRow certified T → ℕ) (rho : ℕ → ℝ) : ℝ :=
  VariableRegisteredSamples.confidenceBudget X N (fun j => rho j.1.1)

/-- The variable-row calibration event is contained in the canonical TV
event; the latter inherits the same actual training failure budget. -/
theorem registered_calibration_good_bad_le
    {Ω : Type uΩ} {X A : Type u}
    [Fintype Ω] [Fintype X] [Fintype A]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (training : Measure Ω) [IsProbabilityMeasure training]
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop) (T : ℕ)
    (N : CoverageRegisteredRow certified T → ℕ) (hN : ∀ j, 0 < N j)
    (sample : ∀ j : CoverageRegisteredRow certified T, Fin (N j) → Ω → X)
    (rho : ℕ → ℝ)
    (hmeas : ∀ j k, Measurable (sample j k))
    (hindep : ∀ j, iIndepFun (sample j) training)
    (hlaw : ∀ j k, training.map (sample j k) =
      (P j.1.1 j.1.2.2 j.1.2.1).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n) :
    MeasurableSet {ω | RegisteredCalibrationGood P certified T N hN sample rho ω} ∧
      training.real {ω | ¬ RegisteredCalibrationGood P certified T N hN sample rho ω} ≤
        registeredConfidenceBudget certified T N rho := by
  obtain ⟨good, _hgood, hbad, hcal⟩ :=
    VariableRegisteredSamples.registered_row_calibration N hN training
      (fun j : CoverageRegisteredRow certified T => P j.1.1 j.1.2.2 j.1.2.1)
      sample (fun j => rho j.1.1) hmeas hindep hlaw
      (fun j => hrho j.1.1 j.1.1.isLt)
  refine ⟨Set.to_countable _ |>.measurableSet, ?_⟩
  have hsub :
      {ω | ¬ RegisteredCalibrationGood P certified T N hN sample rho ω} ⊆ goodᶜ := by
    intro ω hω hg
    exact hω (hcal ω hg)
  exact (measureReal_mono hsub).trans hbad

/-- Unequal fixed sample allocations, selected empirical fits, and actual
selected-policy occupancy caps yield the same sharp joint mixture budget.

All fit, occupancy, envelope and numerical checks concern the SAME Good
event. The microscopic event E, actual source P, registration and N are
fixed before sampling. The proof creates the true row TV estimates locally
and uses the existing sampling-free source-risk endpoint, then the existing
selectedTrainingDeployment_failure_le. No calibration or joint probability
bound is included as a caller hypothesis. -/
theorem registered_selected_joint_failure_of_cap_on_good
    {Ω : Type uΩ} {C : Type uC} {X Y A : Type u}
    [Fintype Ω] [Fintype X] [Fintype A]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [MeasurableSpace C]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (training : Measure Ω) [IsProbabilityMeasure training]
    (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (N : CoverageRegisteredRow certified T → ℕ) (hN : ∀ j, 0 < N j)
    (sample : ∀ j : CoverageRegisteredRow certified T, Fin (N j) → Ω → X)
    (rho : ℕ → ℝ)
    (hmeas : ∀ j k, Measurable (sample j k))
    (hindep : ∀ j, iIndepFun (sample j) training)
    (hlaw : ∀ j k, training.map (sample j k) =
      (P j.1.1 j.1.2.2 j.1.2.1).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n)
    (select : Ω → C) (q : C → X → Y) (initial : C → PMF X)
    (Q : C → ℕ → Y → A → PMF Y)
    (policy : C → ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (eta kappa : Ω → ℕ → ℝ)
    (hfit : ∀ ω, RegisteredCalibrationGood P certified T N hN sample rho ω →
      ∀ n (hn : n < T) x a (hc : certified n x a),
      tvDist ((empiricalResponsePMF
        (hN ⟨(⟨n, hn⟩, a, x), hc⟩)
        (sample ⟨(⟨n, hn⟩, a, x), hc⟩) ω).map
          (q (select ω))).toMeasure
        (Q (select ω) n (q (select ω) x) a).toMeasure ≤ eta ω n)
    (hcap : ∀ ω, RegisteredCalibrationGood P certified T N hN sample rho ω →
      ∀ n, n < T →
      (coverageDeploymentRowLaw (initial (select ω)) (q (select ω)) P
        (policy (select ω)) n).toMeasure.real {xa | ¬ certified n xa.1 xa.2} ≤ kappa ω n)
    (E : Set (CausalHistory X (A × X) T))
    (F : C → Set (CausalHistory Y (A × Y) T))
    (hF : ∀ ω, RegisteredCalibrationGood P certified T N hN sample rho ω →
      MeasurableSet (F (select ω)))
    (henvelope : ∀ ω, RegisteredCalibrationGood P certified T N hN sample rho ω →
      E ⊆ (riskHistoryMap (q (select ω))
        (fun ax : A × X => (ax.1, q (select ω) ax.2)) T) ⁻¹' F (select ω))
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hchecked : ∀ ω, RegisteredCalibrationGood P certified T N hN sample rho ω →
      min 1 ((causalLaw ((initial (select ω)).map (q (select ω)))
        (riskMacroControlKernel (Q (select ω)) (policy (select ω))) T).toMeasure.real
          (F (select ω)) +
        ∑ n ∈ Finset.range T, (min 1 (rho n + eta ω n) +
          (1 - min 1 (rho n + eta ω n)) * kappa ω n)) ≤ β) :
    Measurable select ∧
      (selectedTrainingDeployment training.toPMF select
        (fun c => causalLaw (initial c) (riskMicroControlKernel (q c) P (policy c)) T)).toMeasure.real
          {z | z.2 ∈ E} ≤
        min 1 (registeredConfidenceBudget certified T N rho +
          (1 - registeredConfidenceBudget certified T N rho) * β) := by
  obtain ⟨_hgood, hbad⟩ := registered_calibration_good_bad_le training
    P certified T N hN sample rho hmeas hindep hlaw hrho
  refine ⟨measurable_of_finite _, ?_⟩
  apply selectedTrainingDeployment_failure_le training.toPMF select
    (fun c => causalLaw (initial c) (riskMicroControlKernel (q c) P (policy c)) T)
    {ω | RegisteredCalibrationGood P certified T N hN sample rho ω}
    (fun _ => E) _ β hβ
  · rw [Measure.toPMF_toMeasure]
    change training.real
      {ω | ¬ RegisteredCalibrationGood P certified T N hN sample rho ω} ≤ _
    exact hbad
  · intro ω hω
    have hcert : ∀ n, n < T → ∀ x a, certified n x a →
        tvDist ((P n x a).map (q (select ω))).toMeasure
          (Q (select ω) n (q (select ω) x) a).toMeasure ≤ min 1 (rho n + eta ω n) := by
      intro n hn x a hc
      let j : CoverageRegisteredRow certified T := ⟨(⟨n, hn⟩, a, x), hc⟩
      exact empirical_coarse_row_tv (P n x a)
        (empiricalResponsePMF (hN j) (sample j) ω)
        (q (select ω)) (measurable_of_countable _)
        (Q (select ω) n (q (select ω) x) a) (rho n) (eta ω n)
        (hω j) (hfit ω hω n hn x a hc)
    have hrisk := ArbitraryObservationRiskCheck.coverage_arbitrary_observation_microscopic_failure_risk
      (initial (select ω)) (q (select ω)) P (Q (select ω)) (policy (select ω))
      certified (fun n => min 1 (rho n + eta ω n)) T hcert
      E (F (select ω)) (hF ω hω) (henvelope ω hω)
    have hbudget :=
      ObservableActionCoverageContinuationCheck.deployment_coverage_budget_le_of_actual_occupancy_cap
        (initial (select ω)) (q (select ω)) P (policy (select ω)) certified
        (fun n => min 1 (rho n + eta ω n)) (kappa ω) T
        (fun _ _ => min_le_left _ _) (hcap ω hω)
    exact hrisk.trans
      ((min_le_min le_rfl (add_le_add le_rfl hbudget)).trans (hchecked ω hω))

end
end VariableRegisteredJointCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
