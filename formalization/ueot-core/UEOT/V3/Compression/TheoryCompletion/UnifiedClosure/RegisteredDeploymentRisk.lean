import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentJoint
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableActionCoverage

/-!
# Registered calibration and selected deployment risk on a common good event

The same fixed registered-row calibration event controls the selected
actual training/deployment joint. Empirical fit and the numerical reference
budget are checked on that event, and a proved cap on the same selected
policy occupancy enters the budget. The calibration failure charge is paid
once. No witness-only sampling module is required by this generic result.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace RegisteredGoodJointCheck

open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe uΩ uC u

/-- One fixed registered-row calibration event, before any candidate is selected. -/
def RegisteredCalibrationGood
    {Ω : Type uΩ} {X A : Type u} [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N)
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop) (T : ℕ)
    (sample : CoverageRegisteredRow certified T → Fin N → Ω → X)
    (rho : ℕ → ℝ) (ω : Ω) : Prop :=
  ∀ j : CoverageRegisteredRow certified T,
    tvDist (P j.1.1 j.1.2.2 j.1.2.1).toMeasure
      (empiricalResponsePMF hN (sample j) ω).toMeasure ≤ rho j.1.1

/-- The same finite-row concentration budget as the published terminal. -/
def registeredConfidenceBudget
    {X A : Type u} [Fintype X] [Fintype A]
    (certified : ℕ → X → A → Prop) (T N : ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ j : CoverageRegisteredRow certified T,
    (Fintype.card (Finset X) : ℝ) *
      (2 * Real.exp (-2 * (N : ℝ) * (rho j.1.1) ^ 2))

/-- The old simultaneous calibration event is contained in the canonical
TV good event. Enlarging that event spends no additional failure budget. -/
theorem registered_calibration_good_bad_le
    {Ω : Type uΩ} {X A : Type u}
    [Fintype Ω] [Fintype X] [Fintype A]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {N : ℕ} (hN : 0 < N) (training : Measure Ω) [IsProbabilityMeasure training]
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop) (T : ℕ)
    (sample : CoverageRegisteredRow certified T → Fin N → Ω → X) (rho : ℕ → ℝ)
    (hmeas : ∀ j k, Measurable (sample j k))
    (hindep : ∀ j, iIndepFun (sample j) training)
    (hlaw : ∀ j k, training.map (sample j k) =
      (P j.1.1 j.1.2.2 j.1.2.1).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n) :
    MeasurableSet {ω | RegisteredCalibrationGood hN P certified T sample rho ω} ∧
      training.real {ω | ¬ RegisteredCalibrationGood hN P certified T sample rho ω} ≤
        registeredConfidenceBudget certified T N rho := by
  obtain ⟨good, _hgood, hbad, hcal⟩ :=
    coverage_registered_source_calibration hN training P certified T sample rho
      hmeas hindep hlaw hrho
  refine ⟨Set.to_countable _ |>.measurableSet, ?_⟩
  have hsub : {ω | ¬ RegisteredCalibrationGood hN P certified T sample rho ω} ⊆
      goodᶜ := by
    intro ω hω hg
    exact hω (hcal ω hg)
  exact (measureReal_mono hsub).trans hbad

/-- Checks on the common calibration event suffice. A proof about the
selected policy's actual occupancy replaces that quantity in the numerical
budget. No check is imposed on bad training records; their actual joint
contribution is bounded by their probability, exactly once.

This uses the same source, common microscopic event and constructed
training/deployment joint as `coverage_statistical_selected_joint_failure_risk`.
Its existing all-outcome premises cannot directly yield this weaker contract;
the existing calibration, conditional-risk and joint lemmas are reused. -/
theorem registered_selected_joint_failure_of_cap_on_good
    {Ω : Type uΩ} {C : Type uC} {X Y A : Type u}
    [Fintype Ω] [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [MeasurableSpace C]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    {N : ℕ} (hN : 0 < N) (training : Measure Ω) [IsProbabilityMeasure training]
    (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (sample : CoverageRegisteredRow certified T → Fin N → Ω → X) (rho : ℕ → ℝ)
    (hmeas : ∀ j k, Measurable (sample j k))
    (hindep : ∀ j, iIndepFun (sample j) training)
    (hlaw : ∀ j k, training.map (sample j k) =
      (P j.1.1 j.1.2.2 j.1.2.1).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n)
    (select : Ω → C) (q : C → X → Y) (initial : C → PMF X)
    (Q : C → ℕ → Y → A → PMF Y)
    (policy : C → ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (eta kappa : Ω → ℕ → ℝ)
    (hfit : ∀ ω, RegisteredCalibrationGood hN P certified T sample rho ω →
      ∀ n (hn : n < T) x a (hc : certified n x a),
      tvDist ((empiricalResponsePMF hN (sample ⟨(⟨n, hn⟩, a, x), hc⟩) ω).map
        (q (select ω))).toMeasure (Q (select ω) n (q (select ω) x) a).toMeasure ≤ eta ω n)
    (hcap : ∀ ω, RegisteredCalibrationGood hN P certified T sample rho ω →
      ∀ n, n < T →
      (coverageDeploymentRowLaw (initial (select ω)) (q (select ω)) P
        (policy (select ω)) n).toMeasure.real {xa | ¬ certified n xa.1 xa.2} ≤ kappa ω n)
    (E : Set (CausalHistory X (A × X) T))
    (F : C → Set (CausalHistory Y (A × Y) T))
    (henvelope : ∀ c, E ⊆
      (riskHistoryMap (q c) (fun ax : A × X => (ax.1, q c ax.2)) T) ⁻¹' F c)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hchecked : ∀ ω, RegisteredCalibrationGood hN P certified T sample rho ω →
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
  obtain ⟨_hgood, hbad⟩ := registered_calibration_good_bad_le hN training
    P certified T sample rho hmeas hindep hlaw hrho
  refine ⟨measurable_of_finite _, ?_⟩
  apply selectedTrainingDeployment_failure_le training.toPMF select
    (fun c => causalLaw (initial c) (riskMicroControlKernel (q c) P (policy c)) T)
    {ω | RegisteredCalibrationGood hN P certified T sample rho ω}
    (fun _ => E) _ β hβ
  · rw [Measure.toPMF_toMeasure]
    change training.real {ω | ¬ RegisteredCalibrationGood hN P certified T sample rho ω} ≤ _
    exact hbad
  · intro ω hω
    refine (coverage_empirical_registered_microscopic_failure_risk hN
      (initial (select ω)) (q (select ω)) P (Q (select ω)) (policy (select ω))
      certified T sample rho (eta ω) ω hω (hfit ω hω)
      E (F (select ω)) (henvelope (select ω))).trans ?_
    have hbudget :=
      ObservableActionCoverageContinuationCheck.deployment_coverage_budget_le_of_actual_occupancy_cap
        (initial (select ω)) (q (select ω)) P (policy (select ω)) certified
        (fun n => min 1 (rho n + eta ω n)) (kappa ω) T
        (fun _ _ => min_le_left _ _) (hcap ω hω)
    exact (min_le_min le_rfl (add_le_add le_rfl hbudget)).trans (hchecked ω hω)


end
end RegisteredGoodJointCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
