import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentJoint
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness

/-!
# Calibrated selection and actual joint deployment risk

The registered source experiment supplies a common good training event.
Its selected conditional deployment laws retain the actual coverage penalty,
and the constructed training/deployment joint integrates their risk.

The existing fixed-policy statistical experiment separately instantiates
this joint law with risk at most 143/256. Its nonempty calibration event
bounds one fixed deployment law, so that instance needs no additional
training-failure charge.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe uΩ uC u

/-- A registered source experiment, a data-selected controlled deployment,
and a checked bound on its actual coverage budget yield a genuine
unconditional failure bound for one common microscopic event.

Only registered rows have samples. The confidence event comes from those
samples, while uncovered-row mass is evaluated under the actual selected
causal deployment law. The `hchecked` premise retains that coverage term;
restricted training observations alone do not establish it. -/
theorem coverage_statistical_selected_joint_failure_risk
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
    (eta : Ω → ℕ → ℝ)
    (hfit : ∀ ω n (hn : n < T) x a (hc : certified n x a),
      tvDist ((empiricalResponsePMF hN (sample ⟨(⟨n, hn⟩, a, x), hc⟩) ω).map
        (q (select ω))).toMeasure (Q (select ω) n (q (select ω) x) a).toMeasure ≤ eta ω n)
    (E : Set (CausalHistory X (A × X) T))
    (F : C → Set (CausalHistory Y (A × Y) T))
    (henvelope : ∀ c, E ⊆
      (riskHistoryMap (q c) (fun ax : A × X => (ax.1, q c ax.2)) T) ⁻¹' F c)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hchecked : ∀ ω,
      min 1 ((causalLaw ((initial (select ω)).map (q (select ω)))
        (riskMacroControlKernel (Q (select ω)) (policy (select ω))) T).toMeasure.real
          (F (select ω)) +
        ∑ n ∈ Finset.range T, (min 1 (rho n + eta ω n) +
          (1 - min 1 (rho n + eta ω n)) *
            (coverageDeploymentRowLaw (initial (select ω)) (q (select ω)) P
              (policy (select ω)) n).toMeasure.real
                {xa | ¬ certified n xa.1 xa.2})) ≤ β) :
    Measurable select ∧
      (selectedTrainingDeployment training.toPMF select
        (fun c => causalLaw (initial c) (riskMicroControlKernel (q c) P (policy c)) T)).toMeasure.real
          {z | z.2 ∈ E} ≤
        min 1 ((∑ j : CoverageRegisteredRow certified T,
          (Fintype.card (Finset X) : ℝ) *
            (2 * Real.exp (-2 * (N : ℝ) * (rho j.1.1) ^ 2))) +
          (1 - ∑ j : CoverageRegisteredRow certified T,
            (Fintype.card (Finset X) : ℝ) *
              (2 * Real.exp (-2 * (N : ℝ) * (rho j.1.1) ^ 2))) * β) := by
  refine ⟨measurable_of_finite _, ?_⟩
  obtain ⟨good, _hgood, hbad, hcal⟩ :=
    coverage_registered_source_calibration hN training P certified T sample rho
      hmeas hindep hlaw hrho
  apply selectedTrainingDeployment_failure_le training.toPMF select
    (fun c => causalLaw (initial c) (riskMicroControlKernel (q c) P (policy c)) T)
    good (fun _ => E) _ β hβ
  · simpa only [Measure.toPMF_toMeasure] using hbad
  · intro ω hω
    exact (coverage_empirical_registered_microscopic_failure_risk hN
      (initial (select ω)) (q (select ω)) P (Q (select ω)) (policy (select ω))
      certified T sample rho (eta ω) ω (hcal ω hω) (hfit ω)
      E (F (select ω)) (henvelope (select ω))).trans (hchecked ω)

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory UEOT.V3.PathError
open scoped BigOperators Classical

noncomputable section

open StatisticalRiskWitness

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSpace State := ⊤

/-- The existing positive-probability calibration event is nonempty. Since
this concrete deployment policy is fixed, one good record bounds the same
law for every record. Its genuine training/deployment joint therefore keeps
the sharper `143/256` bound without spending a training-failure penalty. -/
theorem statistical_fixed_policy_training_deployment_witness :
    (selectedTrainingDeployment trainingLaw.toPMF (fun _ : SampleSpace => ())
      (fun _ : Unit => actualMicroLaw 2)).toMeasure.real
        {z | riskEverFailure (fun x : State => coarse x = true) 2 z.2} ≤ 143 / 256 ∧
      (143 / 256 : ℝ) < 1 := by
  obtain ⟨ω, hω⟩ := good_sample_exists
  have hrisk := microscopic_two_step_risk_on_good ω hω
  have h := selectedTrainingDeployment_failure_le trainingLaw.toPMF
    (fun _ : SampleSpace => ()) (fun _ : Unit => actualMicroLaw 2) Set.univ
    (fun _ => {h | riskEverFailure (fun x : State => coarse x = true) 2 h})
    0 (143 / 256) (by norm_num) (by simp) (fun _ _ => hrisk)
  norm_num at h
  exact ⟨h, by norm_num⟩

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
