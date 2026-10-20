import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViability
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisteredDeploymentRisk

/-!
# Finite support viability closes coverage in registered joint risk

The selected candidate uses the already proved viability policy. Initial
viability on the same calibration event derives zero actual uncertified
occupancy for that exact policy, eliminating the cap premise at the joint
endpoint. Empirical reference fit, the failure envelope and the reference
risk check remain explicit; no extra calibration budget is introduced.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace ViableRegisteredJointCheck

open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open RegisteredGoodJointCheck SupportViabilityClosure
open scoped BigOperators Classical

noncomputable section

universe uΩ uC u

/-- Candidate policies are the already proved support-viability construction,
retaining each candidate's full fallback as an explicit input. -/
abbrev viableFamilyPolicy
    {C : Type uC} {X Y A : Type u}
    (initial : C → PMF X) (q : C → X → Y)
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop) (T : ℕ)
    (fallback : C → ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    C → ∀ n, CausalHistory Y (A × Y) n → PMF A :=
  fun c => viablePolicy (initial c) (q c) P certified T (fallback c)

/-- A single registered training experiment, initial support viability and
a Good-only empirical reference check imply a bound on the same selected
actual training/deployment experiment. Actual zero uncertified occupancy
is derived for the very policy used in the joint; it is not an input.

Viability certifies transition rows, not physical survival. The common
microscopic failure event is controlled through its explicit reference
envelope and reference error budget. -/
theorem viable_registered_selected_joint_failure_on_good
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
    (fallback : C → ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (eta : Ω → ℕ → ℝ)
    (hinit : ∀ ω, RegisteredCalibrationGood hN P certified T sample rho ω →
      ∀ y : Y, (initialSupport (initial (select ω)) (q (select ω)) y).Nonempty →
        Viable (q (select ω)) P certified 0 T
          (initialSupport (initial (select ω)) (q (select ω)) y))
    (hfit : ∀ ω, RegisteredCalibrationGood hN P certified T sample rho ω →
      ∀ n (hn : n < T) x a (hc : certified n x a),
      tvDist ((empiricalResponsePMF hN (sample ⟨(⟨n, hn⟩, a, x), hc⟩) ω).map
        (q (select ω))).toMeasure (Q (select ω) n (q (select ω) x) a).toMeasure ≤ eta ω n)
    (E : Set (CausalHistory X (A × X) T))
    (F : C → Set (CausalHistory Y (A × Y) T))
    (henvelope : ∀ c, E ⊆
      (riskHistoryMap (q c) (fun ax : A × X => (ax.1, q c ax.2)) T) ⁻¹' F c)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hchecked : ∀ ω, RegisteredCalibrationGood hN P certified T sample rho ω →
      min 1 ((causalLaw ((initial (select ω)).map (q (select ω)))
        (riskMacroControlKernel (Q (select ω))
          (viableFamilyPolicy initial q P certified T fallback (select ω))) T).toMeasure.real
            (F (select ω)) +
        ∑ n ∈ Finset.range T, min 1 (rho n + eta ω n)) ≤ β) :
    Measurable select ∧
      (selectedTrainingDeployment training.toPMF select
        (fun c => causalLaw (initial c)
          (riskMicroControlKernel (q c) P
            (viableFamilyPolicy initial q P certified T fallback c)) T)).toMeasure.real
          {z | z.2 ∈ E} ≤
        min 1 (registeredConfidenceBudget certified T N rho +
          (1 - registeredConfidenceBudget certified T N rho) * β) := by
  refine registered_selected_joint_failure_of_cap_on_good hN training P certified T sample rho
    hmeas hindep hlaw hrho select q initial Q
    (viableFamilyPolicy initial q P certified T fallback) eta (fun _ _ => 0) hfit
    ?_ E F henvelope β hβ ?_
  · intro ω hg n hn
    exact le_of_eq (viablePolicy_zero_uncovered
      (initial (select ω)) (q (select ω)) P certified T (fallback (select ω))
      (hinit ω hg) n hn)
  · intro ω hg
    simpa only [mul_zero, add_zero] using hchecked ω hg


end
end ViableRegisteredJointCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
