import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJoint
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableRegisteredJoint

/-!
# Support viability in the unequal-allocation training/deployment experiment

The deployed policy is the existing `viableFamilyPolicy`. Initial support
viability on the same registered calibration event proves that policy's own
zero actual uncertified occupancy. Thus the joint risk endpoint needs no
external occupancy cap. Fixed per-row sample allocations and a Good-only
measurable failure envelope are handled by the same source experiment and Good
event. The observation alphabet may be infinite.

Certification concerns transition rows, not physical survival. The reference
event risk and empirical fit remain explicit. A complete fallback policy is
an input, and no infinite-horizon survival conclusion is asserted.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace ViableVariableRegisteredJointCheck

open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open SupportViabilityClosure ViableRegisteredJointCheck VariableRegisteredJointCheck
open scoped BigOperators Classical

noncomputable section

universe uΩ uC u

/-- One actual registered experiment with fixed unequal row sample counts,
same-Good initial support viability, empirical fit, event envelope and risk
check bounds the actual selected training/deployment failure probability.

The policy in the conclusion is exactly the policy whose zero uncertified
occupancy is proved internally. Candidate selection may depend on all training
data. No independent calibration bound, alternate-policy cap or global
candidate envelope is required.
-/
theorem viable_registered_selected_joint_failure_on_good
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
    (fallback : C → ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (eta : Ω → ℕ → ℝ)
    (hinit : ∀ ω, RegisteredCalibrationGood P certified T N hN sample rho ω →
      ∀ y : Y, (initialSupport (initial (select ω)) (q (select ω)) y).Nonempty →
        Viable (q (select ω)) P certified 0 T
          (initialSupport (initial (select ω)) (q (select ω)) y))
    (hfit : ∀ ω, RegisteredCalibrationGood P certified T N hN sample rho ω →
      ∀ n (hn : n < T) x a (hc : certified n x a),
      tvDist ((empiricalResponsePMF
        (hN ⟨(⟨n, hn⟩, a, x), hc⟩)
        (sample ⟨(⟨n, hn⟩, a, x), hc⟩) ω).map
          (q (select ω))).toMeasure
        (Q (select ω) n (q (select ω) x) a).toMeasure ≤ eta ω n)
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
  refine VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good
    training P certified T N hN sample rho hmeas hindep hlaw hrho
    select q initial Q (viableFamilyPolicy initial q P certified T fallback)
    eta (fun _ _ => 0) hfit ?_ E F hF henvelope β hβ ?_
  · intro ω hg n hn
    exact le_of_eq (viablePolicy_zero_uncovered
      (initial (select ω)) (q (select ω)) P certified T (fallback (select ω))
      (hinit ω hg) n hn)
  · intro ω hg
    simpa only [mul_zero, add_zero] using hchecked ω hg

end
end ViableVariableRegisteredJointCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
