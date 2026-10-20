import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableRegisteredJoint

/-!
# Good-selected failure envelopes by completion outside Good selections

Research module, 2026-10-20, outside the production import graph.
Actual validation status is recorded separately in the accompanying build receipt.

The existing registered joint endpoint assumes an envelope for every
candidate, although its reference event is only checked for selections on
one common Good event. Complete the unused candidate envelopes by `univ`.
The completed event agrees with the original on every Good selection, so
the existing proved risk and viability endpoints apply without changing
the experiment, selected policy, calibration event or numerical budget.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace GoodSelectedEnvelopeCheck

open MeasureTheory ProbabilityTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open RegisteredGoodJointCheck ViableRegisteredJointCheck SupportViabilityClosure
open scoped BigOperators Classical

noncomputable section

universe uΩ uC u

/-- Complete reference events for candidates never selected by a Good record.
This auxiliary completion does not alter the actual deployment family. -/
def completeSelectedEnvelope
    {Ω : Type*} {C : Type*} {H : Type*} (Good : Ω → Prop) (select : Ω → C)
    (F : C → Set H) (c : C) : Set H :=
  if ∃ ω, Good ω ∧ select ω = c then F c else Set.univ

/-- The completion leaves the checked reference event unchanged on Good. -/
theorem completeSelectedEnvelope_on_good
    {Ω : Type*} {C : Type*} {H : Type*} (Good : Ω → Prop) (select : Ω → C)
    (F : C → Set H) (ω : Ω) (hgood : Good ω) :
    completeSelectedEnvelope Good select F (select ω) = F (select ω) := by
  unfold completeSelectedEnvelope
  exact if_pos ⟨ω, hgood, rfl⟩

/-- A selected envelope on Good gives a total candidate envelope after
completion. This is set theory; it assumes no probabilistic conclusion. -/
theorem completeSelectedEnvelope_covers
    {Ω : Type*} {C : Type*} {H : Type*} {K : Type*} (Good : Ω → Prop) (select : Ω → C)
    (map : C → H → K) (E : Set H) (F : C → Set K)
    (henvelope : ∀ ω, Good ω → E ⊆ (map (select ω)) ⁻¹' F (select ω)) :
    ∀ c, E ⊆ (map c) ⁻¹' completeSelectedEnvelope Good select F c := by
  intro c
  by_cases hc : ∃ ω, Good ω ∧ select ω = c
  · obtain ⟨ω, hg, hc⟩ := hc
    subst c
    simpa only [completeSelectedEnvelope_on_good Good select F ω hg] using
      henvelope ω hg
  · simpa only [completeSelectedEnvelope, if_neg hc, Set.preimage_univ] using
      (Set.subset_univ E)

/-- Calibration, empirical fit, actual occupancy cap, selected envelope and
reference budget all concern the same Good record. Only reference sets of
candidates never selected on Good are completed; the existing joint-risk
proof supplies the entire probabilistic conclusion. -/
theorem registered_selected_joint_failure_of_cap_and_envelope_on_good
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
    (henvelope : ∀ ω, RegisteredCalibrationGood hN P certified T sample rho ω →
      E ⊆
        (riskHistoryMap (q (select ω))
          (fun ax : A × X => (ax.1, q (select ω) ax.2)) T) ⁻¹'
          F (select ω))
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
  let G : Ω → Prop := RegisteredCalibrationGood hN P certified T sample rho
  refine registered_selected_joint_failure_of_cap_on_good hN training P certified T sample rho
    hmeas hindep hlaw hrho select q initial Q policy eta kappa hfit hcap E
    (completeSelectedEnvelope G select F)
    (completeSelectedEnvelope_covers G select
      (fun c => riskHistoryMap (q c) (fun ax : A × X => (ax.1, q c ax.2)) T)
      E F henvelope) β hβ ?_
  intro ω hω
  simpa only [completeSelectedEnvelope_on_good G select F ω hω] using
    hchecked ω hω

/-- The same viability family used by the actual joint derives its own zero
uncertified occupancy internally through the published viable endpoint.
Only the selected failure envelope is weakened to the common Good event. -/
theorem viable_registered_selected_joint_failure_with_envelope_on_good
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
    (henvelope : ∀ ω, RegisteredCalibrationGood hN P certified T sample rho ω →
      E ⊆
        (riskHistoryMap (q (select ω))
          (fun ax : A × X => (ax.1, q (select ω) ax.2)) T) ⁻¹'
          F (select ω))
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
  let G : Ω → Prop := RegisteredCalibrationGood hN P certified T sample rho
  refine viable_registered_selected_joint_failure_on_good hN training P certified T sample rho
    hmeas hindep hlaw hrho select q initial Q fallback eta hinit hfit E
    (completeSelectedEnvelope G select F)
    (completeSelectedEnvelope_covers G select
      (fun c => riskHistoryMap (q c) (fun ax : A × X => (ax.1, q c ax.2)) T)
      E F henvelope) β hβ ?_
  intro ω hω
  simpa only [completeSelectedEnvelope_on_good G select F ω hω] using
    hchecked ω hω

end
end GoodSelectedEnvelopeCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

-- Kernel axiom closure of the two selected-envelope terminals.
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.GoodSelectedEnvelopeCheck.registered_selected_joint_failure_of_cap_and_envelope_on_good
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.GoodSelectedEnvelopeCheck.viable_registered_selected_joint_failure_with_envelope_on_good
