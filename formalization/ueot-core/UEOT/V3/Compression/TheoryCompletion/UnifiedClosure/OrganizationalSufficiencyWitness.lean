import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.UnifiedCoreClosureCertificate
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViabilityNonvacuityWitness
import Mathlib.Tactic

/-!
# Same physical kernel: nontrivial organizational compression and refusal

The four-state physically stochastic witness uses the EXISTING survivalMicroKernel.
If the registered task only protects the visible/safety bit, the frozen
P-ALG algorithm reduces four microstates to two classes. If the hidden
program-state attribute is protected, the two hidden states cannot merge.
A state-label is NOT a proof of physical program synthesis or provenance.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteStablePartition

noncomputable def registeredSurvivalModel :
    UEOT.V3.FiniteStablePartition.Model (Bool × Bool) Bool ℝ
      (Bool × Bool × Unit × Unit × Bool) :=
  modelWithRegisteredOrganization survivalMicroKernel
    (fun x => x.1) (fun x => x.1)
    (fun _ => ()) (fun _ => ()) (fun x => x.1) (fun _ _ => 0)

/-- This same four-state transition row depends on the action but not on
the source state. Its initial registered partition is already stable. -/
theorem registered_survival_initial_stable :
    Stable registeredSurvivalModel (initialSetoid registeredSurvivalModel) := by
  intro x y h a z
  rfl

theorem registered_survival_terminal_eq_initial :
    terminalSetoid registeredSurvivalModel =
      initialSetoid registeredSurvivalModel :=
  stabilize_eq_self_of_stable registeredSurvivalModel
    (initialSetoid registeredSurvivalModel)
    registered_survival_initial_stable

/-- Nontrivial four-to-two controlled compression: a physically random
hidden bit can be forgotten when no protected current label depends on it. -/
theorem registered_survival_two_hidden_states_merge :
    (terminalSetoid registeredSurvivalModel).r
      (true, false) (true, true) := by
  rw [registered_survival_terminal_eq_initial]
  exact ⟨rfl, fun _ => rfl⟩

/-- Distinct visible/safe microstates are not spuriously merged. -/
theorem registered_survival_visible_states_remain_distinct :
    ¬ (terminalSetoid registeredSurvivalModel).r
      (true, false) (false, false) := by
  intro h
  have hh := (organizational_terminal_preserves_registered_interfaces
    registeredSurvivalModel h).1
  simp [registeredSurvivalModel, modelWithRegisteredOrganization] at hh

/-- SAME source kernel, but the registered organizational contract
explicitly protects the hidden current program-state bit. -/
noncomputable def hiddenProgramProtectedModel :
    UEOT.V3.FiniteStablePartition.Model (Bool × Bool) Bool ℝ
      (Bool × Bool × Bool × Unit × Bool) :=
  modelWithRegisteredOrganization survivalMicroKernel
    (fun x => x.1) (fun x => x.1)
    (fun x => x.2) (fun _ => ()) (fun x => x.1) (fun _ _ => 0)

/-- Protected hidden program-state cannot be discarded by any valid stable
refinement, despite its irrelevance for the visible stochastic response. -/
theorem protected_hidden_program_prevents_merge :
    ¬ (terminalSetoid hiddenProgramProtectedModel).r
      (true, false) (true, true) := by
  intro h
  have hh := registered_organizational_attributes_preserved
    survivalMicroKernel
    (fun x : Bool × Bool => x.1)
    (fun x : Bool × Bool => x.1)
    (fun x : Bool × Bool => x.2)
    (fun _ : Bool × Bool => ())
    (fun x : Bool × Bool => x.1)
    (fun _ _ => (0 : ℝ)) h
  exact Bool.false_ne_true hh.2.2.1

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
