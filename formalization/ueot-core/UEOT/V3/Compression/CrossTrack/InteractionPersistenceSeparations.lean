import UEOT.V3.Compression.CrossTrack.InteractionBindingIsolation
import UEOT.V3.ViabilityKernel

/-!
# Interaction identifiability versus persistence — separations

Interaction identifiability and persistence are distinct obligations.  These
finite witnesses prevent a later Objecthood synthesis from silently replacing
one by the other.
-/

namespace UEOT.V3.Compression.CrossTrack

open MeasureTheory
open Set
open UEOT.V3
open UEOT.V3.ViabilityKernel

noncomputable section

/-! ## Identifiable but not viable -/

local instance interactionPersistenceBoolMeasurable : MeasurableSpace Bool := ⊤

/-- One probe whose response law is the assembly-labelled point mass. -/
noncomputable def identifiableResponseFamily :
    InteractionResponseFamily Bool Unit Bool where
  response := fun a _ => (PMF.pure a).toMeasure
  probability := by
    intro a i
    infer_instance

theorem identifiableResponseFamily_separating :
    PairwiseInteractionSeparating identifiableResponseFamily {()} := by
  intro a b hab
  refine ⟨(), by simp, ?_⟩
  intro hmeasure
  have hpoint := congrArg (fun μ : Measure Bool => μ {a}) hmeasure
  simp [identifiableResponseFamily, hab] at hpoint

/-- Dynamics that immediately leaves the proposed persistence domain
`{false}`, regardless of action. -/
noncomputable def interactionDoomedDynamics : Bool → Unit → PMF Bool :=
  fun _ _ => PMF.pure true

theorem identifiable_but_not_oneStepViable :
    PairwiseInteractionSeparating identifiableResponseFamily {()} ∧
      viabilityStep interactionDoomedDynamics ({false} : Set Bool) = ∅ := by
  refine ⟨identifiableResponseFamily_separating, ?_⟩
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxV, a, hstay⟩
    have hxFalse : x = false := by simpa using hxV
    subst x
    have htrue : true ∈ (PMF.pure true).support := by simp
    have : true ∈ ({false} : Set Bool) := hstay htrue
    simp at this
  · simp

/-! ## Viable but not identifiable -/

/-- Completely collapsed interaction readout: both assemblies produce the
same response law under the only probe. -/
noncomputable def collapsedResponseFamily :
    InteractionResponseFamily Bool Unit Bool where
  response := fun _ _ => (PMF.pure false).toMeasure
  probability := by
    intro a i
    infer_instance

theorem collapsedResponseFamily_not_separating :
    ¬ PairwiseInteractionSeparating collapsedResponseFamily {()} := by
  intro hsep
  rcases hsep (show (false : Bool) ≠ true by simp) with ⟨i, hi, hne⟩
  simp [collapsedResponseFamily] at hne

/-- Self-loop dynamics that preserves every state forever at the one-step
viability level. -/
noncomputable def interactionSelfLoopDynamics : Bool → Unit → PMF Bool :=
  fun x _ => PMF.pure x

theorem viable_but_not_interactionIdentifiable :
    viabilityStep interactionSelfLoopDynamics (Set.univ : Set Bool) = Set.univ ∧
      ¬ PairwiseInteractionSeparating collapsedResponseFamily {()} := by
  constructor
  · ext x
    simp [viabilityStep, StaysIn, interactionSelfLoopDynamics]
  · exact collapsedResponseFamily_not_separating

end

end UEOT.V3.Compression.CrossTrack
