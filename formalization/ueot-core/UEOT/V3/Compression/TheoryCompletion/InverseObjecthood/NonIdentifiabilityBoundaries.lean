import UEOT.V3.Compression.TheoryCompletion.OperationalObject
import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.Identifiability
import UEOT.V3.Compression.CrossTrack.InteractionPersistenceSeparations
import UEOT.V3.BinaryTesting
import Mathlib.Tactic

namespace UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

open MeasureTheory
open UEOT.V3
open UEOT.V3.BinaryTesting
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.TheoryCompletion

/-! Concrete finite witnesses use the discrete measurable structures. -/
local instance p46BoolMeasurable : MeasurableSpace Bool := ⊤
local instance p46BoolSingleton : MeasurableSingletonClass Bool := by infer_instance
local instance p46ConstitutiveMeasurable :
    MeasurableSpace (ConstitutiveState Bool Unit) := ⊤
local instance p46ConstitutiveSingleton :
    MeasurableSingletonClass (ConstitutiveState Bool Unit) := by infer_instance

/-- Pairwise interaction-identifiability does not imply even the base P0
constitutive-persistence predicate.  The identifiable Bool response family is
paired with dynamics that immediately leave the proposed domain `{false}`. -/
theorem interactionIdentifiable_but_not_constitutivelyPersistent :
    PairwiseInteractionSeparating identifiableResponseFamily {()} ∧
      ¬ ConstitutivelyPersists
        interactionDoomedDynamics ({false} : Set Bool) := by
  refine ⟨identifiableResponseFamily_separating, ?_⟩
  rintro ⟨K, controller, seed, hKV, hseed, hfix, _hsafe⟩
  have hseedStep : seed ∈ viabilityStep interactionDoomedDynamics K := by
    rw [hfix]
    exact hseed
  rcases hseedStep with ⟨_hseedK, a, hstay⟩
  have htrueSupport : true ∈ (interactionDoomedDynamics seed a).support := by
    simp [interactionDoomedDynamics]
  have htrueK : true ∈ K := hstay htrueSupport
  have htrueFalse : true ∈ ({false} : Set Bool) := hKV htrueK
  simp at htrueFalse

/-- The self-loop witness is genuinely constitutively persistent on the whole
finite state space. -/
theorem selfLoop_constitutivelyPersistent :
    ConstitutivelyPersists interactionSelfLoopDynamics (Set.univ : Set Bool) := by
  let controller : Bool → Unit := fun _ => ()
  refine ⟨Set.univ, controller, false, Set.Subset.rfl, by simp, ?_, ?_⟩
  · exact viable_but_not_interactionIdentifiable.1
  · apply constitutive_all_times_safe_of_preserving
      interactionSelfLoopDynamics controller
    · intro x hx
      simp [StaysIn, interactionSelfLoopDynamics]
    · simp

/-- General validity-aware no-go: if two admitted candidates have identical
declared evidence but are distinct literal targets, the evidence cannot identify
literal candidate identity on that validity class. -/
theorem literalCandidate_not_identified_of_valid_sameEvidence
    {A Evidence : Type*}
    (valid : A → Prop) (evidence : A → Evidence)
    {a b : A}
    (ha : valid a) (hb : valid b)
    (hevidence : evidence a = evidence b)
    (hne : a ≠ b) :
    ¬ ObjectClassIdentifiedByEvidenceAmongValid
      valid evidence (equalitySetoid A) := by
  exact objectClass_not_identified_of_valid_counterexample
    valid evidence (equalitySetoid A) ha hb hevidence hne

/-- **Persistent-but-indistinguishable inverse witness.**

Both Bool candidate labels pass the declared constitutive-persistence validity
gate, while the collapsed interaction family gives them identical evidence.
Hence persistence alone cannot turn a nonseparating probe family into a literal
inverse-object identifier. -/
theorem persistentCandidates_not_identified_by_collapsedInteraction :
    ¬ ObjectClassIdentifiedByEvidenceAmongValid
      (fun _ : Bool =>
        ConstitutivelyPersists interactionSelfLoopDynamics (Set.univ : Set Bool))
      (fun a : Bool => collapsedResponseFamily.response a ())
      (equalitySetoid Bool) := by
  apply literalCandidate_not_identified_of_valid_sameEvidence
    (valid := fun _ : Bool =>
      ConstitutivelyPersists interactionSelfLoopDynamics (Set.univ : Set Bool))
    (evidence := fun a : Bool => collapsedResponseFamily.response a ())
    (a := false) (b := true)
  · exact selfLoop_constitutivelyPersistent
  · exact selfLoop_constitutivelyPersistent
  · rfl
  · simp

/-- **P-INV-01 discrimination boundary for P4.**

If two candidate data laws have total variation strictly below one, every
measurable equal-prior binary discriminator has strictly positive average
error.  No inverse-object selection algorithm can obtain perfect finite-sample
discrimination on that observation space without additional evidence. -/
theorem binaryDiscrimination_error_pos_of_tvDist_lt_one
    {X : Type*} [MeasurableSpace X]
    (P0 P1 : Measure X)
    [IsProbabilityMeasure P0] [IsProbabilityMeasure P1]
    (hTV : UEOT.V3.TotalVariation.tvDist P0 P1 < 1)
    (A : Set X) (hA : MeasurableSet A) :
    0 < binaryRisk P0 P1 A := by
  have hbound := binaryRisk_lower_bound P0 P1 A hA
  have hlower : 0 < (1 / 2 : ℝ) *
      (1 - UEOT.V3.TotalVariation.tvDist P0 P1) := by
    positivity
  exact hlower.trans_le hbound

end UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
