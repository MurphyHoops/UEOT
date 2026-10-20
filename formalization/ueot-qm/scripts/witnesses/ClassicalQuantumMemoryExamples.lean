import UEOTQM.ClassicalQuantumMemory

/-!
# Legal controls for retained records and quantum memory

The two instruments have the same identity memory channel at every density
input, but different certain labels. A complete two-step feedback protocol uses
that retained label to choose a later operation, so its later event probabilities
also differ. All instruments are complete actual Kraus families.
-/

namespace UEOTQM.ClassicalQuantumMemoryExamples

open Matrix ClassicalQuantumMemory
open scoped BigOperators ComplexOrder

noncomputable section

abbrev Qubit := Fin 2
abbrev Label := Fin 2

/-- The identity operation with a fixed, certain classical record. -/
def certain (tag : Label) : Instrument Qubit Label Unit where
  kraus o _ := if o = tag then 1 else 0
  complete := by
    fin_cases tag <;> simp [Fin.sum_univ_two]

theorem certain_branch (tag o : Label) (X : Operator Qubit) :
    (certain tag).branch o X = if o = tag then X else 0 := by
  by_cases h : o = tag <;>
    simp [Instrument.branch, krausMap, certain, h]

theorem certain_channel (tag : Label) (X : Operator Qubit) :
    (certain tag).channel X = X := by
  simp [Instrument.channel, certain_branch]

theorem certain_channelState (tag : Label) (ρ : Density Qubit) :
    (certain tag).channelState ρ = ρ := by
  apply Density.ext
  exact certain_channel tag ρ.matrix

theorem certain_probability (tag o : Label) (ρ : Density Qubit) :
    (certain tag).probability ρ o = if o = tag then 1 else 0 := by
  by_cases h : o = tag <;>
    simp [Instrument.probability, certain_branch, h, mass, ρ.trace_one]

/-- A concrete normalized input witnesses the actual worst-case supremum. -/
def rhoZero : Density Qubit where
  matrix := Matrix.diagonal (fun i => if i = 0 then (1 : ℂ) else 0)
  positive := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> norm_num
  trace_one := by simp [Matrix.trace, Fin.sum_univ_two]

/-- The old unlabelled defect is exactly zero on all input densities. -/
theorem deleted_record_channelDefect_zero :
    channelDefect (certain 0).channelState (certain 1).channelState = 0 := by
  have h0 : (certain 0).channelState = fun ρ => ρ := funext (certain_channelState 0)
  have h1 : (certain 1).channelState = fun ρ => ρ := funext (certain_channelState 1)
  rw [h0, h1, channelDefect_self]

theorem retained_record_tv_one (ρ σ : Density Qubit) :
    Mixture.tv (weights (certain 0) ρ) (weights (certain 1) σ) = 1 := by
  norm_num [Mixture.tv, weights_weight, certain_probability, Fin.sum_univ_two]

theorem retained_joint_distance_one (ρ σ : Density Qubit) :
    effectDistance (state (certain 0) ρ) (state (certain 1) σ) = 1 := by
  apply le_antisymm (effectDistance_le_one _ _)
  have h := record_tv_le_joint_distance (certain 0) (certain 1) ρ σ
  simpa only [retained_record_tv_one] using h

/-- An actual input gives the lower bound; the universal effect bound gives 1. -/
theorem retained_record_defect_one : defect (certain 0) (certain 1) = 1 := by
  change (channel (certain 0)).defect (channel (certain 1)) = 1
  apply le_antisymm ((channel (certain 0)).defect_le_one (channel (certain 1)))
  calc
    (1 : ℝ) = effectDistance ((channel (certain 0)).state rhoZero)
        ((channel (certain 1)).state rhoZero) :=
      (retained_joint_distance_one rhoZero rhoZero).symm
    _ ≤ _ := (channel (certain 0)).state_distance_le_defect (channel (certain 1)) rhoZero

/-- Deleting the record makes this stability target false by the full unit gap. -/
theorem deleted_record_is_not_a_record_bound :
    ¬ Mixture.tv (weights (certain 0) rhoZero) (weights (certain 1) rhoZero) ≤
      channelDefect (certain 0).channelState (certain 1).channelState := by
  rw [retained_record_tv_one, deleted_record_channelDefect_zero]
  norm_num

/-- `none` is the first operation; `some o` is a later operation selected from
its observed label. Both models use exactly the same later operations. -/
def feedbackFamily (first : Label) : Option Label → Instrument Qubit Label Unit
  | none => certain first
  | some o => certain o

/-- A complete causal two-step controller retains and uses the first label. -/
def feedbackProtocol : Adaptive.Protocol (Option Label) Label :=
  .node none (fun o => .node (some o) (fun _ => .stop))

attribute [local instance] Classical.propDecidable

/-- The event refers only to the second, later outcome. -/
def feedbackLaterZero : Finset (ProtocolMemory.Leaf feedbackProtocol) :=
  {⟨0, ⟨0, PUnit.unit⟩⟩, ⟨1, ⟨0, PUnit.unit⟩⟩}

theorem feedbackLaterZero_iff (l : ProtocolMemory.Leaf feedbackProtocol) :
    l ∈ feedbackLaterZero ↔ l.2.1 = 0 := by
  unfold feedbackLaterZero
  erw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl) <;> rfl
  · intro hp
    rcases l with ⟨o, p, u⟩
    change p = 0 at hp
    subst p
    cases u
    fin_cases o
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem feedback_later_zero_probability_zero_model (ρ : Density Qubit) :
    RecordProbability.eventProbability
      (ProtocolMemory.weights (feedbackFamily 0) feedbackProtocol ρ) feedbackLaterZero = 1 := by
  have hne : (⟨0, ⟨0, PUnit.unit⟩⟩ : ProtocolMemory.Leaf feedbackProtocol) ≠
      ⟨1, ⟨0, PUnit.unit⟩⟩ := by
    intro h
    have hfirst := congrArg (fun l : ProtocolMemory.Leaf feedbackProtocol => l.1) h
    norm_num at hfirst
  unfold RecordProbability.eventProbability feedbackLaterZero
  refine (Finset.sum_pair (f :=
    (ProtocolMemory.weights (feedbackFamily 0) feedbackProtocol ρ).weight) hne).trans ?_
  simp [ProtocolMemory.weights, Adaptive.leafProbability, Adaptive.leafWeight,
    Adaptive.Protocol.word, feedbackProtocol, recordOperator,
    feedbackFamily, certain_branch, mass, ρ.trace_one]

theorem feedback_later_zero_probability_one_model (ρ : Density Qubit) :
    RecordProbability.eventProbability
      (ProtocolMemory.weights (feedbackFamily 1) feedbackProtocol ρ) feedbackLaterZero = 0 := by
  have hne : (⟨0, ⟨0, PUnit.unit⟩⟩ : ProtocolMemory.Leaf feedbackProtocol) ≠
      ⟨1, ⟨0, PUnit.unit⟩⟩ := by
    intro h
    have hfirst := congrArg (fun l : ProtocolMemory.Leaf feedbackProtocol => l.1) h
    norm_num at hfirst
  unfold RecordProbability.eventProbability feedbackLaterZero
  refine (Finset.sum_pair (f :=
    (ProtocolMemory.weights (feedbackFamily 1) feedbackProtocol ρ).weight) hne).trans ?_
  simp [ProtocolMemory.weights, Adaptive.leafProbability, Adaptive.leafWeight,
    Adaptive.Protocol.word, feedbackProtocol, recordOperator,
    feedbackFamily, certain_branch, mass, ρ.trace_one]

/-- This distinguishes a genuine later adaptive outcome despite identical
unconditional first memory channels. -/
theorem adaptive_later_event_gap_one (ρ σ : Density Qubit) :
    |RecordProbability.eventProbability
        (ProtocolMemory.weights (feedbackFamily 0) feedbackProtocol ρ) feedbackLaterZero -
      RecordProbability.eventProbability
        (ProtocolMemory.weights (feedbackFamily 1) feedbackProtocol σ) feedbackLaterZero| = 1 := by
  rw [feedback_later_zero_probability_zero_model,
    feedback_later_zero_probability_one_model]
  norm_num

theorem adaptive_later_effect_gap_one (ρ σ : Density Qubit) :
    |(eventEffect Qubit feedbackLaterZero).probability
        (ProtocolMemory.state (feedbackFamily 0) feedbackProtocol ρ) -
      (eventEffect Qubit feedbackLaterZero).probability
        (ProtocolMemory.state (feedbackFamily 1) feedbackProtocol σ)| = 1 := by
  rw [ProtocolMemory.event_probability, ProtocolMemory.event_probability]
  exact adaptive_later_event_gap_one ρ σ

/-- The complete leaf law is separated by the same later-event witness. -/
theorem adaptive_record_tv_one (ρ σ : Density Qubit) :
    Mixture.tv (ProtocolMemory.weights (feedbackFamily 0) feedbackProtocol ρ)
      (ProtocolMemory.weights (feedbackFamily 1) feedbackProtocol σ) = 1 := by
  apply le_antisymm (Mixture.tv_le_one _ _)
  have h := RecordProbability.eventProbability_abs_sub_le_tv
    (ProtocolMemory.weights (feedbackFamily 0) feedbackProtocol ρ)
    (ProtocolMemory.weights (feedbackFamily 1) feedbackProtocol σ) feedbackLaterZero
  simpa only [adaptive_later_event_gap_one] using h

end

end UEOTQM.ClassicalQuantumMemoryExamples

/-! Explicit witness declaration audit. -/
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.Qubit
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.Label
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.certain
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.certain_branch
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.certain_channel
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.certain_channelState
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.certain_probability
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.rhoZero
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.deleted_record_channelDefect_zero
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.retained_record_tv_one
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.retained_joint_distance_one
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.retained_record_defect_one
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.deleted_record_is_not_a_record_bound
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.feedbackFamily
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.feedbackProtocol
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.feedbackLaterZero
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.feedbackLaterZero_iff
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.feedback_later_zero_probability_zero_model
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.feedback_later_zero_probability_one_model
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.adaptive_later_event_gap_one
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.adaptive_later_effect_gap_one
#print axioms UEOTQM.ClassicalQuantumMemoryExamples.adaptive_record_tv_one
