import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.HighProbabilityDiscovery
import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.ControlClosureBridge

/-!
# P4.8 — terminal finite inverse-Objecthood closure

The terminal statement is deliberately layered.  A P4 discovery contract
recovers the declared scientific object class in marginal probability.  A
control-encoder bridge, a same-parent bridge, and collapse of the target class
to literal candidate equality are independent extra assumptions and therefore
produce independent strengthened conclusions.

This module does not manufacture a common probability space, does not infer a
full Objecthood certificate from interaction evidence, and does not identify
purpose or Pi/Phi.  P4.7 remains the separate deterministic adapter that feeds
a recovered control encoder into P3 value/GOD/policy/GOA closure.
-/

namespace UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

open Filter Topology MeasureTheory

universe uOmega uCandidate uX uS uParent

/-- If the declared object class determines a control encoder, encoder mismatch
is no more probable than object-class failure at every sample size. -/
theorem controlEncoderFailure_le_scheduleFailure
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    {X : Type uX} {S : Type uS}
    (encoder : Candidate → X → S)
    (B : ObjectClassControlEncoderBridge D.objectClass encoder)
    (n : ℕ) :
    (D.mu n).real
        {omega | encoder (D.estimate n omega) ≠ encoder D.truth} ≤
      D.schedule.failure n := by
  have hsubset :
      {omega | encoder (D.estimate n omega) ≠ encoder D.truth} ⊆
        {omega | ¬ D.objectClass.r (D.estimate n omega) D.truth} := by
    intro omega hneq hclass
    exact hneq (B.encoder_eq_of_class _ _ hclass)
  let _ : IsProbabilityMeasure (D.mu n) := D.probability n
  exact (measureReal_mono hsubset).trans (D.classFailure_le n)

/-- Consequently the probability of recovering the wrong control encoder tends
to zero.  This does not itself assert same-parent identity. -/
theorem controlEncoderFailure_tendsto_zero
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    {X : Type uX} {S : Type uS}
    (encoder : Candidate → X → S)
    (B : ObjectClassControlEncoderBridge D.objectClass encoder) :
    Tendsto
      (fun n => (D.mu n).real
        {omega | encoder (D.estimate n omega) ≠ encoder D.truth})
      atTop (𝓝 0) := by
  exact squeeze_zero
    (fun _ => measureReal_nonneg)
    (fun n => controlEncoderFailure_le_scheduleFailure D encoder B n)
    D.schedule.failure_tendsto_zero

/-- A separately declared same-parent bridge gives the analogous finite-sample
failure bound for parent identity. -/
theorem parentIdentityFailure_le_scheduleFailure
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    {Parent : Type uParent}
    (parent : Candidate → Parent)
    (B : ObjectClassParentBridge D.objectClass parent)
    (n : ℕ) :
    (D.mu n).real
        {omega | parent (D.estimate n omega) ≠ parent D.truth} ≤
      D.schedule.failure n := by
  have hsubset :
      {omega | parent (D.estimate n omega) ≠ parent D.truth} ⊆
        {omega | ¬ D.objectClass.r (D.estimate n omega) D.truth} := by
    intro omega hneq hclass
    exact hneq (B.parent_eq_of_class _ _ hclass)
  let _ : IsProbabilityMeasure (D.mu n) := D.probability n
  exact (measureReal_mono hsubset).trans (D.classFailure_le n)

/-- Same-parent error tends to zero only when the explicit parent bridge is
present. -/
theorem parentIdentityFailure_tendsto_zero
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    {Parent : Type uParent}
    (parent : Candidate → Parent)
    (B : ObjectClassParentBridge D.objectClass parent) :
    Tendsto
      (fun n => (D.mu n).real
        {omega | parent (D.estimate n omega) ≠ parent D.truth})
      atTop (𝓝 0) := by
  exact squeeze_zero
    (fun _ => measureReal_nonneg)
    (fun n => parentIdentityFailure_le_scheduleFailure D parent B n)
    D.schedule.failure_tendsto_zero

/-- If every target object class is a singleton on the candidate space, class
recovery upgrades to literal candidate recovery.  Pairwise interaction
separation is one way P4.3 can supply this premise; it is not built into P4. -/
theorem literalCandidateFailure_tendsto_zero_of_class_collapse
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    (hcollapse : ∀ a b, D.objectClass.r a b → a = b) :
    Tendsto
      (fun n => (D.mu n).real {omega | D.estimate n omega ≠ D.truth})
      atTop (𝓝 0) := by
  have hbound : ∀ n,
      (D.mu n).real {omega | D.estimate n omega ≠ D.truth} ≤
        D.schedule.failure n := by
    intro n
    have hsubset :
        {omega | D.estimate n omega ≠ D.truth} ⊆
          {omega | ¬ D.objectClass.r (D.estimate n omega) D.truth} := by
      intro omega hneq hclass
      exact hneq (hcollapse _ _ hclass)
    let _ : IsProbabilityMeasure (D.mu n) := D.probability n
    exact (measureReal_mono hsubset).trans (D.classFailure_le n)
  exact squeeze_zero
    (fun _ => measureReal_nonneg) hbound D.schedule.failure_tendsto_zero

/-- **P4 terminal finite inverse-Objecthood closure.**

With all three optional identifiability bridges supplied, four different error
notions vanish: scientific object-class error, literal candidate error, control-
encoder error, and same-parent error.  Their separation in the conclusion is
intentional; deleting any bridge deletes only the corresponding stronger claim. -/
theorem p4_terminal_finite_inverse_closure
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    {X : Type uX} {S : Type uS}
    (encoder : Candidate → X → S)
    (Bcontrol : ObjectClassControlEncoderBridge D.objectClass encoder)
    {Parent : Type uParent}
    (parent : Candidate → Parent)
    (Bparent : ObjectClassParentBridge D.objectClass parent)
    (hcollapse : ∀ a b, D.objectClass.r a b → a = b) :
    Tendsto
        (fun n => (D.mu n).real
          {omega | ¬ D.objectClass.r (D.estimate n omega) D.truth})
        atTop (𝓝 0) ∧
    Tendsto
        (fun n => (D.mu n).real {omega | D.estimate n omega ≠ D.truth})
        atTop (𝓝 0) ∧
    Tendsto
        (fun n => (D.mu n).real
          {omega | encoder (D.estimate n omega) ≠ encoder D.truth})
        atTop (𝓝 0) ∧
    Tendsto
        (fun n => (D.mu n).real
          {omega | parent (D.estimate n omega) ≠ parent D.truth})
        atTop (𝓝 0) := by
  exact ⟨D.classFailure_tendsto_zero,
    literalCandidateFailure_tendsto_zero_of_class_collapse D hcollapse,
    controlEncoderFailure_tendsto_zero D encoder Bcontrol,
    parentIdentityFailure_tendsto_zero D parent Bparent⟩

end UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
