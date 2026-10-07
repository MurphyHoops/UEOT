import UEOT.V3.Compression.TheoryCompletion.Purpose
import UEOT.V3.Compression.TheoryCompletion.TeleologicalGauge

/-!
# Scientific Closure C6 — mechanism-to-purpose bridge

Purpose is not inferred from object existence or from a raw mechanism signal.
The bridge from independently calibrated mechanism evidence to teleological
semantics is explicit and may fail.  Bellman/control faithfulness and viability
remain later, independent gates already formalized by P2.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

open UEOT.V3.Compression.TheoryCompletion

universe uM uO uP

/-- A mechanism observation can be teleologically faithful without being
injective at the raw mechanism level: observationally indistinguishable
mechanisms must at least induce the same policy ordering. -/
def MechanismTeleologicalFaithfulness
    {Mechanism : Type uM} {Observation : Type uO} {P : Type uP}
    (observe : Mechanism → Observation)
    (objective : Mechanism → NumericalObjective P) : Prop :=
  ∀ m n, observe m = observe n →
    PolicyOrderingEquivalent (objective m) (objective n)

/-- Under the explicit mechanism/teleology faithfulness condition, identification
at the registered mechanism-observation level transfers to the teleological
objective class. -/
theorem mechanismObservation_identifies_teleologicalClass
    {Mechanism : Type uM} {Observation : Type uO} {P : Type uP}
    (observe : Mechanism → Observation)
    (objective : Mechanism → NumericalObjective P)
    (hfaith : MechanismTeleologicalFaithfulness observe objective)
    {m n : Mechanism} (hobs : observe m = observe n) :
    TeleologicalObjectiveClass (objective m) =
      TeleologicalObjectiveClass (objective n) := by
  exact teleologicalObjectiveClass_eq_of_equivalent (hfaith m n hobs)

/-- **C6 no-go.**  Equal observable mechanism evidence does not identify purpose
without a mechanism→teleology faithfulness bridge.  The explicit Bool example
uses one constant observation channel and two objectives with opposite order. -/
theorem equalMechanismObservation_does_not_determine_purpose :
    ∃ (observe : Bool → Unit)
      (objective : Bool → NumericalObjective Bool)
      (m n : Bool),
      observe m = observe n ∧
      ¬ PolicyOrderingEquivalent (objective m) (objective n) := by
  let observe : Bool → Unit := fun _ => ()
  let J : NumericalObjective Bool := fun b => if b then 1 else 0
  let K : NumericalObjective Bool := fun b => if b then 0 else 1
  let objective : Bool → NumericalObjective Bool := fun b => if b then K else J
  refine ⟨observe, objective, false, true, rfl, ?_⟩
  intro h
  have hcomp := h false true
  simp [objective, J, K, InducedPreference] at hcomp
  norm_num at hcomp

/-- Consequently, an arbitrary observation/objective pair need not satisfy the
required bridge. -/
theorem mechanismTeleologicalFaithfulness_not_automatic :
    ∃ (observe : Bool → Unit)
      (objective : Bool → NumericalObjective Bool),
      ¬ MechanismTeleologicalFaithfulness observe objective := by
  rcases equalMechanismObservation_does_not_determine_purpose with
    ⟨observe, objective, m, n, hobs, hneq⟩
  refine ⟨observe, objective, ?_⟩
  intro hfaith
  exact hneq (hfaith m n hobs)

/-- Even after mechanism-level teleological identification, numerical
representatives need not be pointwise equal; the invariant output is the
teleological objective class. -/
theorem mechanism_bridge_targets_class_not_numerical_identity
    {Mechanism : Type uM} {Observation : Type uO} {P : Type uP}
    (observe : Mechanism → Observation)
    (objective : Mechanism → NumericalObjective P)
    (hfaith : MechanismTeleologicalFaithfulness observe objective)
    {m n : Mechanism} (hobs : observe m = observe n) :
    PolicyOrderingEquivalent (objective m) (objective n) :=
  hfaith m n hobs

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
