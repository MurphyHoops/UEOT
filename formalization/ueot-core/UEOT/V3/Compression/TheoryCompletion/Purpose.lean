import UEOT.V3.Compression.Hierarchy.Separations
import UEOT.V3.Compression.TeleologicalEquivalence

/-!
# P0.2 scratch — Purpose constitution

This layer separates a numerical objective from the ordering and choice behavior
it represents.  It deliberately does not define the P1 TeleologicalContract or
claim a unique reward representation.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set
open UEOT.Reward
open UEOT.V3.Compression.TeleologicalEquivalence
open UEOT.V3.Compression.Hierarchy

universe uP

/-- One numerical representation of purpose on a declared alternative/policy
space.  The representation itself is not the semantic invariant. -/
abbrev NumericalObjective (P : Type uP) := P → ℝ

/-- Weak preference induced by one numerical objective. -/
def InducedPreference {P : Type uP}
    (J : NumericalObjective P) (p q : P) : Prop :=
  J p ≤ J q

/-- Equality of the weak preference ordering induced by two numerical
representations. -/
def PolicyOrderingEquivalent {P : Type uP}
    (J K : NumericalObjective P) : Prop :=
  ∀ p q, InducedPreference J p q ↔ InducedPreference K p q

/-- The maximizer set is the choice-level semantic projection of one numerical
objective. -/
def MaximizerSet {P : Type uP} (J : NumericalObjective P) : Set P :=
  {p | IsMaximizer J p}

/-- The canonical order-equivalence relation is exactly equality of induced
weak preference comparisons, up to its historical argument orientation. -/
theorem policyOrderingEquivalent_iff_orderEquivalent
    {P : Type uP} (J K : NumericalObjective P) :
    PolicyOrderingEquivalent J K ↔ OrderEquivalent J K := by
  constructor
  · intro h p q
    exact (h p q).symm
  · intro h p q
    exact (h p q).symm

/-- Canonical maximizer equivalence is literally equality of maximizer sets. -/
theorem maximizerEquivalent_iff_maximizerSet_eq
    {P : Type uP} (J K : NumericalObjective P) :
    MaximizerEquivalent J K ↔ MaximizerSet J = MaximizerSet K := by
  constructor
  · intro h
    ext p
    exact (h p).symm
  · intro h p
    have hp := Set.ext_iff.mp h p
    exact hp.symm

/-- Choice-level representation class of a numerical objective.  This is an
ordinary set of representations with the same maximizers; it is deliberately
not the stronger P1 teleological-contract quotient. -/
def ChoiceRepresentationClass {P : Type uP}
    (J : NumericalObjective P) : Set (NumericalObjective P) :=
  {K | MaximizerEquivalent J K}

@[simp] theorem mem_choiceRepresentationClass
    {P : Type uP} (J K : NumericalObjective P) :
    K ∈ ChoiceRepresentationClass J ↔ MaximizerEquivalent J K := by
  rfl

/-- Equal weak preference order implies equal choice behavior. -/
theorem policyOrderingEquivalent_to_maximizerEquivalent
    {P : Type uP} {J K : NumericalObjective P}
    (h : PolicyOrderingEquivalent J K) :
    MaximizerEquivalent J K := by
  exact orderEquivalent_to_maximizerEquivalent
    ((policyOrderingEquivalent_iff_orderEquivalent J K).mp h)

/-- Positive-affine changes preserve the induced policy ordering. -/
theorem positiveAffineEquivalent_to_policyOrderingEquivalent
    {P : Type uP} {J K : NumericalObjective P}
    (h : PositiveAffineEquivalent J K) :
    PolicyOrderingEquivalent J K := by
  exact (policyOrderingEquivalent_iff_orderEquivalent J K).mpr
    (positiveAffineEquivalent_to_orderEquivalent h)

/-- DDH gauge transformations stay inside one choice-representation class. -/
theorem dualDriveGauge_mem_choiceRepresentationClass
    {P : Type uP}
    (piVal phiVal chiVal : P → ℝ) (lambdaVal : ℝ) :
    (fun p =>
      (piVal p + lambdaVal * chiVal p) -
        lambdaVal * (phiVal p + chiVal p)) ∈
      ChoiceRepresentationClass
        (fun p => piVal p - lambdaVal * phiVal p) := by
  exact dualDriveGauge_maximizerEquivalent
    piVal phiVal chiVal lambdaVal

/-- **Purpose no-go.**  A carrier/state type alone does not choose one
choice-representation class: the same finite carrier admits objectives with
different maximizers. -/
theorem carrier_does_not_determine_choiceRepresentationClass :
    ∃ J K : NumericalObjective Bool,
      K ∉ ChoiceRepresentationClass J := by
  simpa [ChoiceRepresentationClass] using
    carrier_does_not_determine_maximizers

end UEOT.V3.Compression.TheoryCompletion
