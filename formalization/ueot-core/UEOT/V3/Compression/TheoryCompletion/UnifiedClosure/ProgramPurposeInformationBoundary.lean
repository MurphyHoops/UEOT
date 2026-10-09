import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveGaugeCompleteness
import UEOT.V3.Compression.TheoryCompletion.AutopoiesisClosure
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCResourcePurpose
import Mathlib.Tactic

/-!
# UMC-05 — exactly which information can recover a repair program / goal

The existing P12 impossibility theorem proves that the *same physical seed*
cannot uniquely reveal two distinct repair programs. We strengthen the
comparison with a constructive sufficient information condition: an
INJECTIVELY encoded program can be exactly reconstructed through invFun.
This is a finite/abstract information-theoretic conditional recovery result,
not spontaneous autopoiesis, interpreter synthesis or repair operation.

The same controlled action dynamics can carry incompatible teleological
price conventions. Thus purpose provenance is separate from process data.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uProgram uPhysical

/-- Independently registered injective program information suffices for
a left-inverse decoder. This discharges the *decoder existence* premise,
not the independent encoder's physical existence or correctness. -/
theorem injective_program_information_has_decoder
    {Program : Type uProgram} {Physical : Type uPhysical}
    [Inhabited Program]
    (encode : Program → Physical)
    (hencode : Function.Injective encode) :
    ∃ recover : Physical → Program,
      ∀ program, recover (encode program) = program := by
  classical
  exact ⟨Function.invFun encode, fun program =>
    Function.leftInverse_invFun hencode program⟩

/-- Exact necessary AND sufficient condition for lossless program recovery
from a physical encoding, under a known encoder and inhabited program type.
This characterizes the missing information premise instead of just postulating
a decoder. It does not construct the encoder from physical-only dynamics. -/
theorem perfect_program_decoder_iff_injective_information
    {Program : Type uProgram} {Physical : Type uPhysical}
    [Inhabited Program] (encode : Program → Physical) :
    (∃ recover : Physical → Program,
      ∀ program, recover (encode program) = program) ↔
    Function.Injective encode := by
  constructor
  · rintro ⟨recover, hrecover⟩ p q hpq
    calc
      p = recover (encode p) := (hrecover p).symm
      _ = recover (encode q) := congrArg recover hpq
      _ = q := hrecover q
  · exact injective_program_information_has_decoder encode

/-- If the physical record carries no program distinguishing information,
the required injective encoding is impossible. This is not one faulty
decoder: no proposed encoder into a singleton physical record can work. -/
theorem singleton_physical_record_cannot_encode_two_programs :
    ¬ ∃ encode : Bool → PUnit, Function.Injective encode := by
  rintro ⟨encode, h⟩
  exact Bool.false_ne_true (h (Subsingleton.elim _ _))

/-- Both sides of the information boundary, explicitly using the
pre-existing P12 theorem as the necessity/no-go half. -/
theorem same_physical_seed_program_reconstruction_no_go :
    ¬ ∃ recover : Bool → Bool,
      recover false = false ∧ recover false = true :=
  no_physicalOnly_synthesizer_for_distinct_sources
    (X := Bool) (Program := Bool) false Bool.false_ne_true

/-- One registered process with two distinct control actions; objectives
are evaluated on precisely the same process. -/
def goalControlledStep (state action : Bool) : Bool :=
  xor state action

def measuredGoalMechanism : ResourceSignal Bool where
  performance := fun action => if goalControlledStep false action then 1 else 0
  expenditure := fun action => if action then 1 else 0
  budget := 1

/-- At price zero the expensive better-performance action is preferred;
with price two the same measured mechanism favors the cheaper action.
A scalar goal is NOT identified by the action transition or accounting. -/
theorem same_process_opposite_goals :
    ¬ PolicyOrderingEquivalent
      (measuredGoalMechanism.objective 0)
      (measuredGoalMechanism.objective 2) := by
  intro h
  have hbad := h false true
  simp [measuredGoalMechanism, ResourceSignal.objective,
    InducedPreference, goalControlledStep] at hbad

/-- A combined internal no-go: exactly one controlled mechanism has
opposite acceptable preferences under two independent evaluator prices,
while a physical-only program decoder is impossible for aliased sources.
Neither impossibility depends on empirical unknowns. -/
theorem independent_program_and_goal_source_obstructions :
    (¬ PolicyOrderingEquivalent
      (measuredGoalMechanism.objective 0)
      (measuredGoalMechanism.objective 2)) ∧
    (¬ ∃ recover : Bool → Bool,
      recover false = false ∧ recover false = true) :=
  ⟨same_process_opposite_goals,
   same_physical_seed_program_reconstruction_no_go⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
