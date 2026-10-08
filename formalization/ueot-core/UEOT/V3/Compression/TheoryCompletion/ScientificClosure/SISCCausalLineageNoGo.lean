import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCRegisteredCausalCandidates
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCEmissionTiming
import UEOT.V3.Compression.TheoryCompletion.LineageEvolution
import UEOT.V3.Compression.CrossTrack.ParentSemanticNoGo
import Mathlib.Tactic

/-!
# SISC N5 — a full-state process does not determine reproductive lineage

Unlike SI-1's generic collapsed-response ambiguity, this exact countermodel
holds fixed the *same fully known microscopic stochastic kernel* and even an
injective current-state readout. Two independently admissible genealogical
interpretations agree on every law derived from that kernel but assign
opposite parentOf predicates to a positive-mass edge.

This is not a claim that physical parentage is arbitrary in nature.
It proves the logically necessary separation: a descriptive Markov
transition law is not a separately identified reproductive causal relation.
P8's LineageSemantics deliberately carries parentOf as its own field.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion

/-- A fully known, normalized microscopic process, previously proved
row-stochastic in SISCEmissionTiming. -/
def n5PhysicalKernel : FiniteControlledStochasticKernel Bool Unit :=
  flipObservationKernel

/-- Explicitly register all microscopic tokens as directly observed. -/
def n5FullReadout : Bool → Bool := id

theorem n5_full_readout_injective : Function.Injective n5FullReadout := by
  exact fun _ _ h => h

/-- One independently declared genealogical semantics treats a false→true
physical transition as a genuine reproductive parent edge. -/
def n5ReproductiveInterpretation : LineageSemantics Bool Bool where
  identity := id
  parentOf := fun p c => p ≠ c

/-- Another interpretation of the *identical fully observed physical
process* treats its transitions as non-reproductive state changes. -/
def n5NonreproductiveInterpretation : LineageSemantics Bool Bool where
  identity := id
  parentOf := fun _ _ => False

/-- **Causal ancestry no-go at maximum micro-observability.** The
transition probability is 1 on false→true, both models use the identical
microkernel and fully injective readout, yet the same positive transition
is genealogical under one explicit P8 semantics and not under the other.

Thus neither a full microstate readout nor a known Markov kernel can, by
itself, derive the extra P8 parentOf predicate. The distinction requires
external mechanistic and/or intervenable provenance data and a typed bridge.
-/
theorem full_microstate_process_does_not_fix_parent_semantics :
    n5PhysicalKernel.mass false () true = 1 ∧
    Function.Injective n5FullReadout ∧
    n5ReproductiveInterpretation.parentOf false true ∧
    ¬ n5NonreproductiveInterpretation.parentOf false true ∧
    ¬ n5ReproductiveInterpretation.SameObject false true := by
  refine ⟨?_, n5_full_readout_injective, ?_, ?_, ?_⟩
  · norm_num [n5PhysicalKernel, flipObservationKernel]
  · exact Bool.false_ne_true
  · simp [n5NonreproductiveInterpretation]
  · simp [LineageSemantics.SameObject, n5ReproductiveInterpretation]

/-- No single edge predicate can simultaneously recover both genealogical
interpretations of the *same* microscopic transition/readout data. -/
theorem fixed_physical_kernel_has_no_semantics_independent_parent_decoder :
    ¬ ∃ recovered : Bool → Bool → Prop,
       (∀ p c, recovered p c ↔ n5ReproductiveInterpretation.parentOf p c) ∧
       (∀ p c, recovered p c ↔ n5NonreproductiveInterpretation.parentOf p c) := by
  rintro ⟨recovered, hrep, hnonrep⟩
  have hparent : recovered false true :=
    (hrep false true).2 Bool.false_ne_true
  exact ((hnonrep false true).1 hparent)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
