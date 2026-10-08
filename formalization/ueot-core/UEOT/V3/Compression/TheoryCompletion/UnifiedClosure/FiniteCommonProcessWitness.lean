import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeterministicDiracPredictiveBridge
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCKernelLineageExamples
import Mathlib.Tactic

/-!
# UMC-01 finite common-source positive and negative controls

All of the following use one actual Boolean-flip transition mechanism.
The SISC finite Markov kernel is *definitionally matched* to the Dirac
stochastic kernel newly constructed from the deterministic flip process.

Two distinct observation protocols applied to this same process show
exact predictive separation versus a legitimate quotient alias. N3/P8
certificates can be combined for the full-readout toy only under the
separately registered lineage interpretation; N5 proves that physical
Markov semantics alone cannot supply that interpretation.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.Compression.TheoryCompletion

/-- The SINGLE, fixed controlled microscopic transition. -/
def flipStep (x : Bool) (_ : Unit) : Bool := !x

/-- The existing N5 normalized microkernel is EXACTLY the Dirac
stochastic semantics of our controlled deterministic flip, for every
source and target, not just one selected source state. -/
theorem flip_dirac_kernel_eq_n5 (x y : Bool) :
    (diracControlledKernel flipStep).mass x () y =
      n5PhysicalKernel.mass x () y := by
  cases x <;> cases y <;>
    norm_num [diracControlledKernel, flipStep,
      n5PhysicalKernel, flipObservationKernel]

/-- An injective present readout separates all future predictive
signatures of the registered two-state model. -/
theorem flip_future_state_faithful :
    Function.Injective (canonicalFuture flipStep id) := by
  intro x y h
  exact current_response_of_equal_future flipStep id h

/-- The same process automatically yields a unique normalized stochastic
quotient on the exact canonical future-state representation. -/
theorem flip_has_unique_normalized_predictive_quotient :
    letI : Fintype (ReachableState (canonicalFuture flipStep id)) :=
      Fintype.ofFinite _
    ∃! Kbar : FiniteControlledStochasticKernel
      (ReachableState (canonicalFuture flipStep id)) Unit,
      ∀ x a c,
      Kbar.mass (toReachable (canonicalFuture flipStep id) x) a c =
        massIntoClass (diracControlledKernel flipStep)
          (canonicalFuture flipStep id) x a c :=
  existsUnique_canonical_future_stochastic_quotient flipStep id

/-- Negative control: on the SAME flipping process, an uninformative
observation protocol collapses distinct microscopic tokens even when
all allowed future observations are included. -/
theorem flip_constant_readout_aliases_distinct_tokens :
    false ≠ true ∧
    canonicalFuture flipStep (fun _ : Bool => PUnit.unit) false =
    canonicalFuture flipStep (fun _ : Bool => PUnit.unit) true := by
  refine ⟨Bool.false_ne_true, ?_⟩
  apply Subtype.ext
  funext word
  exact Subsingleton.elim _ _

/-- The old N3 result is backed by EXACTLY this newly derived kernel.
It selects the one supported response-compatible micro-successor, but
not an ontic object in the absence of independent P8 semantics. -/
theorem flip_n3_unique_matches_common_process :
    (∀ x y : Bool,
      n5PhysicalKernel.mass x () y =
        (diracControlledKernel flipStep).mass x () y) ∧
    resolveRegisteredCandidates (supportAdmittedProtocol n5ToySearch) =
      .unique true := by
  refine ⟨?_, n5_toy_supported_unique⟩
  intro x y
  exact (flip_dirac_kernel_eq_n5 x y).symm

/-- A nontrivial joint model exists: common process -> exact predictive
quotient -> calibrated positive-mass unique successor. Yet the
genealogical label remains independent, as the N5 fixed-microstate no-go
proves even with perfect full-state readout. -/
theorem flip_common_process_joint_witness_and_genealogy_boundary :
    Function.Injective (canonicalFuture flipStep id) ∧
    (∀ x y : Bool,
      n5PhysicalKernel.mass x () y =
        (diracControlledKernel flipStep).mass x () y) ∧
    resolveRegisteredCandidates (supportAdmittedProtocol n5ToySearch) =
      .unique true ∧
    ¬ ∃ recovered : Bool → Bool → Prop,
      (∀ p c, recovered p c ↔ n5ReproductiveInterpretation.parentOf p c) ∧
      (∀ p c, recovered p c ↔ n5NonreproductiveInterpretation.parentOf p c) := by
  refine ⟨flip_future_state_faithful, ?_, n5_toy_supported_unique,
    fixed_physical_kernel_has_no_semantics_independent_parent_decoder⟩
  intro x y
  exact (flip_dirac_kernel_eq_n5 x y).symm

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
