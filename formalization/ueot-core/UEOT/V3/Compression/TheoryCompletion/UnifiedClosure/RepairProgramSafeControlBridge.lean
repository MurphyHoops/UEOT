import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeCausalHistoryTransport
import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.JointRecovery
import Mathlib.Tactic

/-!
# R3/R4 interface: real repaired programs as source-derived safe actions

Existing RLSR already proves triple-redundant repair-program reconstruction,
joint controller/program recovery and physical kernel correspondence.
This file DOES NOT recreate an interpreter, fault model or repair theorem.

It instead reconciles that actual recovered program with the independently
frozen PMF viability and discounted-control interfaces on literally the
same original source M; this supplies a typed bridge to safe Bellman control.
A valid program is viable, NOT necessarily constrained-optimal.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

universe uX uA uP

variable {X : Type uX} {A : Type uA} {Program : Type uP}
variable [Fintype X] [Fintype A] [Nonempty A]
variable [DecidableEq Program]

/-- Every pre-existing behaviorally valid reconstructed program supplies
a concrete member of the exact safety-restricted original-action subtype.
No new synthesis existence or standalone safety axiom is introduced. -/
noncomputable def recoveredProgramSourceSafeAction
    (M : Model X (fun _ => A)) (K : Set X)
    (T : TrustedRepairSubstrate Program X A) (r : Program)
    (hr : RepairProgramValid T (fun x a => M.transitionPMF x a) K r)
    (x : X) : viableSourceAction M K x :=
  ⟨T.execute r x, fun hx => hr x hx⟩

/-- The repaired program really drives exactly the same microscopic source
kernel as R3's safe-control model, not an independently fabricated recovery
dynamics.  The equality uses RLSR6's frozen autonomous joint kernel lemma. -/
theorem reconstructed_program_source_kernel_agrees_with_safe_action
    (M : Model X (fun _ => A)) (K : Set X)
    (T : TrustedRepairSubstrate Program X A) (r : Program)
    (hr : RepairProgramValid T (fun x a => M.transitionPMF x a) K r)
    (x : X) :
    jointRepairKernel T (fun x a => M.transitionPMF x a)
        (restoredJointState T r x) =
      (M.transitionPMF x
        (recoveredProgramSourceSafeAction M K T r hr x).1).map
          (restoredJointState T r) := by
  simpa [recoveredProgramSourceSafeAction] using
    jointRepairKernel_restored T (fun x a => M.transitionPMF x a) r x

/-- Every positive-probability original successor selected by a recovered
program stays within the viability kernel whenever its current source
state is viable. This is a real bridge from the RLSR program-validity
certificate to the SAME source as the R3 Bellman controller. -/
theorem reconstructed_program_preserves_source_viability
    (M : Model X (fun _ => A)) (K : Set X)
    (T : TrustedRepairSubstrate Program X A) (r : Program)
    (hr : RepairProgramValid T (fun x a => M.transitionPMF x a) K r)
    (x y : X) (hx : x ∈ K)
    (hpos : 0 < M.transition x (T.execute r x) y) :
    y ∈ K := by
  exact viable_action_positive_source_successor M K x y
    (recoveredProgramSourceSafeAction M K T r hr x)
    hx hpos

/-- Safety and genuinely autonomous, registered program execution hold
together on a single microkernel. This invokes, rather than reproves, the
RLSR6 closure theorem for the recovered joint target. -/
theorem reconstructed_program_joint_and_source_safety
    (M : Model X (fun _ => A)) (K : Set X)
    (T : TrustedRepairSubstrate Program X A) (r : Program)
    (hr : RepairProgramValid T (fun x a => M.transitionPMF x a) K r)
    (x : X) (hx : x ∈ K) :
    StaysIn (M.transitionPMF x
      (recoveredProgramSourceSafeAction M K T r hr x).1) K ∧
    StaysIn
      (jointRepairKernel T (fun x a => M.transitionPMF x a)
        (restoredJointState T r x))
      (RecoveredJointTarget T K r) := by
  constructor
  · exact (recoveredProgramSourceSafeAction M K T r hr x).property hx
  · exact jointRepairKernel_staysIn_recoveredTarget T
      (fun x a => M.transitionPMF x a) K hr hx

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
