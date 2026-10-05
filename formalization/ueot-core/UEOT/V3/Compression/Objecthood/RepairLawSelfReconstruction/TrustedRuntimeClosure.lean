import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.SafeJointRecovery

/-!
# RLSR-T10 — explicit trusted-context closure

The original RLSR7 compressed the trusted boundary to one abstract node.  After
T1 the actual assumptions are more explicit: execution semantics, codec
semantics, ambient physical dynamics, and the object/target specification.
This module records that trust budget directly and proves the mutable repair
organization still has a finite, well-founded dependency architecture.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set

universe uX uA uP uR

variable {X : Type uX} {A : Type uA}
variable {Program : Type uP} {Representation : Type uR}

/-- Exact external context relative to which RLSR is proved.  It deliberately
contains no distinguished correct `Program` value. -/
structure TrustedRepairContext where
  execution : TrustedRepairSubstrate Program X A
  codec : TrustedRepairCodec Program Representation
  dynamics : X → A → PMF X
  target : Set X

/-- Preferred mode-free safe runtime derived from the declared trusted context. -/
noncomputable def TrustedRepairContext.safeKernel
    (C : TrustedRepairContext (X := X) (A := A)
      (Program := Program) (Representation := Representation))
    (s : RepairOrganizationState X A Representation) :
    PMF (RepairOrganizationState X A Representation) :=
  safeRepairKernel C.execution C.codec C.dynamics s

/-- Refined dependency nodes: four trusted inputs followed by mutable object
organization. -/
inductive TrustedRuntimeDependencyNode
  | executionSemantics
  | codecSemantics
  | ambientDynamics
  | objectSpecification
  | repairProgram
  | controller
  | physicalOrganization
  deriving DecidableEq, Repr

/-- Trusted inputs are rank zero; reconstructed program organization is rank
one; controller/physical organization are rank two. -/
def trustedRuntimeDependencyRank : TrustedRuntimeDependencyNode → Nat
  | .executionSemantics => 0
  | .codecSemantics => 0
  | .ambientDynamics => 0
  | .objectSpecification => 0
  | .repairProgram => 1
  | .controller => 2
  | .physicalOrganization => 2

/-- Actual semantic dependency edges of the strengthened RLSR architecture. -/
inductive TrustedRuntimeDependencyStep :
    TrustedRuntimeDependencyNode → TrustedRuntimeDependencyNode → Prop
  | execution_program :
      TrustedRuntimeDependencyStep .executionSemantics .repairProgram
  | codec_program :
      TrustedRuntimeDependencyStep .codecSemantics .repairProgram
  | dynamics_program :
      TrustedRuntimeDependencyStep .ambientDynamics .repairProgram
  | specification_program :
      TrustedRuntimeDependencyStep .objectSpecification .repairProgram
  | program_controller :
      TrustedRuntimeDependencyStep .repairProgram .controller
  | program_physical :
      TrustedRuntimeDependencyStep .repairProgram .physicalOrganization
  | dynamics_physical :
      TrustedRuntimeDependencyStep .ambientDynamics .physicalOrganization
  | specification_physical :
      TrustedRuntimeDependencyStep .objectSpecification .physicalOrganization

/-- Predicate identifying the declared external/trusted boundary. -/
def IsTrustedRuntimeBoundary : TrustedRuntimeDependencyNode → Prop
  | .executionSemantics => True
  | .codecSemantics => True
  | .ambientDynamics => True
  | .objectSpecification => True
  | _ => False

/-- Every declared dependency edge points strictly outward from the trusted
boundary / repair source hierarchy. -/
theorem trustedRuntimeDependencyRank_lt_of_step
    {a b : TrustedRuntimeDependencyNode}
    (h : TrustedRuntimeDependencyStep a b) :
    trustedRuntimeDependencyRank a < trustedRuntimeDependencyRank b := by
  cases h <;> decide

/-- The refined dependency relation is well founded. -/
theorem trustedRuntimeDependencyStep_wellFounded :
    WellFounded TrustedRuntimeDependencyStep := by
  apply (measure trustedRuntimeDependencyRank).wf.mono
  intro a b h
  exact trustedRuntimeDependencyRank_lt_of_step h

/-- No RLSR reconstruction dependency points into one of the declared trusted
inputs.  Those inputs are assumptions of the theorem, not mutable objects that
the theorem claims to reconstruct. -/
theorem trustedRuntimeBoundary_has_no_internal_predecessor
    {b : TrustedRuntimeDependencyNode}
    (hb : IsTrustedRuntimeBoundary b) :
    ¬ ∃ a, TrustedRuntimeDependencyStep a b := by
  intro h
  rcases h with ⟨a, hab⟩
  cases b <;> simp [IsTrustedRuntimeBoundary] at hb
  all_goals cases hab

/-- There is still a genuine repair-of-repair chain from trusted semantics to
mutable repair program and then to controller/physical organization. -/
theorem refinedTrustBudget_has_two_step_repair_chain :
    (TrustedRuntimeDependencyStep .executionSemantics .repairProgram ∧
      TrustedRuntimeDependencyStep .repairProgram .controller) ∧
    (TrustedRuntimeDependencyStep .codecSemantics .repairProgram ∧
      TrustedRuntimeDependencyStep .repairProgram .physicalOrganization) := by
  exact ⟨⟨.execution_program, .program_controller⟩,
    ⟨.codec_program, .program_physical⟩⟩

/-- No infinite repairer-of-repairer regress can occur inside the declared
strengthened RLSR dependency architecture. -/
theorem no_infinite_refined_runtime_repair_regress :
    ¬ ∃ f : Nat → TrustedRuntimeDependencyNode,
      ∀ n, TrustedRuntimeDependencyStep (f (n + 1)) (f n) := by
  intro h
  rcases h with ⟨f, hf⟩
  have h0 : trustedRuntimeDependencyRank (f 1) <
      trustedRuntimeDependencyRank (f 0) := by
    simpa using trustedRuntimeDependencyRank_lt_of_step (hf 0)
  have h1 : trustedRuntimeDependencyRank (f 2) <
      trustedRuntimeDependencyRank (f 1) := by
    simpa using trustedRuntimeDependencyRank_lt_of_step (hf 1)
  have h2 : trustedRuntimeDependencyRank (f 3) <
      trustedRuntimeDependencyRank (f 2) := by
    simpa using trustedRuntimeDependencyRank_lt_of_step (hf 2)
  have hbound : trustedRuntimeDependencyRank (f 0) ≤ 2 := by
    cases hnode : f 0 <;> simp [trustedRuntimeDependencyRank]
  omega

end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
