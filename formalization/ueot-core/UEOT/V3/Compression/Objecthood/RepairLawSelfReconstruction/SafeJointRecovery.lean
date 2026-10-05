import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.JointRecovery

/-!
# RLSR-T2 — mode-free safe joint recovery

This module removes the mutable scheduler bit from the strengthened RLSR path.
Every physical step first canonicalizes the mutable repair-program representation,
rebinds the ordinary controller to the decoded internal program, and only then
uses that controller to choose the physical action.

Thus the causal order is literal in one kernel:

`repair program -> controller -> physical transition`.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood

universe uX uA uP uR

noncomputable section

variable {X : Type uX} {A : Type uA}
variable {Program : Type uP} {Representation : Type uR}

/-- RLSR1 state specialized to an executable controller. -/
abbrev RepairOrganizationState
    (X : Type uX) (A : Type uA) (Representation : Type uR) :=
  SelfReconstructingState X (X → A) Representation

/-- Canonical recovered organization around one decoded program. -/
def canonicalRepairOrganizationState
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) (x : X) :
    RepairOrganizationState X A Representation :=
  { physical := x
    controller := T.execute r
    repairProgram := codec.encode r }

/-- Repair organization before *every* physical move.  This has no mutable mode
or scheduler state. -/
def canonicalizeRepairOrganization
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (s : RepairOrganizationState X A Representation) :
    RepairOrganizationState X A Representation :=
  canonicalRepairOrganizationState T codec
    (codec.decode s.repairProgram) s.physical

@[simp] theorem canonicalizeRepairOrganization_physical
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (s : RepairOrganizationState X A Representation) :
    (canonicalizeRepairOrganization T codec s).physical = s.physical := rfl

@[simp] theorem canonicalizeRepairOrganization_controller
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (s : RepairOrganizationState X A Representation) :
    (canonicalizeRepairOrganization T codec s).controller =
      T.execute (codec.decode s.repairProgram) := rfl

@[simp] theorem canonicalizeRepairOrganization_program
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (s : RepairOrganizationState X A Representation) :
    (canonicalizeRepairOrganization T codec s).repairProgram =
      codec.encode (codec.decode s.repairProgram) := rfl

/-- **Mode-free safe repair kernel.**  Program reconstruction and controller
rebinding happen before the physical action is selected.  The actual action is
read from the rebuilt controller field, not bypassed through a parallel call. -/
noncomputable def safeRepairKernel
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X)
    (s : RepairOrganizationState X A Representation) :
    PMF (RepairOrganizationState X A Representation) :=
  let s' := canonicalizeRepairOrganization T codec s
  (P s'.physical (s'.controller s'.physical)).map fun y =>
    { s' with physical := y }

/-- On a canonical program representation, one safe step is exactly the physical
kernel selected by that program, lifted back to canonical organizational state. -/
theorem safeRepairKernel_canonical
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program) (x : X) :
    safeRepairKernel T codec P (canonicalRepairOrganizationState T codec r x) =
      (P x (T.execute r x)).map
        (canonicalRepairOrganizationState T codec r) := by
  simp only [safeRepairKernel, canonicalizeRepairOrganization,
    canonicalRepairOrganizationState, codec.decode_encode]
  apply congrArg (fun f : X → RepairOrganizationState X A Representation =>
    PMF.map f (P x (T.execute r x)))
  funext y
  rfl

/-- Generic recovered joint target for one internal program. -/
def SafeRecoveredTarget
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (K : Set X) (r : Program) :
    Set (RepairOrganizationState X A Representation) :=
  {s | ∃ x ∈ K, s = canonicalRepairOrganizationState T codec r x}

/-- Carrier validity closes the recovered target under the mode-free kernel. -/
theorem safeRepairKernel_staysIn_recoveredTarget
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X)
    {r : Program} (hr : RepairProgramValid T P K r)
    {x : X} (hx : x ∈ K) :
    StaysIn
      (safeRepairKernel T codec P
        (canonicalRepairOrganizationState T codec r x))
      (SafeRecoveredTarget T codec K r) := by
  rw [safeRepairKernel_canonical]
  intro s hs
  rw [PMF.mem_support_map_iff] at hs
  rcases hs with ⟨y, hy, rfl⟩
  exact ⟨y, hr x hx hy, rfl⟩

section Triple

variable [DecidableEq Program]

abbrev TripleRepairOrganizationState :=
  RepairOrganizationState X A (TripleProgramRepresentation Program)

/-- Arbitrary ordinary-controller corruption plus one arbitrary replica
replacement.  There is deliberately no scheduler/mode coordinate to corrupt. -/
def safeSingleReplicaDamagedState
    (x : X) (controller : X → A)
    (r bad : Program) (i : Fin 3) :
    TripleRepairOrganizationState (X := X) (A := A) (Program := Program) :=
  { physical := x
    controller := controller
    repairProgram := replaceProgramReplica i bad (tripleProgramEncode r) }

/-- The strengthened runtime masks one arbitrary replica fault *before* selecting
its physical action and ignores any corrupted stored controller by rebuilding it
from the decoded program. -/
theorem safeRepairKernel_singleReplica_exact
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X)
    (x : X) (controller : X → A)
    (r bad : Program) (i : Fin 3) :
    safeRepairKernel T tripleRepairCodec P
      (safeSingleReplicaDamagedState x controller r bad i) =
      (P x (T.execute r x)).map
        (canonicalRepairOrganizationState T tripleRepairCodec r) := by
  simp only [safeRepairKernel, canonicalizeRepairOrganization,
    safeSingleReplicaDamagedState, canonicalRepairOrganizationState,
    tripleRepairCodec, tripleProgramDecode_replace_encode]
  apply congrArg (fun f : X → TripleRepairOrganizationState
      (X := X) (A := A) (Program := Program) =>
    PMF.map f (P x (T.execute r x)))
  funext y
  rfl

/-- The same theorem also formalizes one-step masking of a fresh single-replica
fault during execution: every safe step re-decodes and re-canonicalizes before
using the controller. -/
theorem safeRepairKernel_recurrent_singleReplica_fault_masked
    (T : TrustedRepairSubstrate Program X A)
    (P : X → A → PMF X)
    (x : X) (controller : X → A)
    (r bad : Program) (i : Fin 3) :
    safeRepairKernel T tripleRepairCodec P
      { physical := x
        controller := controller
        repairProgram := replaceProgramReplica i bad (tripleProgramEncode r) } =
      (P x (T.execute r x)).map
        (canonicalRepairOrganizationState T tripleRepairCodec r) :=
  safeRepairKernel_singleReplica_exact T P x controller r bad i

end Triple

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
