import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.TrustedSubstrate

/-!
# RLSR1 — mutable internal repair-program state

The mutable object state stores a physical coordinate, an ordinary controller,
and a repair-program *representation*.  The representation type is deliberately
separate from the executable `Program` type: later stages may use a redundant
encoding such as three replicas and reconstruct an executable program through a
trusted decoder.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

universe uX uC uR uP uA

/-- Object-level state whose repair organization can itself be corrupted.
`Representation` is mutable; no trusted substrate or correct policy is stored in
this state. -/
structure SelfReconstructingState
    (X : Type uX) (Controller : Type uC) (Representation : Type uR) where
  physical : X
  controller : Controller
  repairProgram : Representation

/-- Execution semantics for an already decoded internal program.  This is only
a view through the trusted interpreter; it does not select a correct program. -/
def executedRepairController
    {Program : Type uP} {X : Type uX} {A : Type uA}
    (T : TrustedRepairSubstrate Program X A) (r : Program) : X → A :=
  T.execute r

/-- Behavioral binding between mutable controller state and an internally
executed program. -/
def ControllerImplementsProgram
    {Program : Type uP} {X : Type uX} {A : Type uA}
    (T : TrustedRepairSubstrate Program X A)
    (controller : X → A) (r : Program) : Prop :=
  controller = executedRepairController T r

@[simp] theorem controllerImplementsProgram_refl
    {Program : Type uP} {X : Type uX} {A : Type uA}
    (T : TrustedRepairSubstrate Program X A) (r : Program) :
    ControllerImplementsProgram T (executedRepairController T r) r := by
  rfl

/-- Replacing the program representation changes only mutable object state and
leaves the physical/controller coordinates intact. -/
def SelfReconstructingState.withRepairProgram
    {X : Type uX} {Controller : Type uC} {Representation : Type uR}
    (s : SelfReconstructingState X Controller Representation)
    (r : Representation) : SelfReconstructingState X Controller Representation :=
  { physical := s.physical
    controller := s.controller
    repairProgram := r }

@[simp] theorem SelfReconstructingState.withRepairProgram_physical
    {X : Type uX} {Controller : Type uC} {Representation : Type uR}
    (s : SelfReconstructingState X Controller Representation)
    (r : Representation) :
    (s.withRepairProgram r).physical = s.physical := rfl

@[simp] theorem SelfReconstructingState.withRepairProgram_controller
    {X : Type uX} {Controller : Type uC} {Representation : Type uR}
    (s : SelfReconstructingState X Controller Representation)
    (r : Representation) :
    (s.withRepairProgram r).controller = s.controller := rfl

end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
