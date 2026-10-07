import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.SafeJointRecovery

/-!
# Theory Completion P5 / Track O — finite joint organization state

P5 extends recurrent homeostasis from physical/controller state to the mutable
RLSR organization state carrying physical state, stored controller and repair-
program representation.

The completed RLSR structure intentionally did not carry a global `Fintype`
instance.  P5 does not reopen that source file.  Instead this module exposes an
explicit product equivalence and a local/noncomputable `Fintype` constructor for
finite-domain homeostasis arguments.
-/

namespace UEOT.V3.Compression.Objecthood.JointHomeostasis

open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

universe uX uA uR

noncomputable section

/-- The RLSR organization state is exactly a three-coordinate product.  Keeping
this as an explicit equivalence avoids adding a new global instance to the
already completed RLSR API. -/
def repairOrganizationStateEquiv
    {X : Type uX} {A : Type uA} {Representation : Type uR} :
    RepairOrganizationState X A Representation ≃
      X × (X → A) × Representation where
  toFun s := (s.physical, s.controller, s.repairProgram)
  invFun p :=
    { physical := p.1
      controller := p.2.1
      repairProgram := p.2.2 }
  left_inv s := by
    cases s
    rfl
  right_inv p := by
    rcases p with ⟨x, controller, representation⟩
    rfl

/-- Finite-domain P5 may instantiate the full mutable organization state as a
finite carrier without modifying RLSR.  Function-space finiteness is supplied
classically from finite `X` and `A`; no decidable-equality assumption becomes a
scientific hypothesis. -/
@[instance_reducible] noncomputable def repairOrganizationStateFintype
    {X : Type uX} {A : Type uA} {Representation : Type uR}
    [Fintype X] [Fintype A] [Fintype Representation] :
    Fintype (RepairOrganizationState X A Representation) := by
  classical
  letI : Fintype (X → A) := inferInstance
  exact Fintype.ofEquiv
    (X × (X → A) × Representation)
    (repairOrganizationStateEquiv
      (X := X) (A := A) (Representation := Representation)).symm

end
end UEOT.V3.Compression.Objecthood.JointHomeostasis
