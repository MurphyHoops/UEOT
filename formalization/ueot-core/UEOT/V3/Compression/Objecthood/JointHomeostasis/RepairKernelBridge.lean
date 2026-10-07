import UEOT.V3.Compression.Objecthood.JointHomeostasis.FiniteJointState

/-!
# Theory Completion P5.0 — decode-preserving RLSR repair bridge

The strengthened RLSR runtime already reconstructs program organization before
selecting the physical action.  P5 records the exact theorem needed by the
homeostasis layer: whenever the mutable representation still decodes to one
intended program `r`, arbitrary stored-controller corruption is irrelevant and
one safe step is exactly the physical `r`-step mapped back to canonical
organization.
-/

namespace UEOT.V3.Compression.Objecthood.JointHomeostasis

open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

universe uX uA uP uR

noncomputable section

/-- Decode-preserving organizational damage is completely repaired before the
physical action is chosen.  The successor organization is canonical around the
same decoded program `r`. -/
theorem safeRepairKernel_eq_of_decode_eq
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X)
    (r : Program)
    (s : RepairOrganizationState X A Representation)
    (hdecode : codec.decode s.repairProgram = r) :
    safeRepairKernel T codec P s =
      (P s.physical (T.execute r s.physical)).map
        (canonicalRepairOrganizationState T codec r) := by
  simp only [safeRepairKernel, canonicalizeRepairOrganization, hdecode]
  apply congrArg
    (fun f : X → RepairOrganizationState X A Representation =>
      PMF.map f (P s.physical (T.execute r s.physical)))
  funext y
  rfl

end
end UEOT.V3.Compression.Objecthood.JointHomeostasis
